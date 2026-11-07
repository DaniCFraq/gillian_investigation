#!/usr/bin/env python3
"""Aggregate systematisation of Gillian's simplification tags.

Parses the per-tag tables of SIMPLIFICATIONS.md, classifies every tag along two
axes (theory of the trigger, nature of the rule), crosses the result with the
benchmark in file_simplification_results.csv, and prints the markdown section
that lives at the top of SIMPLIFICATIONS.md ("Aggregate systematisation").

    python3 simplification_taxonomy.py             # summary tables on stdout
    python3 simplification_taxonomy.py --tags      # one CSV line per tag
    python3 simplification_taxonomy.py --markdown  # the section as it appears
                                                   # at the top of the dictionary
"""

import collections
import csv
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
DICT = os.path.join(ROOT, "SIMPLIFICATIONS.md")
BENCH = os.path.join(ROOT, "file_simplification_results.csv")


def parse_dictionary():
    """One record per `check_reduction` tag documented in SIMPLIFICATIONS.md."""
    rows, section = [], None
    for line in open(DICT):
        header = re.match(r"^## `([^`]+)`", line)
        if header:
            section = header.group(1)
            continue
        if section is None or not line.startswith("| `"):
            continue  # skips the aggregate section's own tables
        # split on pipes that are not escaped: patterns contain `\|`
        cells = re.split(r"(?<!\\)\|", line.rstrip("\n"))
        if len(cells) < 5:
            continue
        tag = re.match(r"^`([0-9][0-9_a-z]*)`$", cells[1].strip())
        if tag:
            # a couple of rows carry an unescaped `|` inside a code span
            rows.append(dict(tag=tag.group(1), fn=section,
                             st=cells[2].strip(),
                             me="|".join(cells[3:-1]).strip()))
    return rows


def nature(row):
    """What the rule's correctness depends on — the provability axis."""
    trigger, meaning = row["st"].lower(), row["me"].lower()
    if any(k in meaning for k in
           ("raise", "failwith", "internal error", "⟶ error", "unreachable")):
        return "error"
    if any(k in meaning for k in ("dispatch", "parent of", "subtree")):
        return "dispatch"
    if any(k in meaning for k in
           ("recurse", "reduce each", "reduce under", "delegated",
            "⟶ normalise", "normalised", "reduce body", "⟶ default")):
        return "congruence"
    if any(k in meaning for k in
           ("unchanged", "kept as", "kept (", "fallthrough", "just the body",
            "refused", "⟶ none")):
        return "fallback"
    if ("pfs" in trigger or "gamma" in trigger or "matching" in trigger
            or "pfs" in meaning
            or any(k in meaning for k in
                   ("known list", "known string", "known number", "known int",
                    "known prefix", "entail", "substitute"))):
        return "context"
    if any(k in meaning for k in
           ("concretely evaluate", "literal", "computed", "compare them",
            "expand to")):
        return "computation"
    return "algebraic"


def theory(row):
    """Which theory the trigger's operator belongs to."""
    text = (row["st"] + " | " + row["me"]).lower()
    has = lambda *ks: any(re.search(k, text) for k in ks)
    if has(r"setunion", r"setinter", r"setdiff", r"setmem", r"setsub", r"eset",
           r"∈", r"⊆", r"∖", r"∪", r"∩", r"\bset\b"):
        return "sets"
    if has(r"strlen", r"tostringop", r"\bstring", r"strcat", r"strnth",
           r"strless"):
        return "strings"
    if has(r"lst", r"elist", r"llist", r"\blist", r"concat", r"\+\+", r"\bcar\b",
           r"\bcdr\b", r"\brev\b", r"\bnth\b", r"sublist", r"slice", r"len\("):
        return "lists"
    if has(r"typeof", r"isint", r"intonum", r"numtoint", r"\bcast",
           r"lit \(type", r"\btype\b"):
        return "types"
    if has(r"\bfloat", r"<f", r"<=f", r"fplus", r"fminus", r"ftimes", r"fdiv",
           r"cnum", r"funaryminus", r"\bnumber", r"\bnum\b"):
        return "floats"
    if has(r"\bint\b", r"\bints\b", r"integer", r"<i", r"<=i", r"iplus",
           r"iminus", r"itimes", r"idiv", r"imod", r"cint", r"divis"):
        return "integers"
    if has(r"\bnot\b", r"¬", r"∧", r"∨", r"\band\b", r"\bor\b", r"equal",
           r"\btrue\b", r"\bfalse\b", r"forall", r"exists", r"implic", r"⇒"):
        return "logic"
    return "generic"


# Hand-corrections, applied after the automatic pass (see the note in
# SIMPLIFICATIONS.md: the nature axis is hand-checked on the mandatory tags).
OVERRIDES = {"090_1": ("nature", "dispatch")}


def benchmark():
    """Per-tag: in how many example files it fires / is mandatory."""
    fires, mandatory, files = collections.Counter(), collections.Counter(), 0
    for row in csv.DictReader(open(BENCH)):
        files += 1
        m = set(t.strip() for t in (row["mandatory_simplifications_error"] + ";"
                                    + row["mandatory_simplifications_timeout"]
                                    ).split(";") if t.strip())
        o = set(t.strip() for t in row["optional_simplifications"].split(";")
                if t.strip())
        for t in m:
            mandatory[t] += 1
        for t in m | o:
            fires[t] += 1
    return files, fires, mandatory


FILE_OF = {
    "normalise_cat": "Reduction.ml",
    "normalise_list_expressions": "Reduction.ml",
    "prefix_catch": "Reduction.ml",
    "reduce_lexpr_loop": "Reduction.ml",
    "simplify_int_arithmetic_lexpr": "Reduction.ml",
    "simplify_num_arithmetic_lexpr": "Reduction.ml",
    "substitute_for_specific_length": "Reduction.ml",
    "simplify_pfs_and_gamma": "Simplifications.ml",
    "simplify_implication": "Simplifications.ml",
}

THEORY_NAME = {
    "lists": "Lists",
    "logic": "Propositional logic / equality",
    "integers": "Integer arithmetic",
    "floats": "Floating-point arithmetic",
    "sets": "Sets",
    "strings": "Strings",
    "types": "Types and casts",
    "generic": "Generic / structural",
}

NATURE_ROWS = [
    ("computation", "Concrete computation",
     "Every operand is a literal; the rule computes the result.",
     "**Yes** — falls out of the semantics."),
    ("algebraic", "Algebraic rewrite",
     "An identity of the theory applied to symbolic terms (`rev(rev l) = l`, "
     "`0 * x = 0`, `l[n]` over a concrete list). *Residual bucket: everything "
     "not matched by another row.*",
     "**Yes** — the natural proof target."),
    ("congruence", "Congruence (traversal)",
     "Rewrites nothing; recurses into the sub-terms.",
     "**Yes**, trivially (induction hypothesis)."),
    ("fallback", "Identity / fall-back",
     "No rule applies; the term is rebuilt as it was.",
     "**Yes**, trivially (identity)."),
    ("context", "Context-dependent",
     "Correctness depends on the PFS (path condition) or on `gamma` (typing "
     "environment), not on the term alone.",
     "**No**, not without modelling PFS/`gamma`."),
    ("dispatch", "Dispatch / guard",
     "Entry node into a sub-tree of rules; rewrites nothing on its own.",
     "N/A — not a rule."),
    ("error", "Error", "Raises an exception (ill-formed expression).",
     "Needs an exception semantics."),
]

# The arms modelled in verifications/cameleer/list_normaliser.ml.
MODELLED = ["401", "402", "404_1", "404_7", "405", "408_1", "408_3", "411"]

OMITTED = [
    ("409", "Congruence into a generic `UnOp` — the modelled language has no "
            "unary operator other than `LstLen`. Same rule shape as "
            "`405`/`411`, which are proved."),
    ("403", "Delegates to `normalise_cat`, whose proof needs "
            "append-associativity instantiated at specific arguments. A GOSPEL "
            "`lemma` has no proof body and cannot be applied to arguments, so "
            "this would require OCaml `[@lemma]` functions, which the model "
            "deliberately avoids."),
    ("413", "Congruence into `LstSub`, a constructor absent from the modelled "
            "language."),
    ("408_2", "`len(EList ++ tl)` — needs `LstCat`, same reason as `403`."),
]


def markdown(rows, files, fires, mandatory):
    """Emit the 'Aggregate systematisation' section of SIMPLIFICATIONS.md."""
    by_tag = {r["tag"]: r for r in rows}
    total = sum(mandatory.values())
    n_fires = sum(1 for t in fires if fires[t])
    n_mand = sum(1 for t in mandatory if mandatory[t])
    out = []
    p = out.append

    def stats(tags):
        return (len(tags),
                sum(1 for t in tags if fires[t]),
                sum(1 for t in tags if mandatory[t]),
                sum(mandatory[t] for t in tags))

    def grouped(axis):
        g = collections.defaultdict(list)
        for r in rows:
            g[r[axis]].append(r["tag"])
        return g

    p("## Aggregate systematisation\n")
    p("The per-function tables below give one row per tag. This section "
      "aggregates them along three axes and crosses them with the "
      f"{files}-example benchmark in `file_simplification_results.csv`. It is "
      "generated by `simplification_taxonomy.py`.\n")
    p("**Reading the columns.** *Tags* = distinct `check_reduction` sites. "
      "*Fires* = how many of them are logged in at least one of the "
      f"{files} examples. *Mandatory* = how many are mandatory in at least one "
      "example (disabling that tag alone changes the verification outcome). "
      f"*Occurrences* = the sum, over the {files} examples, of the mandatory "
      f"tags in each — the global total is **{total}**.\n")
    p(f"> Of the **{len(by_tag)}** distinct tags, only **{n_fires}** ever fire "
      f"in the benchmark and only **{n_mand}** are ever mandatory. The live "
      "surface of the simplifier is far smaller than the headline count "
      "suggests.\n")

    p("\n### Axis 1 — Location (originating function)\n")
    p("| Function | File | Tags | Fires | Mandatory | Occurrences |")
    p("|---|---|---:|---:|---:|---:|")
    g = grouped("fn")
    for k, ts in sorted(g.items(), key=lambda kv: -stats(kv[1])[3]):
        a = stats(ts)
        p(f"| `{k}` | {FILE_OF[k]} | {a[0]} | {a[1]} | {a[2]} | **{a[3]}** |")
    a = stats([r["tag"] for r in rows])
    p(f"| **Total** | | **{a[0]}** | **{a[1]}** | **{a[2]}** | **{a[3]}** |")
    nle = stats(g["normalise_list_expressions"])
    p(f"\n`normalise_list_expressions` holds {nle[0]} of the {a[0]} call-sites "
      f"({100 * nle[0] / a[0]:.0f} %) but accounts for {nle[3]} of the {total} "
      f"mandatory occurrences ({100 * nle[3] / total:.0f} %). It is the densest "
      "source of mandatory rules in the system.\n")

    p("\n### Axis 2 — Theory (operator at the trigger)\n")
    p("| Theory | Tags | % | Fires | Mandatory | Occurrences |")
    p("|---|---:|---:|---:|---:|---:|")
    for k, ts in sorted(grouped("theory").items(), key=lambda kv: -len(kv[1])):
        s = stats(ts)
        p(f"| {THEORY_NAME[k]} | {s[0]} | {100 * s[0] / a[0]:.0f} % | {s[1]} | "
          f"{s[2]} | {s[3]} |")
    p(f"| **Total** | **{a[0]}** | | **{a[1]}** | **{a[2]}** | **{a[3]}** |")

    p("\n### Axis 3 — Nature of the rule\n")
    p("This is the axis that decides *provability*: it says what each rule's "
      "correctness depends on.\n")
    p("| Nature | What it does | Tags | Mand. | Occ. | Provable in a "
      "self-contained denotational model? |")
    p("|---|---|---:|---:|---:|---|")
    g = grouped("nature")
    for key, name, desc, provable in NATURE_ROWS:
        s = stats(g[key])
        p(f"| {name} | {desc} | {s[0]} | {s[2]} | {s[3]} | {provable} |")
    p(f"| **Total** | | **{a[0]}** | **{a[2]}** | **{a[3]}** | |")
    p(f"\nAxis 3 is assigned automatically from each rule's trigger and effect, "
      "with *algebraic rewrite* as the residual bucket; for the "
      f"{n_mand} ever-mandatory tags it was checked by hand.\n")

    p(f"\n### The {n_mand} mandatory tags, by nature\n")
    p("Splitting rewrites from traversal arms matters for reading the "
      "*mandatory* column: for a traversal arm, \"mandatory\" means that "
      "switching it off **breaks the traversal**, not that the rewrite itself "
      "was essential.\n")
    buckets = [(("computation", "algebraic"), "Genuine rewrites"),
               (("congruence", "fallback", "dispatch"),
                "Traversal arms (congruence / fall-back / guard)"),
               (("context",), "Context-dependent (PFS / `gamma`)")]
    for kinds, title in buckets:
        sel = [(t, c) for t, c in sorted(mandatory.items(),
                                         key=lambda kv: -kv[1])
               if c and by_tag[t]["nature"] in kinds]
        p(f"\n**{title}** — {len(sel)} tags\n")
        p("| Tag | Mand. | Theory | Function | Rule |")
        p("|---|---:|---|---|---|")
        for t, c in sel:
            r = by_tag[t]
            rule = r["me"].replace("\\|", "|").replace("|", "\\|")
            p(f"| `{t}` | {c}/{files} | {THEORY_NAME[r['theory']]} | "
              f"`{r['fn']}` | {rule} |")

    p("\n### Coverage of the Cameleer proof\n")
    cov = sum(mandatory[t] for t in MODELLED)
    p("`verifications/cameleer/list_normaliser.ml` models **8 arms** of "
      f"`normalise_list_expressions` — `{'`, `'.join(MODELLED)}` — worth "
      f"**{cov}** of the {total} mandatory occurrences in the benchmark "
      f"(**{100 * cov / total:.0f} %**), out of {len(by_tag)} tags.\n")
    fired_nle = [r["tag"] for r in rows
                 if r["fn"] == "normalise_list_expressions" and fires[r["tag"]]]
    p(f"Of the {len(fired_nle)} tags of that function that ever fire, the "
      f"{len(OMITTED)} left out are:\n")
    p("| Tag | Mand. | Why it is out |")
    p("|---|---:|---|")
    for t, why in OMITTED:
        p(f"| `{t}` | {mandatory[t]}/{files} | {why} |")
    p("")
    p("---")
    return "\n".join(out) + "\n"


def main():
    rows = parse_dictionary()
    for r in rows:
        r["nature"], r["theory"] = nature(r), theory(r)
        if r["tag"] in OVERRIDES:
            field, value = OVERRIDES[r["tag"]]
            r[field] = value
    files, fires, mandatory = benchmark()

    if "--markdown" in sys.argv:
        sys.stdout.write(markdown(rows, files, fires, mandatory))
        return

    if "--tags" in sys.argv:
        w = csv.writer(sys.stdout)
        w.writerow(["tag", "function", "theory", "nature", "fires", "mandatory"])
        for r in rows:
            w.writerow([r["tag"], r["fn"], r["theory"], r["nature"],
                        fires[r["tag"]], mandatory[r["tag"]]])
        return

    total = sum(mandatory.values())
    print(f"# {len(rows)} call-sites, {len(set(r['tag'] for r in rows))} distinct tags, "
          f"{files} benchmark files")
    print(f"# {sum(1 for t in fires if fires[t])} ever fire, "
          f"{sum(1 for t in mandatory if mandatory[t])} ever mandatory, "
          f"{total} mandatory occurrences\n")
    for axis in ("fn", "theory", "nature"):
        groups = collections.defaultdict(list)
        for r in rows:
            groups[r[axis]].append(r["tag"])
        print(f"{axis:12s} {'tags':>5} {'fires':>6} {'mand':>5} {'occ':>5}")
        for k, ts in sorted(groups.items(),
                            key=lambda kv: -sum(mandatory[t] for t in kv[1])):
            print(f"{k[:12]:12s} {len(ts):5d} "
                  f"{sum(1 for t in ts if fires[t]):6d} "
                  f"{sum(1 for t in ts if mandatory[t]):5d} "
                  f"{sum(mandatory[t] for t in ts):5d}")
        print()


if __name__ == "__main__":
    main()
