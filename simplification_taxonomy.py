#!/usr/bin/env python3
"""Aggregate systematisation of Gillian's simplification tags.

Reads the per-tag tables of SIMPLIFICATIONS.md, classifies every tag by theory
and by nature, crosses that with file_simplification_results.csv (written by
setup.py), and produces the "Aggregate systematisation" section of
SIMPLIFICATIONS.md.

    python3 simplification_taxonomy.py          # print the section
    python3 simplification_taxonomy.py --write  # replace it in SIMPLIFICATIONS.md
    python3 simplification_taxonomy.py --tags   # one CSV line per tag
"""

import collections
import csv
import os
import re
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
DICT = os.path.join(ROOT, "SIMPLIFICATIONS.md")
BENCH = os.path.join(ROOT, "file_simplification_results.csv")
SECTION = "## Aggregate systematisation"

# ---------------------------------------------------------------- classifiers
# Both axes are first-match-wins keyword tables over the dictionary's own
# "Structure" (trigger) and "Meaning" columns.

# (nature, keywords looked for in the meaning); no match = "algebraic".
NATURE_KEYWORDS = [
    ("error", ("raise", "failwith", "internal error", "⟶ error", "unreachable")),
    ("dispatch", ("dispatch", "parent of", "subtree")),
    ("congruence", ("recurse", "reduce each", "reduce under", "delegated",
                    "⟶ normalise", "normalised", "reduce body", "⟶ default")),
    ("fallback", ("unchanged", "kept as", "kept (", "fallthrough",
                  "just the body", "refused", "⟶ none")),
    ("context", ("pfs", "known list", "known string", "known number",
                 "known int", "known prefix", "entail", "substitute")),
    ("computation", ("concretely evaluate", "literal", "computed",
                     "compare them", "expand to")),
]
CONTEXT_TRIGGERS = ("pfs", "gamma", "matching")

# (theory, display name, regex over trigger + meaning); no match = "generic".
THEORIES = [
    ("sets", "Sets",
     r"setunion|setinter|setdiff|setmem|setsub|eset|∈|⊆|∖|∪|∩|\bset\b"),
    ("strings", "Strings", r"strlen|tostringop|\bstring|strcat|strnth|strless"),
    ("lists", "Lists",
     r"lst|elist|llist|\blist|concat|\+\+|\bcar\b|\bcdr\b|\brev\b|\bnth\b"
     r"|sublist|slice|len\("),
    ("types", "Types and casts",
     r"typeof|isint|intonum|numtoint|\bcast|lit \(type|\btype\b"),
    ("floats", "Floating-point arithmetic",
     r"\bfloat|<f|<=f|fplus|fminus|ftimes|fdiv|cnum|funaryminus|\bnumber"
     r"|\bnum\b"),
    ("integers", "Integer arithmetic",
     r"\bint\b|\bints\b|integer|<i|<=i|iplus|iminus|itimes|idiv|imod|cint"
     r"|divis"),
    ("logic", "Propositional logic / equality",
     r"\bnot\b|¬|∧|∨|\band\b|\bor\b|equal|\btrue\b|\bfalse\b|forall|exists"
     r"|implic|⇒"),
    ("generic", "Generic / structural", r""),
]
THEORY_NAME = {key: name for key, name, _ in THEORIES}

# Hand-corrections where the keywords pick the wrong bucket.
OVERRIDES = {
    "090_1": {"nature": "dispatch", "theory": "lists"},  # `l[n]`, n literal
    "203_3": {"theory": "integers"},   # integer monomial product
    "312_3": {"theory": "floats"},     # float unary minus fall-back
    "105_16_3": {"theory": "logic"},   # conjunction fall-through
    "105_17_3": {"theory": "logic"},   # disjunction fall-through
}

# Display order of the nature table: (key, name, what it does, provable?).
NATURES = [
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

# The three groups of the "mandatory tags, by nature" listing.
MANDATORY_GROUPS = [
    ("Genuine rewrites", ("computation", "algebraic")),
    ("Traversal arms (congruence / fall-back / guard)",
     ("congruence", "fallback", "dispatch")),
    ("Context-dependent (PFS / `gamma`)", ("context",)),
]

SIMPLIFICATIONS_ML = {"simplify_pfs_and_gamma", "simplify_implication"}

# Cameleer proof (verifications/cameleer/list_normaliser.ml): arms modelled,
# and why the other firing arms of normalise_list_expressions are left out.
MODELLED = ["401", "402", "404_1", "404_7", "405", "408_1", "408_3", "409",
            "411"]
OMITTED = [
    ("403", "Delegates to `normalise_cat`, whose proof needs "
            "append-associativity instantiated at specific arguments. A GOSPEL "
            "`lemma` has no proof body and cannot be applied to arguments, so "
            "this would require OCaml `[@lemma]` functions, which the model "
            "deliberately avoids."),
    ("413", "Congruence into `LstSub`, a constructor absent from the modelled "
            "language."),
    ("408_2", "`len(EList ++ tl)` — needs `LstCat`, same reason as `403`."),
]


def nature(trigger, meaning):
    for name, keywords in NATURE_KEYWORDS:
        if any(k in meaning for k in keywords) or (
                name == "context" and any(k in trigger for k in CONTEXT_TRIGGERS)):
            return name
    return "algebraic"


def theory(trigger, meaning):
    text = trigger + " | " + meaning
    return next(key for key, _, pattern in THEORIES if re.search(pattern, text))


# --------------------------------------------------------------------- inputs

def read_dictionary():
    """One classified record per tag row of the per-function tables."""
    rows, fn = [], None
    for line in open(DICT):
        header = re.match(r"^## `([^`]+)`", line)
        if header:
            fn = header.group(1)
        if fn is None or not line.startswith("| `"):
            continue  # also skips the aggregate section's own tables
        # split on unescaped pipes only: the patterns contain `\|`
        cells = re.split(r"(?<!\\)\|", line.rstrip("\n"))
        tag = re.fullmatch(r"`([0-9][0-9_a-z]*)`", cells[1].strip())
        if not tag or len(cells) < 5:
            continue
        # a few meanings carry an unescaped `|` inside a code span
        trigger, meaning = cells[2].strip(), "|".join(cells[3:-1]).strip()
        row = dict(tag=tag.group(1), fn=fn, meaning=meaning,
                   nature=nature(trigger.lower(), meaning.lower()),
                   theory=theory(trigger.lower(), meaning.lower()))
        row.update(OVERRIDES.get(row["tag"], {}))
        rows.append(row)
    return rows


def read_benchmark():
    """Number of example files, and per tag in how many it fires / is mandatory."""
    split = lambda cell: {t.strip() for t in cell.split(";") if t.strip()}
    fires, mandatory, files = collections.Counter(), collections.Counter(), 0
    for row in csv.DictReader(open(BENCH)):
        files += 1
        must = (split(row["mandatory_simplifications_error"])
                | split(row["mandatory_simplifications_timeout"]))
        mandatory.update(must)
        fires.update(must | split(row["optional_simplifications"]))
    return files, fires, mandatory


# --------------------------------------------------------------------- output

def table(header, align, lines):
    return ["| " + " | ".join(header) + " |", "|" + "|".join(align) + "|",
            *("| " + " | ".join(str(c) for c in line) + " |" for line in lines)]


def section(rows, files, fires, mandatory):
    """The 'Aggregate systematisation' section, as markdown."""
    by_tag = {r["tag"]: r for r in rows}
    n_fires, n_mand, total = len(fires), len(mandatory), sum(mandatory.values())

    def stats(tags):  # (tags, fires, mandatory, occurrences)
        return (len(tags), sum(1 for t in tags if fires[t]),
                sum(1 for t in tags if mandatory[t]),
                sum(mandatory[t] for t in tags))

    def group(axis):
        groups = collections.defaultdict(list)
        for r in rows:
            groups[r[axis]].append(r["tag"])
        return groups

    bold = lambda xs: [f"**{x}**" for x in xs]
    n, f, m, o = stats([r["tag"] for r in rows])
    R, C = "---:", "---"
    out = [f"""{SECTION}

The per-function tables below give one row per tag. This section aggregates \
them along three axes and crosses them with the {files}-example benchmark in \
`file_simplification_results.csv`. It is generated by \
`simplification_taxonomy.py`.

**Reading the columns.** *Tags* = distinct `check_reduction` sites. *Fires* = \
how many of them are logged in at least one of the {files} examples, not \
counting a parent (dispatch) tag when one of its sub-tags fired in the same \
example — `setup.py` only tests the innermost tags. *Mandatory* = how many are \
mandatory in at least one example (disabling that tag alone changes the \
verification outcome). *Occurrences* = the sum, over the {files} examples, of \
the mandatory tags in each — the global total is **{total}**.

> Of the **{len(by_tag)}** distinct tags, only **{n_fires}** ever fire in the \
benchmark and only **{n_mand}** are ever mandatory. The live surface of the \
simplifier is far smaller than the headline count suggests.


### Axis 1 — Location (originating function)
"""]
    fns = group("fn")
    out += table(
        ["Function", "File", "Tags", "Fires", "Mandatory", "Occurrences"],
        [C, C, R, R, R, R],
        [(f"`{fn}`",
          "Simplifications.ml" if fn in SIMPLIFICATIONS_ML else "Reduction.ml",
          *s[:3], f"**{s[3]}**")
         for fn, s in sorted(((fn, stats(ts)) for fn, ts in fns.items()),
                             key=lambda kv: -kv[1][3])]
        + [("**Total**", "", *bold((n, f, m, o)))])
    nle = stats(fns["normalise_list_expressions"])
    out.append(f"""
`normalise_list_expressions` holds {nle[0]} of the {n} call-sites \
({100 * nle[0] / n:.0f} %) but accounts for {nle[3]} of the {total} mandatory \
occurrences ({100 * nle[3] / total:.0f} %). It is the densest source of \
mandatory rules in the system.


### Axis 2 — Theory (operator at the trigger)
""")
    out += table(
        ["Theory", "Tags", "%", "Fires", "Mandatory", "Occurrences"],
        [C, R, R, R, R, R],
        [(THEORY_NAME[k], s[0], f"{100 * s[0] / n:.0f} %", *s[1:])
         for k, s in sorted(((k, stats(ts)) for k, ts in group("theory").items()),
                            key=lambda kv: -kv[1][0])]
        + [("**Total**", f"**{n}**", "", *bold((f, m, o)))])
    out.append("""
### Axis 3 — Nature of the rule

This is the axis that decides *provability*: it says what each rule's \
correctness depends on.
""")
    natures = group("nature")
    out += table(
        ["Nature", "What it does", "Tags", "Mand.", "Occ.",
         "Provable in a self-contained denotational model?"],
        [C, C, R, R, R, C],
        [(name, desc, s[0], s[2], s[3], provable)
         for key, name, desc, provable in NATURES
         for s in [stats(natures[key])]]
        + [("**Total**", "", *bold((n, m, o)), "")])
    out.append(f"""
Axis 3 is assigned automatically from each rule's trigger and effect, with \
*algebraic rewrite* as the residual bucket; for the {n_mand} ever-mandatory \
tags it was checked by hand.


### The {n_mand} mandatory tags, by nature

Splitting rewrites from traversal arms matters for reading the *mandatory* \
column: for a traversal arm, "mandatory" means that switching it off **breaks \
the traversal**, not that the rewrite itself was essential.
""")
    ranked = sorted(mandatory, key=lambda t: (-mandatory[t], t))
    for title, kinds in MANDATORY_GROUPS:
        tags = [t for t in ranked if by_tag[t]["nature"] in kinds]
        out.append(f"\n**{title}** — {len(tags)} tags\n")
        out += table(
            ["Tag", "Mand.", "Theory", "Function", "Rule"], [C, R, C, C, C],
            [(f"`{t}`", f"{mandatory[t]}/{files}",
              THEORY_NAME[by_tag[t]["theory"]], f"`{by_tag[t]['fn']}`",
              by_tag[t]["meaning"].replace("\\|", "|").replace("|", "\\|"))
             for t in tags])

    covered = sum(mandatory[t] for t in MODELLED)
    fired_nle = [t for t in fns["normalise_list_expressions"] if fires[t]]
    out.append(f"""
### Coverage of the Cameleer proof

`verifications/cameleer/list_normaliser.ml` models **{len(MODELLED)} arms** of \
`normalise_list_expressions` — `{'`, `'.join(MODELLED)}` — worth **{covered}** \
of the {total} mandatory occurrences in the benchmark \
(**{100 * covered / total:.0f} %**), out of {len(by_tag)} tags.

Of the {len(fired_nle)} tags of that function that ever fire, the \
{len(OMITTED)} left out are:
""")
    out += table(["Tag", "Mand.", "Why it is out"], [C, R, C],
                 [(f"`{t}`", f"{mandatory[t]}/{files}", why)
                  for t, why in OMITTED])
    return "\n".join(out) + "\n\n---\n"


def main():
    rows = read_dictionary()
    files, fires, mandatory = read_benchmark()

    if "--tags" in sys.argv:
        out = csv.writer(sys.stdout)
        out.writerow(["tag", "function", "theory", "nature", "fires", "mandatory"])
        for r in rows:
            out.writerow([r["tag"], r["fn"], r["theory"], r["nature"],
                          fires[r["tag"]], mandatory[r["tag"]]])
        return

    text = section(rows, files, fires, mandatory)
    if "--write" in sys.argv:
        doc = open(DICT).read()
        start = doc.index(SECTION)
        end = doc.index("\n---\n", start) + len("\n---\n")
        open(DICT, "w").write(doc[:start] + text + doc[end:])
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
