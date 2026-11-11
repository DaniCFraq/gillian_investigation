  



import argparse
import csv
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

"""
    Minimal analysis of simplifications on the Gillian-C AWS header example
    (Gillian-C/examples/amazon), restricted to a few procedures.

    profile   : run each procedure once with GILLIAN_REDUCE_COUNTS set (in-memory
                counter in Reduction.ml, no logging) and record which tags fire
                and how many times. Compares against the WISL results CSV.
    mandatory : for each procedure, disable one WISL-mandatory tag at a time
                (only tags that actually fired in that procedure, per the
                profile CSV) and check whether the verification outcome changes.
"""

ROOT = Path(__file__).resolve().parent
AMAZON_DIR = ROOT / "Gillian-C/examples/amazon"
REDUCTION_FILE = ROOT / "GillianCore/engine/FOLogic/Reduction.ml"
ORIGINAL_LINE = "let () = disable_reductions []"
C_FILES = ("header.c edk.c array_list.c ec.c byte_buf.c hash_table.c "
           "string.c allocator.c error.c base.c")
DEFAULT_PROCS = ["parse_edk", "aws_cryptosdk_enc_ctx_deserialize", "aws_cryptosdk_hdr_parse"]
COUNTS_FILE = ROOT / "reduce_counts.tsv"
TIME_RE = re.compile(r"(?:All specs succeeded|There were failures):\s*([\d.]+)")


def verify_cmd(proc: str) -> str:
    return (f"dune exec -- gillian-c verify {C_FILES} --fstruct-passing "
            f"--no-lemma-proof --proc {proc} -l disabled")


def run(cmd: str, timeout: int, env: dict | None = None) -> tuple[str, float, bool]:
    """Run cmd in AMAZON_DIR. Returns (stdout+stderr, wall time, timed_out).
    On timeout sends SIGTERM first (so the counter is dumped), then SIGKILL."""
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd, shell=True, cwd=AMAZON_DIR, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
    )
    timed_out = False
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            out, _ = proc.communicate(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            out, _ = proc.communicate()
    return out or "", time.monotonic() - start, timed_out


def outcome_signature(trace: str) -> tuple:
    """Same idea as setup.py: per-spec verdicts, reported failures, crash flag."""
    verdicts = sorted(
        (m.group(1), m.group(2))
        for m in re.finditer(r"^(Verifying .*?)\.\.\..*?(Success|Failure)\s*$", trace, re.MULTILINE)
    )
    failures = sorted(set(re.findall(r"^\s*\d+\.\s+(.*?)\s*$", trace, re.MULTILINE)))
    crashed = bool(re.search(r"Fatal error|[Bb]acktrace|exception", trace))
    return (tuple(verdicts), tuple(failures), crashed)


def collapse(tags: list[str]) -> list[str]:
    """Same collapsing as setup.process_simplifications (drop a parent tag when
    its next sorted tag is a direct child), so tags compare with the WISL CSV."""
    tags = sorted(set(tags))
    out = []
    for i, t in enumerate(tags):
        nxt = tags[i + 1] if i + 1 < len(tags) else None
        if nxt is None or t.count("_") + 1 != nxt.count("_"):
            out.append(t)
    return out


def load_wisl(csv_path: Path) -> tuple[set[str], set[str]]:
    """Returns (all tags seen in WISL, union of WISL-mandatory tags)."""
    split = lambda s: {t.strip() for t in (s or "").split(";") if t.strip()}
    seen, mandatory = set(), set()
    with open(csv_path, newline="") as f:
        for row in csv.DictReader(f):
            m = split(row["mandatory_simplifications_error"]) | split(row["mandatory_simplifications_timeout"])
            mandatory |= m
            seen |= m | split(row["optional_simplifications"])
    return seen, mandatory


def set_disabled(tags: list[str]):
    content = REDUCTION_FILE.read_text()
    line = ("let () = disable_reductions [ " + "; ".join(f'"{t}"' for t in tags) + " ]") if tags else ORIGINAL_LINE
    new = re.sub(r"let \(\) = disable_reductions \[.*?\]", line, content, count=1, flags=re.DOTALL)
    if new != content:
        REDUCTION_FILE.write_text(new)


def build():
    subprocess.run("dune build", shell=True, cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


# --------------------------------------------------------------------------- profile

def cmd_profile(args):
    set_disabled([])
    build()
    wisl_seen, wisl_mand = load_wisl(Path(args.wisl_csv))
    rows = []
    for proc in args.procs:
        print(f"\n=== {proc} ===")
        COUNTS_FILE.unlink(missing_ok=True)
        env = dict(os.environ, GILLIAN_REDUCE_COUNTS=str(COUNTS_FILE))
        out, wall, timed_out = run(verify_cmd(proc), args.timeout, env)
        sig = outcome_signature(out)
        m = TIME_RE.search(out)
        status = "timeout" if timed_out else ("ok" if m and "All specs succeeded" in out else "fail")
        print(f"  status={status}  wall={wall:.1f}s  engine_time={m.group(1) if m else '-'}  verdicts={sig[0]}")
        counts = {}
        if COUNTS_FILE.exists():
            for line in COUNTS_FILE.read_text().splitlines():
                tag, n = line.split("\t")
                counts[tag] = int(n)
        else:
            print("  WARNING: no counts file produced")
        for tag, n in counts.items():
            rows.append({"proc": proc, "tag": tag, "count": n, "status": status, "wall_s": f"{wall:.1f}"})

        fired = collapse(list(counts))
        total = sum(counts.values())
        print(f"  {len(counts)} distinct raw tags, {len(fired)} after collapsing, {total} firings in total")
        print("  top 15:", ", ".join(f"{t}:{n}" for t, n in sorted(counts.items(), key=lambda x: -x[1])[:15]))
        print(f"  fired in C but never seen in WISL: {sorted(set(fired) - wisl_seen)}")
        mand_fired = sorted(set(fired) & wisl_mand)
        print(f"  WISL-mandatory that fire here ({len(mand_fired)}/{len(wisl_mand)}): {mand_fired}")
        print(f"  WISL-mandatory that never fire here: {sorted(wisl_mand - set(fired))}")

    COUNTS_FILE.unlink(missing_ok=True)
    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["proc", "tag", "count", "status", "wall_s"])
        w.writeheader()
        w.writerows(sorted(rows, key=lambda r: (r["proc"], -r["count"])))
    print(f"\nProfile written to {args.out}")


# --------------------------------------------------------------------------- mandatory

def cmd_mandatory(args):
    _, wisl_mand = load_wisl(Path(args.wisl_csv))
    fired_by_proc: dict[str, list[str]] = {}
    with open(args.profile_csv, newline="") as f:
        for r in csv.DictReader(f):
            fired_by_proc.setdefault(r["proc"], []).append(r["tag"])

    out_path = Path(args.out)
    done = set()
    if out_path.exists():
        with open(out_path, newline="") as f:
            done = {(r["proc"], r["tag"]) for r in csv.DictReader(f)}
    new_file = not out_path.exists()

    try:
        with open(out_path, "a", newline="") as f:
            w = csv.DictWriter(f, fieldnames=["proc", "tag", "result", "wall_s"])
            if new_file:
                w.writeheader()
            for proc in args.procs:
                tags = sorted(set(collapse(fired_by_proc.get(proc, []))) & wisl_mand)
                print(f"\n=== {proc}: {len(tags)} WISL-mandatory tag(s) fire here ===")
                set_disabled([])
                build()
                base_out, base_wall, base_to = run(verify_cmd(proc), args.timeout)
                if base_to:
                    print("  baseline timed out; skipping procedure")
                    continue
                base_sig = outcome_signature(base_out)
                timeout = max(int(3 * base_wall), 120)
                print(f"  baseline {base_wall:.1f}s, verdicts={base_sig[0]}; per-tag timeout {timeout}s")
                for tag in tags:
                    if (proc, tag) in done:
                        continue
                    set_disabled([tag])
                    build()
                    out, wall, to = run(verify_cmd(proc), timeout)
                    result = "timeout" if to else ("same" if outcome_signature(out) == base_sig else "changed")
                    print(f"  disable {tag:>8}: {result} ({wall:.1f}s)")
                    w.writerow({"proc": proc, "tag": tag, "result": result, "wall_s": f"{wall:.1f}"})
                    f.flush()
    finally:
        set_disabled([])
        print("\nReduction file restored.")


def main():
    p = argparse.ArgumentParser(description="Simplification analysis on Gillian-C amazon procedures.")
    sub = p.add_subparsers(dest="cmd", required=True)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--procs", nargs="+", default=DEFAULT_PROCS)
    common.add_argument("--wisl-csv", default=str(ROOT / "file_simplification_results.csv"))
    common.add_argument("--timeout", type=int, default=1800, help="per-run timeout in seconds")

    sp = sub.add_parser("profile", parents=[common])
    sp.add_argument("--out", default=str(ROOT / "c_fire_profile.csv"))
    sp.set_defaults(func=cmd_profile)

    sm = sub.add_parser("mandatory", parents=[common])
    sm.add_argument("--profile-csv", default=str(ROOT / "c_fire_profile.csv"))
    sm.add_argument("--out", default=str(ROOT / "c_mandatory_results.csv"))
    sm.set_defaults(func=cmd_mandatory)

    args = p.parse_args()
    args.func(args)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        set_disabled([])
        print("\nInterrupted; reduction file restored.")
        sys.exit(1)
