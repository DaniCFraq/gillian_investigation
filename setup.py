import subprocess
import re
import sys
import csv
import os
import signal
import argparse
from pathlib import Path

"""
    1º - Vai correr o programa e ler do ficheiro file.log todas as entradas que comecam por "[REDUCE_" e assim conseguir os numeros das simplificações que estão a ser usadas naquele programa, sem duplicados.
    2º - Ao processar as simplififcações, deixamos apenas aquelas que estão a ser realmente usadas, sem desativar a simplificação pai (do topo).
    3º - Verificar quais simplificações podem ser desativadas. Para isso, corremos primeiro o programa sem alterações e guardamos o resultado (baseline): veredicto de cada spec, falhas reportadas e se o motor crashou. Depois corremos o programa com uma simplificação desativada de cada vez: se o resultado for igual ao baseline, a simplificação é opcional; se mudar (erro diferente, crash, timeout, ou uma falha que desaparece), é obrigatória. Isto permite analisar também exemplos que falham de propósito (memory errors), cujo baseline já é uma falha.
    4º - Para cada ficheiro .wisl encontrado recursivamente na pasta indicada, guarda o caminho, as simplificações obrigatórias e as opcionais num ficheiro CSV.
    5º - Se o ficheiro .wisl já existir no CSV, é ignorado (skip).
"""

compile_cmd: str = "dune build"
line_to_replace: str = "let () = disable_reductions []"
reduction_file: str = "GillianCore/engine/FOLogic/Reduction.ml"
output: str = "program_trace.txt"

original_line: str = line_to_replace
RUN_TIMEOUT = 25


def _killpg(pgid: int):
    """Hard-kill an entire process group, ignoring it if it's already gone."""
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_command(cmd: str, timeout: int | None = None, check: bool = False) -> int:
    proc = subprocess.Popen(
        cmd, shell=True,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    pgid = proc.pid
    try:
        returncode = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        _killpg(pgid)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            pass
        raise
    _killpg(pgid)
    if check and returncode != 0:
        raise subprocess.CalledProcessError(returncode, cmd)
    return returncode


def make_run_cmd(wisl_path: str, with_logging: bool = True) -> str:
    log_flag = "" if with_logging else " -l disabled"
    return f"dune exec -- wisl verify {wisl_path}{log_flag} > {output}"

def clear_output_file():
    Path(output).write_text("")
    Path("file.log").write_text("")


def process_simplifications(reductions_array):
    processed_reductions = []

    for i, number in enumerate(reductions_array[:-1]):
        next_number = reductions_array[i + 1]
        if not (number.count("_") + 1 == next_number.count("_")):
            processed_reductions.append(number)
        if i + 1 == len(reductions_array) - 1:
            processed_reductions.append(reductions_array[i + 1])
    return processed_reductions


def restore_reduction_file():
    """Restore the reduction file to the original line unconditionally."""
    try:
        with open(reduction_file, "r") as f:
            content = f.read()
    except FileNotFoundError:
        print(f"Warning: File {reduction_file} not found when restoring original line.")
        return
    pattern = r"let \(\) = disable_reductions \[.*?\]"
    new_content = re.sub(pattern, original_line, content, count=1, flags=re.DOTALL)
    if new_content != content:
        with open(reduction_file, "w") as f:
            f.write(new_content)

    Path("file.log").write_text("")


def outcome_signature(trace: str) -> tuple:
    """
    Extract a stable outcome signature from a verify run's output:
    the verdict of each spec/lemma, the set of reported analysis
    failures, and whether the engine crashed. Timing values and
    branch progress marks ("s s f") are ignored, so two runs with
    the same final result compare equal even for examples whose
    expected result is a failure (e.g. memory error examples).
    """
    verdicts = sorted(
        (m.group(1), m.group(2))
        for m in re.finditer(
            r"^(Verifying .*?)\.\.\..*?(Success|Failure)\s*$", trace, re.MULTILINE
        )
    )
    failures = sorted(set(re.findall(r"^\s*\d+\.\s+(.*?)\s*$", trace, re.MULTILINE)))
    crashed = bool(re.search(r"Fatal error|[Bb]acktrace|exception", trace))
    return (tuple(verdicts), tuple(failures), crashed)


def test_reductions(simplifications, run_cmd, baseline_sig):
    """
    Test each simplification by disabling it one at a time and comparing
    the run's outcome against the baseline (unmodified) run.
    Returns three lists: optional simplifications (same outcome as
    baseline), mandatory simplifications whose outcome changed, and
    mandatory simplifications due to timeout.
    """
    can_disable = []
    mandatory_error = []
    mandatory_timeout = []

    for simplification in simplifications:
        if not re.fullmatch(r"\d[\d_]*", simplification):
            print(f"  Skipping invalid simplification tag: {simplification!r}")
            continue
        try:
            with open(reduction_file, "r") as f:
                content = f.read()
        except FileNotFoundError:
            print(f"Error: File {reduction_file} not found.")
            sys.exit(1)

        new_line = f'let () = disable_reductions [ "{simplification}" ]'
        patched = content.replace(original_line, new_line)
        with open(reduction_file, "w") as f:
            f.write(patched)

        skip = False
        try:
            clear_output_file()
            run_command(run_cmd, timeout=RUN_TIMEOUT)
        except subprocess.TimeoutExpired:
            print(f"  Timeout ({RUN_TIMEOUT}s) for simplification {simplification}; skipping.")
            mandatory_timeout.append(simplification)
            skip = True
        except Exception as e:
            print(f"  Unexpected error testing simplification {simplification}: {e}")
            mandatory_error.append(simplification)
            skip = True

        if not skip:
            try:
                with open(output, "r") as f:
                    trace = f.read()
                if outcome_signature(trace) == baseline_sig:
                    can_disable.append(simplification)
                else:
                    print(f"  Outcome changed for simplification {simplification}; mandatory.")
                    mandatory_error.append(simplification)
            except FileNotFoundError:
                print(f"Error: Output file {output} not found.")
                restore_reduction_file()
                sys.exit(1)
        restore_reduction_file()
        clear_output_file()

    return can_disable, mandatory_error, mandatory_timeout

def load_already_processed(csv_path: str) -> set[str]:
    """
    Reads the CSV and returns a set of file paths already present.
    Returns an empty set if the CSV does not exist yet.
    """
    processed = set()
    csv_file = Path(csv_path)
    if not csv_file.exists():
        return processed
    with open(csv_file, "r", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if "file" in row:
                processed.add(row["file"])
    return processed

def process_wisl_file(wisl_path: str) -> dict | None:
    """
    Run the full pipeline for a single .wisl file.
    Returns a dict with keys: file, mandatory, optional.
    Returns None if the file could not be run.
    """
    global line_to_replace
    line_to_replace = original_line

    run_cmd  = make_run_cmd(wisl_path, with_logging=True)
    test_cmd = make_run_cmd(wisl_path, with_logging=False)
    print(f"\n{'='*60}")
    print(f"Processing: {wisl_path}")
    print(f"{'='*60}")

    try:
        clear_output_file()
        run_command(run_cmd)
    except Exception as e:
        print(f"  Error running {wisl_path} ({e}); skipping.")
        return None

    try:
        with open(output, "r") as f:
            baseline_trace = f.read()
    except FileNotFoundError:
        print(f"  Output file {output} not found for {wisl_path}; skipping.")
        return None

    baseline_sig = outcome_signature(baseline_trace)
    verdicts, failures, crashed = baseline_sig
    if not verdicts:
        print(f"  No specs verified for {wisl_path} (parse/compile error?); skipping.")
        return None
    n_fail = sum(1 for _, v in verdicts if v == "Failure")
    in_errors_folder = any("errors" in part.lower() for part in Path(wisl_path).parts[:-1])
    if not in_errors_folder and (n_fail > 0 or crashed):
        reason = "crashed" if crashed else f"has {n_fail} failing spec(s)"
        print(f"  Baseline run {reason} and {wisl_path} is not in an 'errors' folder; skipping.")
        return None
    if n_fail == 0:
        print(f"  Baseline outcome: all {len(verdicts)} spec(s) succeeded.")
    else:
        print(f"  Baseline outcome: {n_fail}/{len(verdicts)} spec(s) failing (expected for error examples).")
        for failure in failures:
            print(f"    - {failure}")
    if crashed:
        print("  Warning: baseline run reports a crash/exception.")

    try:
        result = subprocess.run(
            "cat file.log", shell=True, check=True,
            capture_output=True, text=True
        )
        matches = re.findall(r'\[REDUCE_(\d[\d_]*)\]', result.stdout)
    except subprocess.CalledProcessError:
        print(f"  Error reading file.log for {wisl_path}; skipping.")
        return None

    if not matches:
        print(f"  No reductions found in log for {wisl_path}.")
        return {"file": wisl_path, "mandatory": [], "optional": []}

    reductions_array = sorted(set(matches))
    Path("file.log").write_text("")
    processed_reductions = process_simplifications(reductions_array)
    print(f"  All simplifications found:     {processed_reductions}")

    optional, mandatory_error, mandatory_timeout = test_reductions(processed_reductions, test_cmd, baseline_sig)

    print(f"  Mandatory simplifications (error): {mandatory_error}")
    print(f"  Mandatory simplifications (timeout): {mandatory_timeout}")
    print(f"  Optional  simplifications: {optional}")

    return {
        "file": wisl_path,
        "mandatory_error": mandatory_error,
        "mandatory_timeout": mandatory_timeout,
        "optional": optional,
    }

def append_to_csv(results: list[dict], csv_path: str):
    """
    Appends new results to the CSV file.
    Creates the file with a header if it does not exist yet.
    Never removes or rewrites existing entries.
    """
    csv_file = Path(csv_path)
    write_header = not csv_file.exists()

    with open(csv_file, "a", newline="") as f:
        writer = csv.writer(f)
        if write_header:
            writer.writerow([
                "file",
                "mandatory_simplifications_error",
                "mandatory_simplifications_timeout",
                "optional_simplifications",
            ])
        for row in results:
            writer.writerow([
                row["file"],
                "; ".join(row["mandatory_error"]),
                "; ".join(row["mandatory_timeout"]),
                "; ".join(row["optional"]),
            ])
    print(f"\nResults appended to: {csv_path}")

def main():
    parser = argparse.ArgumentParser(
        description="Run Gillian simplification analysis on all .wisl files in a folder."
    )
    parser.add_argument(
        "folder",
        help="Path to the folder containing .wisl files (searched recursively).",
    )
    parser.add_argument(
        "--output-csv",
        default="results.csv",
        help="Path for the output CSV file (default: results.csv).",
    )
    args = parser.parse_args()

    folder = Path(args.folder)
    if not folder.is_dir():
        print(f"Error: '{folder}' is not a valid directory.")
        sys.exit(1)

    wisl_files = sorted(folder.rglob("*.wisl"))
    if not wisl_files:
        print(f"No .wisl files found under '{folder}'.")
        sys.exit(0)

    print(f"Found {len(wisl_files)} .wisl file(s) under '{folder}'.")
    already_processed = load_already_processed(args.output_csv)
    if already_processed:
        print(f"Skipping {len(already_processed)} file(s) already in '{args.output_csv}'.")

    results = []
    try:
        for wisl_file in wisl_files:
            wisl_str = str(wisl_file)
            if wisl_str in already_processed:
                print(f"  [SKIP] {wisl_str} (already in CSV)")
                continue

            result = process_wisl_file(wisl_str)
            if result is not None:
                results.append(result)
    finally:
        print("\nRestoring reduction file...")
        restore_reduction_file()
        print("Reduction file restored.")

    if results:
        append_to_csv(results, args.output_csv)
    else:
        print("No new results to write.")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted by user.")
        sys.exit(0)