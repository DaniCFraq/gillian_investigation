import subprocess
import re
import sys
import csv
import argparse
from pathlib import Path

"""
    1º - Vai correr o programa e ler do ficheiro file.log todas as entradas que comecam por "[REDUCE_" e assim conseguir os numeros das simplificações que estão a ser usadas naquele programa, sem duplicados.
    2º - Ao processar as simplififcações, deixamos apenas aquelas que estão a ser realmente usadas, sem desativar a simplificação pai (do topo).
    3º - Verificar quais simplificações podem ser desativadas. Para isso, vamos correr o programa com uma simplificação desativada de cada vez. Se essa simplificação der erro, continuamos, se não der erro, adicionamos ao array de simplificações que podem ser desativadas.
    4º - Para cada ficheiro .wisl encontrado recursivamente na pasta indicada, guarda o caminho, as simplificações obrigatórias e as opcionais num ficheiro CSV.
"""

compile_cmd: str = "dune build"
line_to_replace: str = "let () = disable_reductions []"
reduction_file: str = "GillianCore/engine/FOLogic/Reduction.ml"
output: str = "program_trace.txt"

original_line: str = line_to_replace
RUN_TIMEOUT = 25


def clear_output_file():
    Path(output).write_text("")


def make_run_cmd(wisl_path: str) -> str:
    
    return f"dune exec -- wisl verify {wisl_path} -l disabled > {output}"


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
    new_content = re.sub(pattern, original_line, content, count=1)
    if new_content != content:
        with open(reduction_file, "w") as f:
            f.write(new_content)


def test_reductions(simplifications, run_cmd):
    """
    Test each simplification by disabling it one at a time.
    Returns the list of simplifications that can safely be disabled.
    """
    can_disable = []

    for simplification in simplifications:
        # 1. Patch: replace original_line with the disabled-simplification line.
        #    The file on disk must always contain original_line at this point
        #    (guaranteed by the restore step at the end of each iteration).
        try:
            with open(reduction_file, "r") as f:
                content = f.read()
        except FileNotFoundError:
            print(f"Error: File {reduction_file} not found.")
            sys.exit(1)

        new_line = f"let () = disable_reductions [ {simplification} ]"
        patched = content.replace(original_line, new_line)
        with open(reduction_file, "w") as f:
            f.write(patched)

        # 2. Recompile with the patch applied.
        # try:
        #     subprocess.run(
        #         compile_cmd, shell=True, check=True,
        #         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        #     )
        # except subprocess.CalledProcessError:
        #     print(f"Compile error while testing simplification {simplification}; aborting.")
        #     restore_reduction_file()
        #     sys.exit(1)

        # 3. Run the .wisl file and check the output.
        skip = False
        try:
            clear_output_file()
            subprocess.run(
                run_cmd, shell=True, check=True,
                timeout=RUN_TIMEOUT,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
            )
        except subprocess.TimeoutExpired:
            print(f"  Timeout ({RUN_TIMEOUT}s) for simplification {simplification}; skipping.")
            skip = True
        except subprocess.CalledProcessError:
            print(f"  Run error for simplification {simplification}; skipping.")
            skip = True
        except Exception as e:
            print(f"  Unexpected error testing simplification {simplification}: {e}")
            skip = True

        if not skip:
            try:
                with open(output, "r") as f:
                    trace = f.read()
                if not any(k in trace.lower() for k in ("failure", "failures", "error", "backtrace")):
                    can_disable.append(simplification)
            except FileNotFoundError:
                print(f"Error: Output file {output} not found.")
                restore_reduction_file()
                sys.exit(1)

        # 4. Restore original_line so the next iteration always starts from a clean file.
        restore_reduction_file()

    return can_disable


def process_wisl_file(wisl_path: str) -> dict | None:
    """
    Run the full pipeline for a single .wisl file.
    Returns a dict with keys: file, mandatory, optional.
    Returns None if the file could not be run.
    """
    global line_to_replace
    line_to_replace = original_line  # reset for each file

    run_cmd = make_run_cmd(wisl_path)
    print(f"\n{'='*60}")
    print(f"Processing: {wisl_path}")
    print(f"{'='*60}")

    # Run the .wisl file and read the log
    try:
        clear_output_file()
        subprocess.run(
            run_cmd, shell=True, check=True,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )
    except subprocess.CalledProcessError:
        print(f"  Error running {wisl_path}; skipping.")
        return None

    try:
        result = subprocess.run(
            "cat file.log", shell=True, check=True,
            capture_output=True, text=True
        )
        matches = re.findall(r'\[REDUCE_([^\]]+)\]', result.stdout)
    except subprocess.CalledProcessError:
        print(f"  Error reading file.log for {wisl_path}; skipping.")
        return None

    if not matches:
        print(f"  No reductions found in log for {wisl_path}.")
        return {"file": wisl_path, "mandatory": [], "optional": []}

    reductions_array = sorted(set(matches))
    processed_reductions = process_simplifications(reductions_array)
    print(f"  All simplifications found:     {processed_reductions}")

    # Test which ones are optional (can be disabled without breaking the run)
    optional = test_reductions(processed_reductions, run_cmd)
    mandatory = [r for r in processed_reductions if r not in optional]

    print(f"  Mandatory simplifications: {mandatory}")
    print(f"  Optional  simplifications: {optional}")

    return {"file": wisl_path, "mandatory": mandatory, "optional": optional}


def write_csv(results: list[dict], csv_path: str):
    """Write results to a CSV file."""
    with open(csv_path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["file", "mandatory_simplifications", "optional_simplifications"])
        for row in results:
            writer.writerow([
                row["file"],
                "; ".join(row["mandatory"]),
                "; ".join(row["optional"]),
            ])
    print(f"\nResults saved to: {csv_path}")


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

    # Collect all .wisl files recursively, sorted for determinism
    wisl_files = sorted(folder.rglob("*.wisl"))
    if not wisl_files:
        print(f"No .wisl files found under '{folder}'.")
        sys.exit(0)

    print(f"Found {len(wisl_files)} .wisl file(s) under '{folder}'.")

    results = []
    try:
        for wisl_file in wisl_files:
            result = process_wisl_file(str(wisl_file))
            if result is not None:
                results.append(result)
    finally:
        # Always restore the reduction file, even on Ctrl-C or crash
        print("\nRestoring reduction file...")
        restore_reduction_file()
        print("Reduction file restored.")

    if results:
        write_csv(results, args.output_csv)
    else:
        print("No results to write.")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted by user.")
        sys.exit(0)