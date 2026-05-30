import subprocess
import re
import sys

"""
    1º - Vai correr o programa e ler do ficheiro file.log todas as entradas que comecam por "[REDUCE_" e assim conseguir os numeros das simplificações que estão a ser usadas naquele programa, sem duplicados.
    2º - Ao processar as simplififcações, deixamos apenas aquelas que estão a ser realmente usadas, sem desativar a simplificação pai (do topo).
    3º - Verificar quais simplificações podem ser desativadas. Para isso, vamos correr o programa com uma simplificação desativada de cada vez. Se essa simplificação der erro, continuamos, se não der erro, adicionamos ao array de simplificações que podem ser desativadas. 
"""

compile_cmd = "dune build"
run_program = "dune exec -- wisl verify wisl/examples/SLL_iterative.wisl > simple_example_trace.txt"
line_to_replace = "let () = disable_reductions []"
file = "GillianCore/engine/FOLogic/Reduction.ml"
output = "simple_example_trace.txt"

# keep the original line so we can restore it on exit
original_line = line_to_replace
# timeout (seconds) for each run to avoid infinite loops
RUN_TIMEOUT = 10
# a1 = [["1", "2", "3"],
#     ["1", "2", "2_1", "2_2"],
#     ["1", "2", "2_1", "2_1_1", "2_1_2", "3"],
#     ["1", "1_1", "1_1_1"],
#     ["1", "2", "2_1", "2_1_1", "2_2"]]


def process_simplifications(reductions_array):
    
    processed_reductions = []

    for i, number in enumerate(reductions_array[:-1]):
        next_number = reductions_array[i + 1]
        if not (number.count("_") + 1 == next_number.count("_")):      
            processed_reductions.append(number)
        if i + 1 == len(reductions_array) - 1:
            processed_reductions.append(reductions_array[i+1])
    return processed_reductions

def test_reductions(simplifications):
    global line_to_replace
    can_disable = []
    for simplification in simplifications:
        try:
            with open(file, "r") as f:
                    content = f.read()
        except FileNotFoundError:
            print(f"Error: File {file} not found.")
            sys.exit(1)
        new_line = f"let () = disable_reductions [ {simplification} ]"
        new_content = content.replace(line_to_replace, new_line)
        with open(file, "w") as f:
            f.write(new_content)
        line_to_replace = new_line

        try:
            subprocess.run(compile_cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError:
            print("Compiling error no baseline.")
            sys.exit(1)
        try:
            try:
                subprocess.run(run_program, shell=True, check=True, timeout=RUN_TIMEOUT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except subprocess.TimeoutExpired:
                print(f"Timeout ({RUN_TIMEOUT}s) reached for simplification {simplification}; skipping.")
                # continue to next simplification
                continue
            except subprocess.CalledProcessError:
                print(f"Error running simplification {simplification}")
                continue

            try:
                with open(output, "r") as f:
                    content = f.read()
                if not any(k in content.lower() for k in ("failure", "failures", "error", "backtrace")):
                    can_disable.append(simplification)

            except FileNotFoundError:
                print(f"Error: File {output} not found")
                sys.exit(1)
        except Exception as e:
            # Catch-all to ensure we don't stop the whole loop on unexpected errors
            print(f"Unexpected error testing simplification {simplification}: {e}")
            continue

    print(can_disable)
    return can_disable

def main():
    try:
        subprocess.run(compile_cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        print("Compiling error no baseline.")
        sys.exit(1)

    try:
        try:
            subprocess.run(run_program, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                result = subprocess.run("cat file.log", shell=True, check=True, capture_output=True, text=True)
                matches = re.findall(r'\[REDUCE_([^\]]+)\]', result.stdout)
                reductions_array = list(set(matches))  # Remove duplicates
                reductions_array.sort()
                processed_reductions = process_simplifications(reductions_array)
                final_reductions_array = test_reductions(processed_reductions)

            except subprocess.CalledProcessError:
                print("Error extracting reductions")
        except subprocess.CalledProcessError:
            print("Error running")
    finally:
        try:
            import re as _re
            with open(file, "r") as f:
                _content = f.read()
        except FileNotFoundError:
            print(f"Warning: File {file} not found when restoring original line.")
        else:
            _pattern = r"let \(\) = disable_reductions \[.*?\]"
            _new = _re.sub(_pattern, original_line, _content, count=1)
            if _new != _content:
                with open(file, "w") as f:
                    f.write(_new)
                line_to_replace = original_line

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)

