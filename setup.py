import subprocess
import re
import sys

"""
    1º - Vai correr o programa e ler do ficheiro file.log todas as entradas que comecam por "[REDUCE_" e assim conseguir os numeros das simplificações que estão a ser usadas naquele programa, sem duplicados.
    2º - Ao processar as simplififcações, deixamos apenas aquelas que estão a ser realmente usadas, sem desativar a simplificação pai (do topo).
    3º - Verificar quais simplificações podem ser desativadas. Para isso, vamos correr o programa com uma simplificação desativada de cada vez. Se essa simplificação der erro, continuamos, se não der erro, adicionamos ao array de simplificações que podem ser desativadas. 
"""

compile_cmd = "dune build"
run_program = "dune exec -- wisl verify wisl/examples/SLL_iterative.wisl"

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


    print(processed_reductions)
    return processed_reductions


def main():
    try:
        subprocess.run(compile_cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        print("Compiling error no baseline.")
        sys.exit(1)

    try:
        subprocess.run(run_program, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            result = subprocess.run("cat file.log", shell=True, check=True, capture_output=True, text=True)
            matches = re.findall(r'\[REDUCE_([^\]]+)\]', result.stdout)
            reductions_array = list(set(matches))  # Remove duplicates
            reductions_array.sort()
            process_simplifications(reductions_array)

            # for x in a1:
            #     process_simplifications(x)
        except subprocess.CalledProcessError:
            print("Error extracting reductions")

    except subprocess.CalledProcessError:
        print("Error running")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)

