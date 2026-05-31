import subprocess
import re
import sys

compile_cmd = "dune build"
command = "dune exec -- wisl verify wisl/examples/SLL_iterative.wisl > program_trace.txt"
file = "GillianCore/engine/FOLogic/Reduction.ml"
output = "program_trace.txt"
N = 30

line_to_replace = "let () = disable_reductions [ 158; 156; 149; 146; 142; 102; 100; 060; 057; 056; 054; 052; 051; 042; 031; 030; 027; 026; 013; 011; 010; 004; 003; 002; 001 ]"

numbers_str = "158; 156; 149; 146; 142; 102; 100; 060; 057; 056; 054; 052; 051; 042; 031; 030; 027; 026; 013; 011; 010; 004; 003; 002; 001"
list_numbers = [n.strip() for n in numbers_str.split(";")]


def change_code(new_list):
    global line_to_replace
    try:
        with open(file, "r") as f:
            content = f.read()
    except FileNotFoundError:
        print(f"Error: File {file} not found.")
        sys.exit(1)
    
    new_list_str = "; ".join(new_list)
    new_line = f"let () = disable_reductions [ {new_list_str} ]"

    new_content = content.replace(line_to_replace, new_line)
    with open(file, "w") as f:
        f.write(new_content)
    line_to_replace = new_line


def run_baseline():
    print(f"=== A calcular o tempo de referência ({N} iterações) ===")
    times = []

    try:
        subprocess.run(compile_cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        print("Compiling error no baseline.")
        sys.exit(1)

    for i in range(N):
        try:
            subprocess.run(command, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError:
            print(f"Error at iteration {i + 1}")
            continue

        try:
            with open(output, "r") as f:
                content = f.read()

            match = re.search(r"All specs succeeded:\s*([\d.]+)", content)
            
            if match:
                time = float(match.group(1))
                times.append(time)
            else:
                print(f"'All specs succeeded' not found at {i+1}")
                
        except FileNotFoundError:
            print(f"Error: File {output} not found")
            sys.exit(1)
            
        print(f"Baseline iteration {i+1}/{N} done...", end="\r")

    print("\n")
    if times:
        avg = sum(times) / len(times)
        max_t = max(times)
        min_t = min(times)

        print("--- Baseline Results ---")
        print(f"Average: {avg:.6f}")
        print(f"Maximum: {max_t:.6f}")
        print(f"Minimum: {min_t:.6f}")
        return avg
    else:
        print("Invalid times. Aborting.")
        sys.exit(1)


def run_config():
    try:
        subprocess.run(compile_cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        print(" Compiling error")
        return float('inf')

    times = []
    for _ in range(N):
        subprocess.run(command, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            with open(output, "r") as f:
                match = re.search(r"All specs succeeded:\s*([\d.]+)", f.read())
                if match:
                    times.append(float(match.group(1)))
        except FileNotFoundError:
            pass

    if times:
        return sum(times) / len(times)
    return float('inf')


def main():
    reference_time = run_baseline()
    
    print("\n=== A iniciar análise individual de simplificações ===")
    print(f"Target Reference time: {reference_time:.6f}s\n")

    positive_simplifications = []
    
    for number in list_numbers:
        if number in ["013"]:
            continue
            
        print(f"Testing number {number}...", end="", flush=True)

        new_list = [n for n in list_numbers if n != number]
        change_code(new_list)

        avg = run_config()
        print(f" Average: {avg:.6f}s")

        if avg > reference_time:
            positive_simplifications.append({
                "simplification": number,
                "average": avg
            })
            
    change_code(list_numbers)

    print("\n=== Resultados Finais ===")
    if not positive_simplifications:
        print(f"0 simplifications below {reference_time:.6f}s.")
    else:
        positive_simplifications.sort(key=lambda x: x["average"])
        for res in positive_simplifications:
            print(f"Simplificação {res['simplification']}: {res['average']:.6f}s")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        change_code(list_numbers)
        sys.exit(0)