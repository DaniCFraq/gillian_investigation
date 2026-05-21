import subprocess
import re
import sys

command = "dune exec -- wisl verify wisl/examples/SLL_iterative.wisl > simple_example_trace.txt"
output = "simple_example_trace.txt"
N = 500
times = []

for i in range(N):
    try:
        subprocess.run(command, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        print(f"Error at {i + 1}")
        continue

    try:
        with open(output, "r") as f:
            content = f.read()

        match = re.search(r"All specs succeeded:\s*([\d.]+)", content)
        
        if match:
            time = float(match.group(1))
            times.append(time)
            print(time)
        else:
            print(f"'All specs succeeded' not found at {i+1}")
            
    except FileNotFoundError:
        print(f"Error: File not found")
        sys.exit(1)
        
    # Mostra o progresso no terminal
    print(f"Iteration {i+1}/{N} done...", end="\r")
    print("\n")

if times:
    avg = sum(times) / len(times)
    max = max(times)
    min = min(times)

    print("Results")
    print(f"Average: {avg:.6f}")
    print(f"Maximum: {max:.6f}")
    print(f"Minimum: {min:.6f}")
else:
    print("Invalid times.")
