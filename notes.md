## Simplifications in simple_example.js

# With flag enable_reductions = true

21
[REDUCE_001]
[REDUCE_089]
[REDUCE_004]
[REDUCE_110]
[REDUCE_110_a]
[REDUCE_028]
[REDUCE_133]
[REDUCE_028_01]
[REDUCE_034]
[REDUCE_005]
[REDUCE_034_b]
[REDUCE_140]
[REDUCE_140_c]
[REDUCE_092]
[REDUCE_092_f]
[REDUCE_040]
[REDUCE_088]
[REDUCE_088_a]
[REDUCE_028_06]
[REDUCE_028_06c]
[REDUCE_088_c]
[REDUCE_088_b]

# With flag enable_reductions = false (ERROR)


## Simplifications in tese_simple1.wisl

# With flag enable_reductions = true

24
[REDUCE_140]
[REDUCE_140]
[REDUCE_026]
[REDUCE_003]
[REDUCE_140_g]
[REDUCE_158]
[REDUCE_144]
[REDUCE_028]
[REDUCE_028_25]
[REDUCE_001]
[REDUCE_146]
[REDUCE_146_e]
[REDUCE_158_c]
[REDUCE_142]
[REDUCE_142_b]
[REDUCE_142_b9]
[REDUCE_142_b7]
[REDUCE_004]
[REDUCE_142_b6]
[REDUCE_142_b6d]
[REDUCE_142_b8]
[REDUCE_156]
[REDUCE_156_d]
[REDUCE_027]
[REDUCE_040]


## Running the program

# JS examples

dune exec -- gillian-js wpst "filename" > "out file"name 2>&1

# WISL examples

dune exec -- wisl verify "filename" > "out filename" 2>&1

# Getting reduction logs

if [[ -f file.log ]]; then grep '^\[REDUCE' file.log | awk '!seen[$0]++' > reduce_unique.log; echo "lines: $(wc -l < reduce_unique.log)"; else echo 'file.log not found'; fi

reduce_unique.log being the output file

# Getting what enters in the SMT

GILLIAN_TRACE_FORMULAS=true dune exec -- wisl verify "filename" > "out_filename" 2>&1

## Simplificações usadas no SLL_iterative.wisl
001, 002, 003, 004, 010, 011, 013, 023, 026, 027, 028, 030, 031, 033, 040, 042, 043, 048, 051, 052, 054, 056, 057, 060, 089, 100, 102, 110, 120, 140, 141, 142, 144, 146, 149, 150, 156, 158

necessárias: 023, 028, 033, 040, 043, 048, 089, 110, 120, 140, 141, 144, 150


# Notas: 
* quando tiramos a 011, o programa fica mais rápido.
* 013 está interligada com a 011, ou seja, não podemos ativar 013 e deixar 011 desativada. 013 ativa implica 011 ativa


# Times for 100 repetitions: