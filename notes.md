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


# Times for 30 repetitions:

=== A calcular o tempo de referência (30 iterações) ===
Baseline iteration 30/30 done...

--- Baseline Results ---
Average: 1.316153
Maximum: 1.343736
Minimum: 1.297469

=== A iniciar análise individual de simplificações ===
Target Reference time: 1.316153s

Testing number 158... Average: 1.318471s
Testing number 156... Average: 1.314772s
Testing number 149... Average: 1.313961s
Testing number 146... Average: 1.312234s
Testing number 142... Average: 1.088089s ---
Testing number 102... Average: 1.311935s
Testing number 100... Average: 1.307116s
Testing number 060... Average: 1.304550s
Testing number 057... Average: 1.312809s
Testing number 056... Average: 1.314404s
Testing number 054... Average: 1.307610s
Testing number 052... Average: 1.316945s
Testing number 051... Average: 1.315642s
Testing number 042... Average: 1.310241s
Testing number 031... Average: 1.316292s
Testing number 030... Average: 1.319531s
Testing number 027... Average: 1.313219s
Testing number 026... Average: 1.320583s
Testing number 011... Average: 1.227518s ----
Testing number 010... Average: 1.313698s
Testing number 004... Average: 1.373517s
Testing number 003... Average: 1.314808s
Testing number 002... Average: 1.323982s
Testing number 001... Average: 1.314998s

=== Resultados Finais ===
Simplificação 031: 1.316292s
Simplificação 052: 1.316945s
Simplificação 158: 1.318471s
Simplificação 030: 1.319531s
Simplificação 026: 1.320583s
Simplificação 002: 1.323982s
Simplificação 004: 1.373517s  ----