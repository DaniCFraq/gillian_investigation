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

# Some notes

In verification_console.ml:87, verify only parses, preprocesses, and proves specs; the leak pass is not invoked there. The leak check is only wired into the symbolic-execution path in wpst_console.ml:32 and only runs when --leak-check is set.

dune exec -- wisl wpst wisl/examples/active_examples/memory_leak_error.wisl --leak-check -l disabled > program_trace.txt 2>&1

# TODO: Create an issue in Gillian GitHub repo

Title
wisl wpst --leak-check reports MemoryLeak even after free(x) on a freed block

Body
When running leak checking on a simple WISL program that allocates a block, writes to it, frees it, and returns, Gillian still reports a MemoryLeak error.

Repro
dune exec -- wisl wpst wisl/examples/active_examples/memory_leak_error.wisl --leak-check -l disabled

Example
{ emp }
function main() {
    x := new(3);
    [x] := 1;
    [x + 1] := 2;
    [x + 2] := 3;
    free(x);
    return null
}
{ (ret == null) * emp }

Observed behaviour
Memory Leak Check post-execution
Errors: MemoryLeak
MEMORY:
  #loc_0 -> FREED

Expected behavior
If the only allocated block has been freed, the leak check should succeed and not report MemoryLeak.

Changes:
/home/dani/Gillian/wisl/lib/state_frac/wislSHeap.ml --- is_empty function --- Freed -> true
/home/dani/Gillian/wisl/lib/state_ex/wislSHeap.ml --- is_empty function --- Freed -> true

# Another error from gillian?

Line 188 /home/dani/Gillian/wisl/lib/state_frac/wislSHeap.ml

An BufferOverflow error is outputing use after free.Change this to out of bounds.