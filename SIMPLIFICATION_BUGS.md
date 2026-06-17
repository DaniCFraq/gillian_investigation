# Simplification Correctness Audit


## 1. CONFIRMED BUG — tags `059` & `060`: byte decomposition uses `n − b1` instead of `n mod 256`

**Location:** `Reduction.ml:1823–1864`

The rule recognises the constraint `256·b1 + b0 = n` with `b0, b1 ∈ [0, 256)`
(the four `PFS.mem` membership checks) and solves for the two bytes.

- **Correct solution:** `b1 = n / 256`, `b0 = n mod 256 = n − 256·b1`.
- **Code computes:**
  ```ocaml
  let vb1 = Z.div n _256 in
  let vb0 = Z.sub n vb1 in
  ```

**Concrete failure — `n = 512`:**

| | b1 | b0 |
|---|---|---|
| Correct | `512 / 256 = 2` | `512 mod 256 = 0` |
| Code | `vb1 = 2` | `vb0 = 512 − 2 = 510` |

The code emits `b1 = 2 ∧ b0 = 510`. But the PFS already carries `b0 < 256`, so
`b0 = 510` is contradictory and the whole constraint reduces to `false`.

The authors flag it themselves in the source comment:
> *Opale: The b0 = n-b1 bit is weird?? Why not mod?*

**Fix (both rules):**
```ocaml
let vb0 = Z.sub n (Z.mul _256 vb1)   (* equivalently Z.rem n _256 *)
```

- Tag `060` (`Reduction.ml:1844–1864`) is the operand-swapped twin
  (`Equal`'s LHS/RHS flipped) and carries the **identical** bug — fix both.
- The `if Z.gt n _65535 then false` guard is correct (max value is
  `256·255 + 255 = 65535`).

---

## 2. HIGH-CONFIDENCE UNSOUNDNESS — tag `068`: `NumToInt` equality rewrite missing the `IsInt` guard

**Location:** `Reduction.ml:1879–1880`
```ocaml
| BinOp (UnOp (NumToInt, x), Equal, y) | BinOp (y, Equal, UnOp (NumToInt, x))
  -> BinOp (UnOp (IntToNum, y), Equal, x)
```
i.e. `NumToInt(x) = y  ⟶  IntToNum(y) = x`.

`NumToInt` is `Z.of_float` (`CExprEval.ml:141–143`) — it **truncates toward
zero**, so it is many-to-one: `NumToInt(x) = y` holds for *any* `x ∈ [y, y+1)`.
The rewrite's RHS `IntToNum(y) = x` pins `x = float(y)` exactly. Therefore:

```
RHS ⟹ LHS   but   LHS ⇏ RHS
```

**Corroboration:** the rule immediately above, `015` (`Reduction.ml:1453`),
performs the analogous cast collapse
`IntToNum(NumToInt(le)) → le` **only** under
`PFS.mem pfs (UnOp (IsInt, le))`. Tag `068` omits exactly that guard. The rule
is sound only if every `NumToInt` site is over a provably-integral number,
which the pattern does not enforce.

**Suggested fix:** guard with `IsInt(x)`, or keep only the sound direction.

**Runnable demonstration (Gillian-JS):**
`Gillian-JS/Examples/simplification_bugs/rule_068_numtoint_unsound.js`
```
dune exec -- gillian-js verify \
  Gillian-JS/Examples/simplification_bugs/rule_068_numtoint_unsound.js -l disabled
```
The spec assumes only `as_int(#x) == 3` (written `as_int #x == as_int 3.5`;
satisfiable by any `#x ∈ [3.0, 4.0)`) and returns the input unchanged, yet
claims `ret == 3`. A sound verifier must reject it. Gillian reports
**"All specs succeeded"** (`REDUCE_068` fires 50×). Guarding rule 068 with
`when PFS.mem pfs (UnOp (IsInt, x))` flips the result to the correct
**"Couldn't satisfy postcondition"**, confirming 068 is the cause.
