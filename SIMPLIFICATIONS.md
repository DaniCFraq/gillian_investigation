# Gillian simplification dictionary

A lookup table for every `check_reduction` tag that Gillian can emit, so a bare number from `file_simplification_results.csv` can be read as an actual simplification.

Each tag is logged as `[REDUCE_<tag>]` when it fires and can be switched off with `disable_reductions [ <tag> ]`. Tags live in two files:

- **`Reduction.ml`** — expression-level reduction (`reduce_lexpr`).
- **`Simplifications.ml`** — pure-formula-set simplification run before the SMT solver (600-series).

**How to read the number.** The prefix tells you the family; underscores add depth (`105` → `105_13` → `105_13_3` is binary-op → integer `*` → `0 * _`). Notation in the table: `++` concat, `len(x)`, `x[i]` nth, `x[a..b]` sublist, `rev`, `car`/`cdr`, `∈`/`⊆`/`∖`/`∪`/`∩` sets, `<i`/`<=i` integer order, `<f`/`<=f` float order.

_Total: 420 tag call-sites across 9 functions._

---

## `normalise_cat` — List-concat normaliser — final shape
*Reduction.ml* · 4 tags

Picks the final form of a flattened `LstCat` after inner cats have been merged and literal runs joined.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `400` | `match nles with` | Final-shape dispatch for a flattened concat (parent of `400_*`). |
| `400_1` | `[]` ⟶ `EList []` | Flattened concat is empty ⟶ `[]`. |
| `400_2` | `[ x ]` ⟶ `x` | Concat of a single part ⟶ that part (drop the `LstCat`). |
| `400_3` | `_` ⟶ `NOp (LstCat, nles)` | Concat of two or more parts ⟶ kept as `LstCat`. |

## `normalise_list_expressions` — List-structure normaliser
*Reduction.ml* · 34 tags

Runs after every `reduce_lexpr_loop` step. Pushes list operations (`nth`, `car`, `cdr`, `len`) through known list structure and recurses structurally into every other node.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `401` | `Lit (LList lst)` ⟶ `Expr.from_lit_list (LList lst)` | Literal list `LList` ⟶ expanded to an `EList`. |
| `402` | `Lit _ \| LVar _ \| ALoc _ \| PVar _` ⟶ `le` | Leaf (literal / lvar / aloc / pvar) ⟶ unchanged. |
| `403` | `NOp (LstCat, les)` ⟶ `normalise_cat f les` | Concat ⟶ delegated to `normalise_cat`. |
| `404` | `BinOp (le, LstNth, n)` | `l[n]` ⟶ list-indexing subtree dispatch (parent of `404_*`). |
| `404_1` | `Some k` ⟶ `k` | `l[n]` on a concrete list, index in range ⟶ the element. |
| `404_2` | `None` ⟶ `raise (exn "Invalid List Expression")` | `l[n]` on a concrete list, index out of range ⟶ error (invalid list expression). |
| `404_3` | `Left k` ⟶ `k` | `(EList ++ tl)[n]` with n inside the literal head ⟶ that element. |
| `404_4` | `Right sz` | `(EList ++ tl)[n]` with n past the head ⟶ recurse: `tl[n - |head|]`. |
| `404_5` | `NOp (LstCat, LstSub (_lst, _start, len) :: tl), idx` ⟶ `Expr.list_nth (NOp (LstCat, tl)) 0` | `(l[a..len] ++ tl)[idx]` when the slice length equals the index ⟶ first element of `tl`. |
| `404_6` | `_, Lit (Num _)` ⟶ `raise (exn "LstNth with float")` | List indexed by a float ⟶ error. |
| `404_7` | `le, n` ⟶ `BinOp (le, LstNth, n)` | General `l[n]` ⟶ unchanged. |
| `405` | `BinOp (le1, op, le2)` ⟶ `BinOp (f le1, op, f le2)` | Other binary op ⟶ recurse into both operands. |
| `406` | `UnOp (Car, lst)` | `car` ⟶ head subtree dispatch (parent of `406_*`). |
| `406_1` | `EList lst` ⟶ `List.hd lst` | `car` of a concrete list ⟶ its head. |
| `406_2` | `NOp (LstCat, EList lst_l :: _)` ⟶ `List.hd lst_l` | `car (EList ++ ...)` ⟶ head of the literal prefix. |
| `406_3` | `lst` ⟶ `UnOp (Car, lst)` | `car` of anything else ⟶ unchanged. |
| `407` | `UnOp (Cdr, lst)` | `cdr` ⟶ tail subtree dispatch (parent of `407_*`). |
| `407_1` | `EList lst` ⟶ `EList (List.tl lst)` | `cdr` of a concrete list ⟶ its tail. |
| `407_2` | `NOp (LstCat, EList lst_l :: tl)` ⟶ `NOp (LstCat, EList (List.tl lst_l) :: tl)` | `cdr (EList ++ tl)` ⟶ `tail(EList) ++ tl`. |
| `407_3` | `lst` ⟶ `UnOp (Cdr, lst)` | `cdr` of anything else ⟶ unchanged. |
| `408` | `UnOp (LstLen, le)` | `len` ⟶ length subtree dispatch (parent of `408_*`). |
| `408_1` | `EList lst` ⟶ `Expr.int (List.length lst)` | `len` of a concrete list ⟶ its literal length. |
| `408_2` | `NOp (LstCat, EList lst :: tl)` | `len (EList ++ tl)` ⟶ `|EList| + len(tl)`. |
| `408_3` | `le` ⟶ `UnOp (LstLen, le)` | `len` of anything else ⟶ unchanged. |
| `409` | `UnOp (op, le)` ⟶ `UnOp (op, f le)` | Other unary op ⟶ recurse into operand. |
| `410` | `NOp (op, les)` ⟶ `NOp (op, List.map f les)` | Other n-ary op ⟶ recurse into each operand. |
| `411` | `EList lst` ⟶ `EList (List.map f lst)` | `EList` ⟶ recurse into each element. |
| `412` | `ESet lst` ⟶ `ESet (List.map f lst)` | `ESet` ⟶ recurse into each element. |
| `413` | `LstSub (le1, le2, le3)` ⟶ `LstSub (f le1, f le2, f le3)` | `LstSub` ⟶ recurse into list, start and length. |
| `414` | `Exists (bt, le)` ⟶ `Exists (bt, f le)` | `Exists` ⟶ recurse into the body. |
| `415` | `ForAll (bt, le)` ⟶ `ForAll (bt, f le)` | `ForAll` ⟶ recurse into the body. |
| `416` | `ConstructorApp (n, les)` ⟶ `ConstructorApp (n, List.map f les)` | Constructor application ⟶ recurse into each argument. |
| `417` | `FuncApp (n, les)` ⟶ `FuncApp (n, List.map f les)` | Logical-function application ⟶ recurse into each argument. |
| `418` | `Cases (le, cs)` | `Cases` ⟶ recurse into scrutinee and case bodies. |

## `prefix_catch` — Arithmetic canonicalisation (Cint / Cnum)
*Reduction.ml* · 20 tags

Turns integer (200-series) and float (300-series) arithmetic into a polynomial normal form: minus becomes plus-of-negation and products are distributed over sums, so `cut` can compare both sides.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `200` | `BinOp (e1, IPlus, e2)` | Canonicalise integer `e1 + e2` (normal-form addition). |
| `201` | `BinOp (e1, IMinus, e2)` ⟶ `f (e1 + ineg e2)` | Integer `e1 - e2` ⟶ `e1 + (-e2)`. |
| `202` | `UnOp (IUnaryMinus, e)` ⟶ `(` | Integer unary minus `-e` — dispatch. |
| `202_1` | `BinOp (e1, IPlus, e2)` ⟶ `f (ineg e1) + f (ineg e2)` | `-(e1 + e2)` ⟶ `(-e1) + (-e2)`. |
| `202_2` | `ce` ⟶ `UnOp (IUnaryMinus, ce)` | `-ce` of a canonical term ⟶ keep the unary minus. |
| `203` | `BinOp (e1, ITimes, e2)` ⟶ `(` | Canonicalise integer `e1 * e2` — distribute over sums. |
| `203_1` | `BinOp (e1, IPlus, e2), fe2` ⟶ `f ((e1 * fe2) + (e2 * fe2))` | `(e1 + e2) * f` ⟶ `e1*f + e2*f`. |
| `203_2` | `fe1, BinOp (e1, IPlus, e2)` ⟶ `f ((fe1 * e1) + (fe1 * e2))` | `f * (e1 + e2)` ⟶ `f*e1 + f*e2`. |
| `203_3` | `fe1, fe2` | Product of two sum-free terms ⟶ multiply the monomials. |
| `204` | `_` ⟶ `e` | Integer expression with no arithmetic head ⟶ leaf (unchanged). |
| `300` | `BinOp (e1, FPlus, e2)` | Canonicalise float `e1 +. e2` (normal-form addition). |
| `301` | `BinOp (e1, FMinus, e2)` ⟶ `f (e1 +. fneg e2)` | Float `e1 -. e2` ⟶ `e1 +. (-.e2)`. |
| `302` | `UnOp (FUnaryMinus, e)` ⟶ `(` | Float unary minus `-.e` — dispatch. |
| `302_1` | `BinOp (e1, FPlus, e2)` ⟶ `f (fneg e1) +. f (fneg e2)` | `-.(e1 +. e2)` ⟶ `(-.e1) +. (-.e2)`. |
| `302_2` | `ce` ⟶ `UnOp (FUnaryMinus, ce)` | `-.ce` of a canonical term ⟶ keep the unary minus. |
| `303` | `BinOp (e1, FTimes, e2)` ⟶ `(` | Canonicalise float `e1 *. e2` — distribute over sums. |
| `303_1` | `BinOp (e1, FPlus, e2), fe2` ⟶ `f ((e1 *. fe2) +. (e2 *. fe2))` | `(e1 +. e2) *. f` ⟶ `e1*.f +. e2*.f`. |
| `303_2` | `fe1, BinOp (e1, FPlus, e2)` ⟶ `f ((fe1 *. e1) +. (fe1 *. e2))` | `f *. (e1 +. e2)` ⟶ `f*.e1 +. f*.e2`. |
| `303_3` | `fe1, fe2` | Product of two sum-free float terms ⟶ multiply the monomials. |
| `304` | `_` ⟶ `e` | Float expression with no arithmetic head ⟶ leaf (unchanged). |

## `reduce_lexpr_loop` — Main expression reducer
*Reduction.ml* · 327 tags

The core rewriter, dispatched on the shape of the expression. Tags 001-124 are the top-level dispatch; the large sub-trees are `008_*` (quantifiers), `013_*` (`LstSub`), `022_*` (unary ops) and `105_*` (binary ops).

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `001` | `Lit _ \| PVar _ \| ALoc _` ⟶ `le` | Literal / program-var / aloc ⟶ unchanged. |
| `002` | `LVar _ when reduce_lvars` | Logical var with `reduce_lvars` on ⟶ substitute it using the PFS. |
| `003` | `LVar _` ⟶ `le` | Logical var ⟶ unchanged. |
| `004` | `EList les` | `EList` ⟶ reduce each element. |
| `005` | `ESet les` | `ESet` ⟶ reduce each element. |
| `006` | `ForAll` | `ForAll` ⟶ reduce under the binder (case a). |
| `007` | `ForAll` | `ForAll` ⟶ reduce under the binder (case b). |
| `008` | `ForAll (bt, e) \| Exists (bt, e)` | `ForAll`/`Exists` with binders ⟶ reduce body and prune binders. |
| `008_0` | `_, []` ⟶ `re` | Quantifier with no binders left ⟶ just the body. |
| `008_1` | `ForAll _, _` ⟶ `ForAll (bt, re)` | `ForAll` with binders ⟶ keep as `ForAll`. |
| `008_2` | `Exists _, _` ⟶ `Exists (bt, re)` | `Exists` with binders ⟶ keep as `Exists`. |
| `008_3` | `_, _` ⟶ `failwith "Impossible."` | Unreachable quantifier shape ⟶ internal error. |
| `010` | `_` ⟶ `true` | Recognised tautology ⟶ `true`. |
| `010_1` | `_` ⟶ `true` | PFS proves the formula ⟶ `true`. |
| `010_2` | `_` ⟶ `false ->` | PFS refutes the formula ⟶ `false`. |
| `011` | `_` | `LstSub` dispatch (start/length analysis). |
| `013` | `LstSub (le1, le2, le3)` | `LstSub (l, start, num)` — sublist subtree dispatch. |
| `013_1` | `_, _, Lit (Int z) when Z.equal z Z.zero` ⟶ `EList []` | `l[_ .. 0]` (length 0) ⟶ `[]`. |
| `013_2` | `flx, Lit (Int z), UnOp (LstLen, fle1)` ⟶ `fle1` | `l[start .. len(l)]`... ⟶ the underlying list. |
| `013_3` | `NOp (LstCat, [ x ]), fle2, fle3` ⟶ `f (LstSub (x, fle2, fle3))` | `(l)[..]` over a single-element concat ⟶ slice that element. |
| `013_4` | `NOp (LstCat, flx :: _), Lit (Int z), UnOp (LstLen, fle1)` ⟶ `fle1` | `(x ++ _)[start .. len(x)]` ⟶ `x`. |
| `013_5` | `Some first` | Sublist over concat — prefix found. |
| `013_6` | `_` | Sublist over concat — fallthrough. |
| `013_7` | `fle1, UnOp (LstLen, lx), fle3 when fst (list_prefix pfs lx fle1)` | `l1[start .. len(lx)]` when `lx` is a known prefix of `l1` ⟶ that prefix. |
| `013_8` | `_` | Sublist prefix analysis fallthrough. |
| `013_9` | `NOp (LstCat, EList les :: _), Lit (Int s), Lit (Int f)` | `(EList ++ _)[s .. f]` with literal bounds ⟶ computed slice. |
| `013_10` | `EList lst, Lit (Int start), Lit (Int len)` | `EList[start .. len]` with literal bounds ⟶ computed slice. |
| `013_11` | `Lit (LList lst), Lit (Int start), Lit (Int len)` | `LList[start .. len]` with literal bounds ⟶ computed slice. |
| `013_12` | `NOp (LstCat, lel :: ler), fle2, fle3` | `(l ++ r)[..]` ⟶ split the slice across the concat. |
| `013_13` | `NOp (LstCat, EList lel :: ler), Lit (Int n), fle3 when Z.gt n Z.zero` | `(EList ++ r)[n ..]` with n>0 ⟶ drop n from the literal head. |
| `013_14` | `NOp (LstCat, lel :: ler), Lit (Int z), fle3` | `(l ++ r)[0 ..]` ⟶ slice within the head / spill into tail. |
| `013_15` | `_` | `LstSub` fallthrough ⟶ unchanged. |
| `016` | `UnOp (ToNumberOp, UnOp (ToStringOp, le))` | `toNumber(toString le)` ⟶ simplified. |
| `017` | `UnOp (LstRev, UnOp (LstRev, le))` | `rev(rev le)` ⟶ `le`. |
| `018` | `UnOp (Not, BinOp (le1, FLessThan, le2))` | `¬(a <f b)` ⟶ `b <=f a`. |
| `019` | `UnOp (Not, BinOp (le1, FLessThanEqual, le2))` | `¬(a <=f b)` ⟶ `b <f a`. |
| `020` | `UnOp (Not, BinOp (le1, ILessThan, le2))` | `¬(a <i b)` ⟶ `b <=i a`. |
| `021` | `UnOp (Not, BinOp (le1, ILessThanEqual, le2))` | `¬(a <=i b)` ⟶ `b <i a`. |
| `022` | `UnOp (op, le)` | `UnOp(op, le)` — unary-operator subtree dispatch. |
| `022_1` | `_, Lit lit` | `op(literal)` ⟶ concretely evaluate. |
| `022_2` | `Not, UnOp (Not, ex)` ⟶ `ex` | `¬¬x` ⟶ `x`. |
| `022_3` | `Not, BinOp (ex, And, ey)` ⟶ `BinOp (UnOp (Not, ex), Or, UnOp (Not, ey))` | `¬(x ∧ y)` ⟶ `¬x ∨ ¬y` (De Morgan). |
| `022_4` | `Not, BinOp (ex, Or, ey)` ⟶ `BinOp (UnOp (Not, ex), And, UnOp (Not, ey))` | `¬(x ∨ y)` ⟶ `¬x ∧ ¬y` (De Morgan). |
| `022_5` | `Not, _` ⟶ `def` | `¬_` other ⟶ unchanged. |
| `022_6` | `TypeOf, _` | `typeOf(_)` ⟶ type-of subtree. |
| `022_6_1` | `false` | `typeOf` could not be determined (literal-false branch). |
| `022_6_2` | `None` ⟶ `def` | `typeOf` unknown ⟶ unchanged. |
| `022_6_3` | `Some t` ⟶ `Lit (Type t)` | `typeOf` resolved to type `t` ⟶ `Lit (Type t)`. |
| `022_7` | `Car, EList (hd :: _)` ⟶ `hd` | `car [hd; …]` ⟶ `hd`. |
| `022_8` | `Car, _ when lexpr_is_list gamma fle` | `car` of a known list ⟶ normalised. |
| `022_9` | `Cdr, EList (_ :: tl)` ⟶ `EList tl` | `cdr [_; …tl]` ⟶ `tl`. |
| `022_10` | `Cdr, _ when lexpr_is_list gamma fle` | `cdr` of a known list ⟶ normalised. |
| `022_11` | `LstLen, EList le` ⟶ `Expr.int (List.length le)` | `len(EList)` ⟶ literal length. |
| `022_12` | `LstLen, NOp (LstCat, [])` ⟶ `Expr.zero_i` | `len(empty concat)` ⟶ `0`. |
| `022_13` | `LstLen, NOp (LstCat, les) when lexpr_is_list gamma fle` | `len(concat)` of a known list ⟶ sum of part lengths. |
| `022_14` | `LstLen, LstSub (_, _, len) when lexpr_is_list gamma fle` ⟶ `len` | `len(l[_.._..len])` ⟶ `len`. |
| `022_15` | `LstLen, UnOp (LstRev, le)` ⟶ `UnOp (LstLen, f le)` | `len(rev l)` ⟶ `len(l)`. |
| `022_16` | `LstLen, _ when lexpr_is_list gamma fle` ⟶ `def` | `len(_)` of a known list ⟶ unchanged. |
| `022_17` | `LstRev, EList le` ⟶ `EList (List.rev le)` | `rev(EList)` ⟶ reversed literal list. |
| `022_18` | `LstRev, NOp (LstCat, les) when lexpr_is_list gamma fle` | `rev(concat)` of a known list ⟶ reverse + flip order. |
| `022_19` | `LstRev, _ when lexpr_is_list gamma fle` ⟶ `def` | `rev(_)` of a known list ⟶ unchanged. |
| `022_20` | `Car, _ \| Cdr, _ \| LstLen, _ \| LstRev, _` | `car`/`cdr`/`len`/`rev` of a non-list ⟶ unchanged. |
| `022_21` | `SetToList, ESet le` ⟶ `EList (Expr.Set.elements (Expr.Set.of_list le))` | `setToList(ESet)` ⟶ deduplicated element list. |
| `022_22` | `StrLen, _ when lexpr_is_string gamma fle` | `strlen` of a known string ⟶ simplified. |
| `022_23` | `StrLen, _` | `strlen(_)` ⟶ unchanged. |
| `022_24` | `FUnaryMinus, _ when lexpr_is_number ~gamma def` | Float unary minus ⟶ `simplify_num_arithmetic_lexpr`. |
| `022_25` | `IUnaryMinus, _ when lexpr_is_int ~gamma def` | Integer unary minus ⟶ `simplify_int_arithmetic_lexpr`. |
| `022_26` | `IsInt, UnOp (IntToNum, e)` ⟶ `(` | `isInt(IntToNum e)` ⟶ type-of-`e` subtree. |
| `022_26_1` | `Some IntType, _` ⟶ `Expr.true_` | `isInt(IntToNum e)` with `e : Int` ⟶ `true`. |
| `022_26_2` | `Some _, _` ⟶ `Expr.false_` | `isInt(IntToNum e)` with `e` non-int ⟶ `false`. |
| `022_26_3` | `None, _` ⟶ `BinOp (UnOp (TypeOf, e), Equal, Lit (Type IntType))` | `isInt(IntToNum e)` type unknown ⟶ `typeOf(e) = Int`. |
| `022_27` | `_, _` ⟶ `def` | Unary-op fallthrough ⟶ unchanged. |
| `022_28` | `CExprEval.TypeError err_msg` | Concrete eval type error ⟶ raise (formerly `022_1_1`). |
| `022_29` | `CExprEval.EvaluationError err_msg` | Concrete eval error ⟶ raise (formerly `022_1_2`). |
| `022_30` | `e` ⟶ `raise e` | Other eval exception ⟶ re-raise (formerly `022_1_3`). |
| `023` | `NOp (LstCat, LstSub (x1, Lit (Int z), z1) :: LstSub (x2, y2, z3) :: rest)` | `l1[0..z] ++ l2[..] ++ rest` ⟶ adjacent sublices merged. |
| `024` | `NOp (LstCat, fst :: rest) when PFS.mem pfs (BinOp (fst, Equal, EList []))` | `(fst ++ rest)` with `fst = []` known ⟶ drop the empty head. |
| `025` | `NOp (LstCat, [ x; LstSub (LVar y, UnOp (LstLen, x'), len) ])` | `x ++ y[len(x) .. len]` ⟶ simplified slice. |
| `026` | `NOp (LstCat, les)` | General concat ⟶ normalise. |
| `027` | `NOp (SetUnion, les)` | `SetUnion` ⟶ normalise. |
| `027_1` | `[]` ⟶ `ESet []` | `SetUnion []` ⟶ `∅`. |
| `027_2` | `[ x ]` ⟶ `x` | `SetUnion [s]` ⟶ `s`. |
| `027_3` | `_` ⟶ `NOp (SetUnion, fles)` | `SetUnion` of several ⟶ kept (normalised). |
| `028` | `NOp (SetInter, [ BinOp (le1, SetDiff, le2); ESet le3 ])` | `(a ∖ b) ∩ {c}` ⟶ simplified. |
| `029` | `NOp (SetInter, les)` | `SetInter` ⟶ normalise. |
| `029_1` | `[], _` ⟶ `ESet []` | `∅ ∩ _` ⟶ `∅`. |
| `029_2` | `_, []` | `_ ∩ ∅` ⟶ `∅`. |
| `029_3` | `_` | `SetInter` general ⟶ kept (normalised). |
| `030` | `BinOp (e1, Equal, e2) when Expr.equal e1 e2` | `e = e` ⟶ `true` (reflexivity). |
| `031` | `BinOp (UnOp (ToStringOp, e1), Equal, UnOp (ToStringOp, e2))` | `toString a = toString b` ⟶ `a = b` (injective). |
| `032` | `BinOp (ALoc x, Equal, ALoc y) when not matching` | `aloc1 = aloc2` (not matching) ⟶ `false` (distinct abstract locations). |
| `033` | `BinOp (ALoc _, Equal, Lit (Loc _)) \| BinOp (Lit (Loc _), Equal, ALoc _)` | `aloc = loc` ⟶ `false` (abstract never equals concrete location). |
| `034` | `BinOp (Lit (LList ll), Equal, Lit (LList lr))` | Two literal lists equal ⟶ compare them. |
| `035` | `BinOp (Lit (LList ll), Equal, EList le)` | `LList = EList` ⟶ element-wise equality. |
| `036` | `BinOp (EList [ x ], Equal, y) when Expr.equal x y` | `[x] = y` with `x = y` ⟶ simplified. |
| `037` | `BinOp (x, Equal, EList [ y ]) when Expr.equal x y` | `x = [y]` with `x = y` ⟶ simplified. |
| `038` | `BinOp (EList ll, Equal, EList lr)` | `EList = EList` ⟶ element-wise equality (length + each). |
| `039` | `_` | List-equality fallthrough. |
| `040` | `BinOp (LstSub (e1, Lit (Int z), el), Equal, e2)` | `l[0..el] = e2` ⟶ sublist equality rewrite. |
| `041` | `BinOp (e2, Equal, LstSub (e1, Lit (Int z), el))` | `e2 = l[0..el]` ⟶ sublist equality rewrite. |
| `042` | `BinOp (e2, Equal, LstSub (NOp (LstCat, e1 :: _), Lit (Int z), el))` | `e2 = (l ++ _)[0..el]` ⟶ sublist-of-concat equality. |
| `043` | `BinOp (LstSub (NOp (LstCat, e1 :: _), Lit (Int z), el), Equal, e2)` | `(l ++ _)[0..el] = e2` ⟶ sublist-of-concat equality. |
| `044` | `BinOp (e2, Equal, LstSub (NOp (LstCat, e3 :: e1 :: _), ex, ey))` | `e2 = (a ++ b ++ _)[..]` ⟶ sublist-of-concat equality (2-prefix). |
| `045` | `BinOp (LstSub (NOp (LstCat, e3 :: e1 :: _), ex, ey), Equal, e2)` | `(a ++ b ++ _)[..] = e2` ⟶ sublist-of-concat equality (2-prefix). |
| `046` | `BinOp (NOp (LstCat, fl :: rl), Equal, NOp (LstCat, fr :: rr))` ⟶ `BinOp (NOp (LstCat, rl), Equal, NOp (LstCat, rr))` | `(fl::rl) = (fr::rr)` (concat) ⟶ compare heads, then tails. |
| `047` | `BinOp` | Concat-equality rewrite. |
| `048` | `BinOp` | Concat-equality rewrite. |
| `049` | `BinOp` | Concat-equality rewrite. |
| `050` | `SetSub ),` ⟶ `e` | `SetSub` equality ⟶ simplified. |
| `051` | `BinOp (Lit (Bool false), Equal, BinOp (e1, ILessThan, e2))` | `false = (a <i b)` ⟶ `b <=i a`. |
| `052` | `BinOp (Lit (Bool false), Equal, BinOp (e1, ILessThanEqual, e2))` | `false = (a <=i b)` ⟶ `b <i a`. |
| `053` | `BinOp (Lit (Bool false), Equal, BinOp (e1, FLessThan, e2))` | `false = (a <f b)` ⟶ `b <=f a`. |
| `054` | `BinOp (Lit (Bool false), Equal, BinOp (e1, FLessThanEqual, e2))` | `false = (a <=f b)` ⟶ `b <f a`. |
| `055` | `BinOp` ⟶ `BinOp (LVar x, Equal, LVar y)` | Equality between lvar-headed binops ⟶ cancel to `x = y`. |
| `056` | `BinOp` ⟶ `BinOp (LVar x, Equal, LVar y)` | Equality between lvar-headed binops ⟶ cancel to `x = y`. |
| `057` | `BinOp (BinOp (Lit (Num x), FPlus, LVar y), Equal, LVar z)` ⟶ `Expr.false_` | `(x + y) = z` that cannot hold ⟶ `false`. |
| `058` | `BinOp (BinOp (Lit (Int x), IPlus, LVar y), Equal, LVar z)` ⟶ `Expr.false_` | `(x + y) = z` (int) that cannot hold ⟶ `false`. |
| `059` | `BinOp` | Arithmetic-equality rewrite. |
| `060` | `BinOp` | Arithmetic-equality rewrite. |
| `061` | `BinOp (BinOp (e, FTimes, Lit (Num x)), Equal, Lit (Num 0.)) when x <> 0.` ⟶ `BinOp (e, Equal, Lit (Num 0.))` | `(e * x) = 0` with `x ≠ 0` (float) ⟶ `e = 0`. |
| `062` | `BinOp (BinOp (Lit (Num x), FTimes, e), Equal, Lit (Num 0.)) when x <> 0.` ⟶ `BinOp (e, Equal, Lit (Num 0.))` | `(x * e) = 0` with `x ≠ 0` (float) ⟶ `e = 0`. |
| `063` | `BinOp (BinOp (e, ITimes, Lit (Int x)), Equal, Lit (Int n))` | `(e * x) = n` (int) ⟶ divisibility rewrite. |
| `064` | `BinOp (BinOp (Lit (Int x), ITimes, e), Equal, Lit (Int n))` | `(x * e) = n` (int) ⟶ divisibility rewrite. |
| `065` | `BinOp (BinOp (a, FTimes, b), FMod, c)` ⟶ `Expr.num 0.` | `(a * b) mod c` (float) ⟶ `0`. |
| `066` | `BinOp (x, FTimes, BinOp (y, FDiv, z)) when x = z` ⟶ `y` | `x * (y / x)` ⟶ `y`. |
| `067` | `BinOp (BinOp (x, FDiv, y), FTimes, z) when y = z` ⟶ `x` | `(x / y) * y` ⟶ `x`. |
| `069` | `BinOp (BinOp (Lit (String rs), StrCat, s), Equal, Lit (String ls))` | `(rs ++ s) = ls` (strings) ⟶ prefix-match rewrite. |
| `069_1` | `-1` ⟶ `Expr.false_` | String compare returns -1 ⟶ `false`. |
| `069_2` | `0 when ls <> rs` ⟶ `Expr.false_` | Prefixes differ (compare 0) ⟶ `false`. |
| `069_3` | `0` ⟶ `BinOp (s, Equal, Lit (String ""))` | Compare 0 ⟶ `s = ""`. |
| `069_4` | `1 when not (String.starts_with ~prefix:rs ls)` ⟶ `Expr.false_` | `rs` is not a prefix of `ls` ⟶ `false`. |
| `069_5` | `1` ⟶ `BinOp (s, Equal, Lit (String (String.sub ls lrs (lls - lrs))))` | Prefix matches ⟶ `s = <remaining suffix>`. |
| `069_6` | `_` ⟶ `raise (Exceptions.Impossible "int comparison not in {-1, 0, 1}")` | Comparison out of {-1,0,1} ⟶ impossible. |
| `070` | `BinOp (BinOp (sl1, StrCat, sr1), Equal, BinOp (sl2, StrCat, sr2))` ⟶ `BinOp (sr1, Equal, sr2)` | `(sl1 ++ sr1) = (sl2 ++ sr2)` ⟶ compare suffixes. |
| `071` | `BinOp (BinOp (sl1, StrCat, sr1), Equal, BinOp (sl2, StrCat, sr2))` ⟶ `BinOp (sl1, Equal, sl2)` | `(sl1 ++ sr1) = (sl2 ++ sr2)` ⟶ compare prefixes. |
| `072` | `BinOp (BinOp (sl, StrCat, sr), Equal, s) when sl = s` | `(sl ++ sr) = sl` ⟶ `sr = ""`. |
| `073` | `BinOp (BinOp (sl, StrCat, sr), Equal, s) when sr = s` | `(sl ++ sr) = sr` ⟶ `sl = ""`. |
| `074` | `BinOp (s, Equal, BinOp (sl, StrCat, sr)) when sl = s` | `sl = (sl ++ sr)` ⟶ `sr = ""`. |
| `075` | `BinOp (s, Equal, BinOp (sl, StrCat, sr)) when sr = s` | `sr = (sl ++ sr)` ⟶ `sl = ""`. |
| `076` | `BinOp (BinOp (sl, StrCat, sr), Equal, Lit (String ""))` | `(sl ++ sr) = ""` ⟶ both empty. |
| `077` | `BinOp (Lit (String s), Equal, UnOp (ToStringOp, le1))` | `s = toString(le1)` ⟶ recovered numeric/structural equality. |
| `077_1` | `""` ⟶ `Expr.false_` | `toString(le) = ""` ⟶ `false` (no number prints empty). |
| `077_2` | `"Infinity" \| "-Infinity" \| "NaN"` ⟶ `le` | String is `Infinity`/`-Infinity`/`NaN` ⟶ unchanged. |
| `077_3` | `_` | Otherwise ⟶ recovered `le = toNumber(s)` equality. |
| `078` | `BinOp (Lit Empty, Equal, e) \| BinOp (e, Equal, Lit Empty)` | `Empty = e` / `e = Empty` ⟶ simplified. |
| `078_1` | `Lit l when l <> Empty` ⟶ `Expr.false_` | `Empty = literal` (≠Empty) ⟶ `false`. |
| `078_2` | `EList _ \| ESet _` ⟶ `Expr.false_` | `Empty = list/set` ⟶ `false`. |
| `078_3` | `_` ⟶ `le` | `Empty = _` otherwise ⟶ unchanged. |
| `079` | `BinOp (Lit l1, Equal, Lit l2)` ⟶ `Expr.bool (l1 = l2)` | Two literals compared ⟶ decided by literal equality. |
| `080` | `BinOp (Lit Nono, Equal, PVar _) \| BinOp (PVar _, Equal, Lit Nono)` ⟶ `le` | `Nono = pvar` ⟶ unchanged (program var can't be None here). |
| `081` | `BinOp (Lit Nono, Equal, LVar x) \| BinOp (LVar x, Equal, Lit Nono)` | `Nono = lvar` ⟶ simplified. |
| `081_1` | `None \| Some NoneType` ⟶ `le` | `Nono = lvar` typed `None` ⟶ unchanged. |
| `081_2` | `_` ⟶ `Expr.false_` | `Nono = lvar` otherwise ⟶ `false`. |
| `082` | `BinOp (Lit Nono, Equal, e) \| BinOp (e, Equal, Lit Nono)` | `Nono = e` / `e = Nono` ⟶ simplified. |
| `082_1` | `Lit Nono` ⟶ `Expr.true_` | `Nono = Nono` ⟶ `true`. |
| `082_2` | `Lit _` ⟶ `Expr.false_` | `Nono = literal` ⟶ `false`. |
| `082_3` | `LVar x when Type_env.get gamma x = Some NoneType` ⟶ `BinOp (Lit Nono, Equal, fe)` | `Nono = lvar` typed `None` ⟶ `Nono = e`. |
| `082_4` | `PVar _` ⟶ `BinOp (Lit Nono, Equal, fe)` | `Nono = pvar` ⟶ `Nono = e`. |
| `082_5` | `LVar _` ⟶ `Expr.false_` | `Nono = lvar` (untyped) ⟶ `false`. |
| `082_6` | `_` ⟶ `Expr.false_` | `Nono = _` otherwise ⟶ `false`. |
| `083` | `BinOp (UnOp (TypeOf, BinOp (_, StrCat, _)), Equal, Lit (Type t))` ⟶ `Expr.false_` | `typeOf(_ ++ _) = T` with T≠String ⟶ `false`. |
| `084` | `BinOp (UnOp (TypeOf, BinOp (_, SetMem, _)), Equal, Lit (Type t))` ⟶ `Expr.false_` | `typeOf(_ ∈ _) = T` with T≠Bool ⟶ `false`. |
| `085` | `BinOp (Lit (Bool true), Impl, e)` ⟶ `e` | `true ⇒ e` ⟶ `e`. |
| `086` | `BinOp (Lit (Bool false), And, _) \| BinOp (_, And, Lit (Bool false))` | `false ∧ _` ⟶ `false`. |
| `087` | `BinOp (_, Impl, Lit (Bool true))` ⟶ `Expr.true_` | `_ ⇒ true` ⟶ `true`. |
| `088` | `BinOp (left, Impl, Lit (Bool false))` ⟶ `UnOp (Not, left)` | `left ⇒ false` ⟶ `¬left`. |
| `089` | `BinOp (left, Impl, right)` | `left ⇒ right` ⟶ implication rewrite. |
| `089_1` | `Lit (Bool true)` ⟶ `right` | `true ⇒ right` ⟶ `right`. |
| `089_2` | `Lit (Bool false)` ⟶ `Expr.true_` | `false ⇒ _` ⟶ `true`. |
| `089_3` | `left` ⟶ `BinOp (left, Impl, f right)` | `left ⇒ right` ⟶ keep, reducing `right`. |
| `089_4` | `left` | Implication fallthrough ⟶ kept. |
| `090` | `BinOp (le, LstNth, idx)` | `l[idx]` (LstNth) ⟶ list-indexing subtree dispatch. |
| `090_1` | `Lit (Int n) when Z.leq Z.zero n` | `l[n]` with `n ≥ 0` literal ⟶ indexing branch. |
| `090_2` | `Lit (Int _) \| Lit (Num _)` | `l[literal]` ⟶ indexing branch. |
| `090_3` | `_` ⟶ `BinOp (fle, LstNth, fidx)` | `l[idx]` general ⟶ kept (operands reduced). |
| `091` | `BinOp (x, LstRepeat, Lit (Int i)) when Z.lt i (Z.of_int 100)` | `LstRepeat x i` with small `i` ⟶ expand to a literal list. |
| `092` | `BinOp (le, StrNth, idx)` | `s[idx]` (StrNth) ⟶ string-indexing subtree dispatch. |
| `092_1` | `true` | `s[i]` ⟶ string-index branch. |
| `092_2` | `false` | `s[i]` ⟶ string-index branch. |
| `092_3` | `Lit (Num _)` | `s[num]` ⟶ string-index branch. |
| `092_4` | `_` ⟶ `BinOp (fle, StrNth, fidx)` | `s[idx]` general ⟶ kept (operands reduced). |
| `093` | `BinOp (Lit (Int z), ILessThanEqual, UnOp (LstLen, _))` ⟶ `Expr.true_` | `n <=i len(l)` for small `n` already known ⟶ `true`. |
| `094` | `PFS.mem pfs (BinOp (e2, FLessThan, e1))` ⟶ `Expr.false_` | `a <f b` known false from PFS ⟶ `false`. |
| `095` | `PFS.mem pfs (BinOp (e2, ILessThan, e1))` ⟶ `Expr.false_` | `a <i b` known false from PFS ⟶ `false`. |
| `096` | `BinOp (e1, FLessThanEqual, e2)` ⟶ `Expr.false_` | `a <=f b` decided ⟶ `false`. |
| `097` | `BinOp (e1, ILessThanEqual, e2)` ⟶ `Expr.false_` | `a <=i b` decided ⟶ `false`. |
| `098` | `BinOp (e1, FLessThanEqual, e2)` ⟶ `Expr.true_` | `a <=f b` decided ⟶ `true`. |
| `099` | `BinOp (e1, ILessThanEqual, e2)` ⟶ `Expr.true_` | `a <=i b` decided ⟶ `true`. |
| `100` | `BinOp (e1, ((FLessThanEqual \| ILessThanEqual) as op), e2)` ⟶ `BinOp (e1, Equal, e2)` | `a <= b` with both bounds known equal ⟶ `a = b`. |
| `101` | `BinOp (_, SetMem, NOp ((SetUnion \| SetInter), []))` | `_ ∈ (∪/∩ of empty)` ⟶ simplified. |
| `102` | `BinOp (leb, SetMem, NOp (((SetUnion \| SetInter) as op), le :: lle))` | `x ∈ (s1 ∪/∩ s2 ...)` ⟶ distribute membership. |
| `103` | `BinOp (leb, SetMem, BinOp (lel, SetDiff, ler))` | `x ∈ (a ∖ b)` ⟶ `x ∈ a ∧ x ∉ b`. |
| `104` | `BinOp (leb, SetMem, ESet les)` | `x ∈ {…}` (ESet) ⟶ disjunction of equalities. |
| `105` | `BinOp (lel, op, ler)` | `BinOp(l, op, r)` — binary-operator subtree dispatch. |
| `105_1` | `ReductionException _ when op = Or \|\| op = And` | Reduction exception under `∧`/`∨` ⟶ handled. |
| `105_2` | `exn` ⟶ `raise exn` | Re-raise reduction exception. |
| `105_3` | `(Lit _ as ll), (Lit _ as lr)` | Both sides literal ⟶ concretely evaluate. |
| `105_4` | `CExprEval.TypeError err_msg` | Concrete eval type error. |
| `105_5` | `CExprEval.EvaluationError err_msg` | Concrete eval error. |
| `105_6` | `e` ⟶ `raise e` | Other eval exception ⟶ re-raise. |
| `105_7` | `_` ⟶ `None` | Concrete eval gave nothing ⟶ none. |
| `105_8` | `Equal when Expr.equal flel fler` | `Equal` with structurally equal sides ⟶ `true`. |
| `105_9` | `Equal` | `Equal` — equality subtree dispatch. |
| `105_9_1` | `Some t1, Some t2 when t1 <> t2` ⟶ `Some Expr.false_` | Equality of differently-typed sides ⟶ `false`. |
| `105_9_2` | `_, _` ⟶ `None` | Equality types undecidable ⟶ none. |
| `105_9_3` | `EList [], x \| x, EList [] \| Lit (LList []), x \| x, Lit (LList [])` | `[] = x` / `x = []` ⟶ empty-list equality. |
| `105_9_3_1` | `Lit (LList (_ :: _)) \| EList (_ :: _)` ⟶ `Expr.false_` | `[] = (non-empty list)` ⟶ `false`. |
| `105_9_3_2` | `_` ⟶ `Expr.false_` | empty vs non-empty ⟶ `false`. |
| `105_9_3_3` | `_` ⟶ `def` | empty-equality fallthrough ⟶ default. |
| `105_9_4` | `Lit (Bool true), LVar _ \| LVar _, Lit (Bool true)` | `true = lvar` / `lvar = true` ⟶ simplified. |
| `105_9_5` | `Lit (Bool true), _ when t2 = Some Type.BooleanType` ⟶ `fler` | `true = e` with `e : Bool` ⟶ `e`. |
| `105_9_6` | `_, Lit (Bool true) when t1 = Some Type.BooleanType` ⟶ `flel` | `e = true` with `e : Bool` ⟶ `e`. |
| `105_9_7` | `UnOp (Not, (BinOp (_, Equal, _) as e)), Lit (Bool b)` | `¬(a = b) = bool` ⟶ simplified. |
| `105_9_8` | `_` | Equality of concats ⟶ head/tail analysis. |
| `105_9_8_1` | `Some (hl1, tl1), Some (hl2, tl2), _, _` | Both concats decompose ⟶ compare heads and tails. |
| `105_9_8_2` | `None, Some _, (Lit (LList _) \| EList _), _` ⟶ `Expr.false_` | One side empty-headed vs literal ⟶ `false`. |
| `105_9_8_3` | `Some _, None, _, (Lit (LList _) \| EList _)` ⟶ `Expr.false_` | One side empty-headed vs literal ⟶ `false`. |
| `105_9_8_4` | `_` ⟶ `def` | Concat-equality fallthrough ⟶ default. |
| `105_9_9` | `_, _ when is_type Type.NumberType t1 && is_type Type.NumberType t2` | Equality of two numbers ⟶ numeric equality. |
| `105_9_10` | `le1, le2 when is_type Type.IntType t1 && is_type Type.IntType t2` | Equality of two ints ⟶ integer equality. |
| `105_9_11` | `_, _` ⟶ `def` | Equality fallthrough ⟶ default. |
| `105_10` | `(FPlus \| FMinus) when lexpr_is_number ~gamma def` | `+. / -.` on numbers ⟶ `simplify_num_arithmetic_lexpr`. |
| `105_11` | `(IPlus \| IMinus) when lexpr_is_int ~gamma def` | `+ / -` on ints ⟶ `simplify_int_arithmetic_lexpr`. |
| `105_12` | `FTimes when lexpr_is_number ~gamma def` | `*.` on numbers ⟶ float-product subtree. |
| `105_12_1` | `Lit (Num 1.), x \| x, Lit (Num 1.)` ⟶ `x` | `1. * x` / `x * 1.` ⟶ `x`. |
| `105_12_2` | `Lit (Num x), _ when x == nan` ⟶ `Lit (Num nan)` | `nan * _` ⟶ `nan`. |
| `105_12_3` | `_, Lit (Num x) when x == nan` ⟶ `Lit (Num nan)` | `_ * nan` ⟶ `nan`. |
| `105_12_4` | `Lit (Num z), BinOp (Lit (Num x), FTimes, y)` ⟶ `BinOp (Lit (Num (z *. x)), FTimes, y)` | `z * (x * y)` ⟶ fold the constant: `(z*x) * y`. |
| `105_12_5` | `_, _` ⟶ `def` | Float-product fallthrough ⟶ default. |
| `105_13` | `ITimes when lexpr_is_int ~gamma def` | `*` on ints ⟶ integer-product subtree. |
| `105_13_1` | `Lit (Int z), x when Z.equal z Z.one` ⟶ `x` | `1 * x` ⟶ `x`. |
| `105_13_2` | `x, Lit (Int z) when Z.equal z Z.one` ⟶ `x` | `x * 1` ⟶ `x`. |
| `105_13_3` | `(Lit (Int z) as zero), _ when Z.equal z Z.zero` ⟶ `zero` | `0 * _` ⟶ `0`. |
| `105_13_4` | `_, (Lit (Int z) as zero) when Z.equal z Z.zero` ⟶ `zero` | `_ * 0` ⟶ `0`. |
| `105_13_5` | `Lit (Int z), BinOp (Lit (Int x), ITimes, y)` ⟶ `BinOp (Lit (Int (Z.mul z x)), ITimes, y)` | `z * (x * y)` ⟶ fold the constant: `(z*x) * y`. |
| `105_13_6` | `_, _` ⟶ `def` | Integer-product fallthrough ⟶ default. |
| `105_14` | `FDiv when lexpr_is_number ~gamma def` | `/.` on numbers ⟶ float-division subtree. |
| `105_14_1` | `x, Lit (Num 1.)` ⟶ `x` | `x /. 1.` ⟶ `x`. |
| `105_14_2` | `_, _` ⟶ `def` | Float-division fallthrough ⟶ default. |
| `105_15` | `IDiv when lexpr_is_int ~gamma def` | `/` on ints ⟶ integer-division subtree. |
| `105_15_1` | `x, Lit (Int o) when Z.equal o Z.one` ⟶ `x` | `x / 1` ⟶ `x`. |
| `105_15_2` | `_, _` ⟶ `def` | Integer-division fallthrough ⟶ default. |
| `105_16` | `And when lexpr_is_bool gamma def` | `∧` on bools ⟶ conjunction subtree. |
| `105_16_1` | `Lit (Bool true), x \| x, Lit (Bool true)` ⟶ `x` | `true ∧ x` / `x ∧ true` ⟶ `x`. |
| `105_16_2` | `Lit (Bool false), _ \| _, Lit (Bool false)` ⟶ `Lit (Bool false)` | `false ∧ _` / `_ ∧ false` ⟶ `false`. |
| `105_16_3` | `_, _` | Conjunction fallthrough. |
| `105_17` | `Or when lexpr_is_bool gamma def` | `∨` on bools ⟶ disjunction subtree. |
| `105_17_1` | `Lit (Bool true), _ \| _, Lit (Bool true)` ⟶ `Lit (Bool true)` | `true ∨ _` / `_ ∨ true` ⟶ `true`. |
| `105_17_2` | `Lit (Bool false), x \| x, Lit (Bool false)` ⟶ `x` | `false ∨ x` / `x ∨ false` ⟶ `x`. |
| `105_17_3` | `_, _` | Disjunction fallthrough. |
| `105_18` | `StrCat when lexpr_is_string gamma def` | `StrCat` ⟶ string-concat subtree. |
| `105_18_1` | `x, Lit (String "") \| Lit (String ""), x` ⟶ `x` | `x ++ ""` / `"" ++ x` ⟶ `x`. |
| `105_18_2` | `BinOp (el, StrCat, Lit (String s1)), Lit (String s2)` ⟶ `BinOp (el, StrCat, Lit (String (s1 ^ s2)))` | `(el ++ "s1") ++ "s2"` ⟶ fold the literal: `el ++ "s1s2"`. |
| `105_18_3` | `_, _` ⟶ `def` | String-concat fallthrough ⟶ default. |
| `105_19` | `SetDiff when lexpr_is_set gamma def` | `SetDiff` ⟶ set-difference subtree. |
| `105_19_1` | `x, y when x = y` ⟶ `ESet []` | `x ∖ x` ⟶ `∅`. |
| `105_19_2` | `ESet [], _` ⟶ `ESet []` | `∅ ∖ _` ⟶ `∅`. |
| `105_19_3` | `x, ESet []` ⟶ `x` | `x ∖ ∅` ⟶ `x`. |
| `105_19_4` | `ESet left, ESet right` | `{..} ∖ {..}` (literal sets) ⟶ computed difference. |
| `105_19_5` | `ESet left, s when Expr.all_literals left` | `{..literal} ∖ s` ⟶ computed difference. |
| `105_19_6` | `ESet left, ESet right` | `{..} ∖ {..}` ⟶ computed difference. |
| `105_19_7` | `NOp (SetUnion, les), _` | `(∪ ..) ∖ _` ⟶ distribute over union. |
| `105_19_8` | `_, NOp (SetUnion, les)` | `_ ∖ (∪ ..)` ⟶ distribute over union. |
| `105_19_9` | `x, ESet [ el ]` ⟶ `x` | `x ∖ {el}` ⟶ simplified. |
| `105_19_10` | `LVar _, _` | `lvar ∖ _` ⟶ simplified. |
| `105_19_11` | `ESet les, fler when all_different pfs les` | `{..all-different} ∖ r` ⟶ simplified. |
| `105_19_12` | `_, _` ⟶ `def` | Set-difference fallthrough ⟶ default. |
| `105_20` | `SetMem when lexpr_is_bool gamma def` | `SetMem` (∈) ⟶ membership subtree. |
| `105_20_1` | `_, ESet []` ⟶ `Lit (Bool false)` | `_ ∈ ∅` ⟶ `false`. |
| `105_20_2` | `_, ESet [ x ]` ⟶ `BinOp (flel, Equal, x)` | `x ∈ {e}` ⟶ `x = e`. |
| `105_20_3` | `le, ESet les` ⟶ `(` | `x ∈ {..}` ⟶ disjunction of equalities. |
| `105_20_4` | `true` ⟶ `Lit (Bool true)` | membership decided ⟶ `true`. |
| `105_20_5` | `false` ⟶ `(` | membership branch. |
| `105_20_5_1` | `Lit _` | membership against literal element. |
| `105_20_5_2` | `_` ⟶ `def` | membership fallthrough ⟶ default. |
| `105_20_6` | `_, _` ⟶ `def` | Membership fallthrough ⟶ default (formerly a duplicated `105_20_4`). |
| `105_21` | `SetSub when lexpr_is_bool gamma def` | `SetSub` (⊆) ⟶ subset subtree. |
| `105_21_1` | `ESet [], _` ⟶ `Lit (Bool true)` | `∅ ⊆ _` ⟶ `true`. |
| `105_21_2` | `_, ESet []` ⟶ `Lit (Bool false)` | `_ ⊆ ∅` ⟶ `false`. |
| `105_21_3` | `ESet left, ESet right` | `{..} ⊆ {..}` ⟶ computed subset. |
| `105_21_4` | `LVar _, NOp (SetUnion, les)` | `lvar ⊆ (∪ ..)` ⟶ simplified. |
| `105_21_5` | `_, _` ⟶ `def` | Subset fallthrough ⟶ default. |
| `105_22` | `FLessThan` | `<f` (float less-than) ⟶ canonical-cut comparison. |
| `105_23` | `ILessThan` | `<i` (int less-than) ⟶ canonical-cut comparison. |
| `105_23_1` | `UnOp (LstLen, _)` ⟶ `true` | `len(l) <i _` special-case ⟶ `true`. |
| `105_23_2` | `_` | `<i` general cut branch. |
| `105_23_3` | `UnOp (LstLen, _), Lit (Int n) when Z.leq n Z.zero` ⟶ `Lit (Bool false)` | `len(l) <i n` with n≤0 ⟶ `false`. |
| `105_23_4` | `UnOp (LstLen, le), Lit (Int z) when Z.equal z Z.one` ⟶ `BinOp (le, Equal, EList [])` | `len(l) <i 1` ⟶ `l = []`. |
| `105_23_5` | `_` | `<i` cut fallthrough. |
| `105_24` | `FLessThanEqual` | `<=f` (float ≤) ⟶ canonical-cut comparison. |
| `105_24_1` | `Some x` ⟶ `Lit (Bool x)` | `<=f` decided by sign check ⟶ that boolean. |
| `105_24_2` | `None` ⟶ `def` | `<=f` undecided ⟶ default. |
| `105_25` | `ILessThanEqual` | `<=i` (int ≤) ⟶ canonical-cut comparison. |
| `105_25_1` | `Some x` ⟶ `Lit (Bool x)` | `<=i` decided by sign check ⟶ that boolean. |
| `105_25_2` | `None` ⟶ `def` | `<=i` undecided ⟶ default. |
| `105_26` | `_` ⟶ `def` | Binary-op fallthrough ⟶ default. |
| `106` | `ConstructorApp (n, les)` ⟶ `ConstructorApp (n, List.map f les)` | Constructor application ⟶ reduce each argument. |
| `107` | `FuncApp (n, les)` ⟶ `FuncApp (n, List.map f les)` | Logical-function application ⟶ reduce each argument. |
| `108` | `Cases (ConstructorApp (c, les), cs)` | `Cases` on a known constructor ⟶ select the matching case. |
| `108_1` | `[ (bs, e) ] when \|bs\| = \|les\|` | Unique matching case ⟶ substitute the bindings into its body and reduce. |
| `108_2` | `_` ⟶ `raise (ReductionException (le, "No case match found"))` | No (unique) matching case ⟶ error. |
| `109` | `Cases (le, cs)` | `Cases` on anything else ⟶ reduce scrutinee and case bodies. |
| `110` | `BinOp (ConstructorApp (ln, lles), Equal, ConstructorApp (rn, rles))` | `C(l…) = C'(r…)` ⟶ constructor equality. |
| `110_1` | `ln = rn && \|lles\| = \|rles\|` | Same constructor and arity ⟶ conjunction of pointwise argument equalities. |
| `110_2` | `_` ⟶ `Expr.false_` | Different constructor or arity ⟶ `false`. |
| `111` | `BinOp (ConstructorApp _, Equal, rle)` | `C(…) = e` ⟶ dispatch on the shape of `e`. |
| `111_1` | `LVar _ \| ConstructorApp _ \| FuncApp _ \| Cases _` ⟶ `le` | Rhs is opaque ⟶ unchanged. |
| `111_2` | `_` ⟶ `Expr.false_` | Rhs can never be a constructor value ⟶ `false`. |
| `112` | `LstSub (e1, Lit (Int 0), e3) when len-equality known` ⟶ `e1` | `l[0..n]` with `len(l) = n` in the PFS ⟶ `l` (formerly `012_1`). |
| `113` | `LstSub (e1, e2, e3)` | `l[a..b]` ⟶ swap `l` for a PFS-equal expression sharing variables with `b` (formerly `012_2`). |
| `114` | `UnOp (NumToInt, UnOp (IntToNum, e)) \| … \| UnOp (LstLen, LstSub (_, _, e))` ⟶ `e` | Cancelling group: `NumToInt(IntToNum e)`, `-(-e)`, `len(repeat(_, e))`, `len(l[_..e])` ⟶ `e` (formerly `014_1`). |
| `115` | `UnOp (IntToNum, UnOp (NumToInt, le)) when PFS.mem pfs (UnOp (IsInt, le))` ⟶ `le` | `IntToNum(NumToInt le)` when `le` is known integer ⟶ `le` (formerly `014_2`). |
| `116` | `UnOp (IntToNum, BinOp (le1, IPlus, le2))` | `IntToNum(a +i b)` ⟶ `IntToNum(a) +f IntToNum(b)` (formerly `014_3`). |
| `117` | `UnOp (NumToInt, BinOp (le1, FPlus, le2))` | `NumToInt(a +f b)` ⟶ `NumToInt(a) +i NumToInt(b)` (formerly `014_4`). |
| `118` | `UnOp (NumToInt, BinOp (le1, FTimes, le2))` | `NumToInt(a *f b)` ⟶ `NumToInt(a) *i NumToInt(b)` (formerly `014_5`). |
| `119` | `UnOp (IntToNum, UnOp (LstLen, x))` | `IntToNum(len x)` with a unique `NumToInt` equality in the PFS ⟶ substitute it. |
| `119_1` | `UnOp (NumToInt, e)` ⟶ `e` | The unique equality is `NumToInt(e)` ⟶ `e` (formerly `014_6`). |
| `119_2` | `_` ⟶ `raise (ReductionException (le, "Impossible"))` | Impossible shape ⟶ error (formerly `014_7`). |
| `120` | `UnOp (IsInt, UnOp (IntToNum, _))` ⟶ `Lit (Bool true)` | `IsInt(IntToNum _)` ⟶ `true` (formerly `014_8`). |
| `121` | `UnOp (IsInt, Lit (Num n))` ⟶ `Lit (Bool (Float.is_integer n))` | `IsInt(n)` on a float literal ⟶ its integer-ness (formerly `014_9`). |
| `122` | `UnOp (IsInt, BinOp (le', (FPlus \| FMinus \| FTimes), re'))` | `IsInt(a ⊕f b)` ⟶ split into `IsInt` of the operands (formerly `014_10`). |
| `123` | `BinOp (UnOp (NumToInt, x), Equal, y)` | `NumToInt(x) = y` ⟶ guard dispatch on `y`. |
| `123_1` | `UnOp (LstLen, _)` ⟶ guard `false` | `y = len(_)` ⟶ rewrite refused (formerly `068_11`). |
| `123_2` | `_` ⟶ guard `true` | Otherwise ⟶ `x = IntToNum(y)` (formerly `068_12`). |
| `124` | `BinOp (y, Equal, UnOp (NumToInt, x))` | `y = NumToInt(x)` ⟶ guard dispatch on `y` (mirror of `123`). |
| `124_1` | `UnOp (LstLen, _)` ⟶ guard `false` | `y = len(_)` ⟶ rewrite refused (formerly `068_21`). |
| `124_2` | `_` ⟶ guard `true` | Otherwise ⟶ `x = IntToNum(y)` (formerly `068_22`). |

## `simplify_int_arithmetic_lexpr` — Integer arithmetic helper
*Reduction.ml* · 6 tags

Light integer simplifications (identities, minus→plus) applied around the `Cint` canonical form.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `210` | `BinOp (l, IPlus, Lit (Int z)) when Z.equal z Z.zero` ⟶ `l` | `l + 0` ⟶ `l`. |
| `211` | `BinOp (Lit (Int z), IPlus, l) when Z.equal z Z.zero` ⟶ `l` | `0 + l` ⟶ `l`. |
| `212` | `BinOp (l, IMinus, r)` ⟶ `f (BinOp (l, IPlus, UnOp (IUnaryMinus, r)))` | `l - r` ⟶ `l + (-r)`. |
| `213` | `UnOp (IUnaryMinus, BinOp (l, IPlus, r))` ⟶ `f (BinOp (UnOp (IUnaryMinus, l), IPlus, UnOp (IUnaryMinus, r)))` | `-(l + r)` ⟶ `(-l) + (-r)`. |
| `214` | `BinOp (l, IPlus, r)` | `l + r` ⟶ combine via the `Cint` canonical form. |
| `215` | `_` ⟶ `le` | Integer-arith fallthrough ⟶ unchanged. |

## `simplify_num_arithmetic_lexpr` — Float arithmetic helper
*Reduction.ml* · 8 tags

Light float simplifications (identities, minus→plus) applied around the `Cnum` canonical form.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `310` | `BinOp (l, FPlus, Lit (Num 0.)) \| BinOp (Lit (Num 0.), FPlus, l)` ⟶ `l` | `l +. 0.` / `0. +. l` ⟶ `l`. |
| `311` | `BinOp (l, FMinus, r)` ⟶ `f (BinOp (l, FPlus, UnOp (FUnaryMinus, r)))` | `l -. r` ⟶ `l +. (-.r)`. |
| `312` | `UnOp (FUnaryMinus, e)` | Float unary minus `-.e` — dispatch (parent of `312_*`). |
| `312_1` | `BinOp (l, FPlus, r)` ⟶ `f ((-.l) +. (-.r))` | `-.(l +. r)` ⟶ `(-.l) +. (-.r)`. |
| `312_2` | `BinOp (l, FMinus, r)` ⟶ `f ((-.l) +. r)` | `-.(l -. r)` ⟶ `(-.l) +. r`. |
| `312_3` | `_` ⟶ `le` | `-.e` not distributable ⟶ unchanged. |
| `313` | `BinOp (l, FPlus, r)` | `l +. r` ⟶ combine via the `Cnum` canonical form. |
| `314` | `_` ⟶ `le` | Float-arith fallthrough ⟶ unchanged. |

## `substitute_for_specific_length` — List-length substitution
*Reduction.ml* · 3 tags

Replaces `len(x)` inside an arithmetic expression using length equalities known from the PFS.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `500` | `[]` ⟶ `le` | No length substitution found ⟶ unchanged. |
| `501` | `[ result ]` ⟶ `result` | Exactly one `len(x)` substitution found ⟶ apply it. |
| `502` | `oops` | Several candidate substitutions ⟶ ambiguous, leave unchanged. |

## `simplify_pfs_and_gamma` — PFS / gamma simplification (pre-SMT)
*Simplifications.ml* · 17 tags

The second simplification engine: rewrites the whole pure-formula set before it reaches the SMT solver — variable elimination, list-length materialisation, unit-type substitution, etc. (600-series, instrumented separately from Reduction).

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `600` | `var typed Undefined / Null / Empty / None` | Unit-type substitution — replace vars typed Undefined/Null/Empty/None with their literal. |
| `601` | `BinOp (a1, And, a2)` | `a ∧ b` in the PFS ⟶ split into two separate pure formulae. |
| `602` | `Some te1, Some te2 when te1 <> te2` | `¬(a = b)` with `a`, `b` of different types ⟶ drop (trivially true). |
| `604` | `Lit (Int nx)` | `l[i] = e` (literal i) ⟶ rewrite `l` as `prefix ++ [e] ++ rest`. |
| `605` | `BinOp (UnOp (LstLen, le), Equal, Lit (Int z)) when Z.equal z Z.zero` | `len(x) = 0` ⟶ `x = []`. |
| `605` | `BinOp (Lit (Int z), Equal, UnOp (LstLen, le)) when Z.equal z Z.zero` | `len(x) = 0` ⟶ `x = []`. |
| `606` | `BinOp (Lit (Int len), Equal, UnOp (LstLen, le))` | `len(x) = n` (n ≤ 100) ⟶ materialise `x = [v1, …, vn]` with fresh vars. |
| `607` | `BinOp (Lit (LList []), Equal, NOp (LstCat, les))` | `(concat) = []` ⟶ each part `= []`. |
| `608` | `BinOp (NOp (LstCat, lcat), Equal, NOp (LstCat, rcat))` | `(concat) = (concat)` ⟶ `understand_lstcat` structural matching. |
| `609` | `BinOp (UnOp (LstLen, x), Equal, BinOp (Lit (Int n), IPlus, LVar z))` | `len(x) = n + z` ⟶ split `x` into a length-n prefix and a remainder. |
| `610` | `BinOp (sl, Equal, LstSub (lst, start, num))` | `l[start..num] = sl` ⟶ rewrite `l` as `prefix ++ sl (++ suffix)`. |
| `612` | `UnOp (LstLen, LVar x), UnOp (LstLen, LVar y) when x <> y` | `len(x) = len(y)` ⟶ substitute one length for the other in the PFS. |
| `613` | `ALoc alocl, ALoc alocr when matching` | `aloc1 = aloc2` (matching mode) ⟶ substitute one abstract location for the other. |
| `614` | `LVar v, le \| le, LVar v` | `lvar = e` ⟶ variable elimination: substitute the lvar throughout the PFS and drop it. (The single most-fired pre-SMT simplification.) |
| `615` | `Lit (Type t), UnOp (TypeOf, LVar v)` | `typeOf(lvar) = T` ⟶ record the type in gamma and drop the formula. |
| `617` | `list-length & concat relations in the PFS` | `analyse_list_structure` — derive extra equalities from list-length / concat relations ("ULTRA LSTCAT"). |
| `620` | `var typed List` | For every list-typed var add the axiom `0 <= len(v)`. |

## `simplify_implication` — Entailment-goal simplification (pre-SMT)
*Simplifications.ml* · 1 tags

Prepares an entailment `A |- B` for the solver; tag 621 injects list-length equality axioms for concat equalities.

| Tag | Structure (trigger ⟶ result) | Meaning |
|---|---|---|
| `621` | `BinOp (NOp (LstCat, lex), Equal, NOp (LstCat, ley))` | For `(concat) = (concat)`, add the length-equality axiom `len(lhs) = len(rhs)`. |
