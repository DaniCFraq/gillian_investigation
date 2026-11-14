type ident = int

type value =
  | VInt of int
  | VList of value list
  | VOther of ident
  | VUndef

(* Operators the pass does not look at (every UnOp other than LstLen, every
   BinOp other than LstNth): only their identity is kept. *)
type unop = int
type binop = int

type expr =
  | Lit of value
  | Var of ident
  | EList of expr list
  | LstNth of expr * expr
  | LstLen of expr
  | UnOp of unop * expr
  | BinOp of binop * expr * expr

(* An interpretation: the value of each variable and the meaning of each
   opaque operator.  Every theorem below holds for all interpretations. *)
type env = {
  var : ident -> value;
  un : unop -> value -> value;
  bin : binop -> value -> value -> value;
}


(* Semantics of the expression language *)
let[@logic] rec nth_v (vs : value list) (n : int) : value =
  match vs with
  | [] -> VUndef
  | v :: tl -> if n = 0 then v else if n < 0 then VUndef else nth_v tl (n - 1)
(*@ r = nth_v vs n
      variant vs *)

let[@logic] nth_val (v : value) (i : value) : value =
  match (v, i) with
  | VList vs, VInt n -> nth_v vs n
  | _ -> VUndef

let[@logic] len_val (v : value) : value =
  match v with
  | VList vs -> VInt (List.length vs)
  | _ -> VUndef

let[@logic] rec eval (s : env) (e : expr) : value =
  match e with
  | Lit v -> v
  | Var x -> s.var x
  | EList es -> VList (eval_list s es)
  | LstNth (e1, e2) -> nth_val (eval s e1) (eval s e2)
  | LstLen e1 -> len_val (eval s e1)
  | UnOp (op, e1) -> s.un op (eval s e1)
  | BinOp (op, e1, e2) -> s.bin op (eval s e1) (eval s e2)
(*@ r = eval s e
      variant e *)

and[@logic] eval_list (s : env) (es : expr list) : value list =
  match es with
  | [] -> []
  | e :: tl -> eval s e :: eval_list s tl
(*@ r = eval_list s es
      variant es *)

(*@ lemma eval_list_length: forall s: env, es: expr list.
      List.length (eval_list s es) = List.length es *)


(* The normal form the pass aims at: no literal list, no LstLen of an
   explicit list, and no LstNth of an explicit list at an in-range literal
   index.  These are exactly the redexes of tags 401, 408_1 and 404_1. *)
let[@logic] is_list_lit (v : value) : bool =
  match v with
  | VList _ -> true
  | _ -> false

let[@logic] is_elist (e : expr) : bool =
  match e with
  | EList _ -> true
  | _ -> false

let[@logic] in_range_idx (l : expr list) (n2 : expr) : bool =
  match n2 with
  | Lit (VInt n) -> 0 <= n && n < List.length l
  | _ -> false

let[@logic] nth_redex (n1 : expr) (n2 : expr) : bool =
  match n1 with
  | EList l -> in_range_idx l n2
  | _ -> false

let[@logic] rec normal (e : expr) : bool =
  match e with
  | Lit v -> not (is_list_lit v)
  | Var _ -> true
  | EList es -> normal_list es
  | LstNth (e1, e2) -> normal e1 && normal e2 && not (nth_redex e1 e2)
  | LstLen e1 -> normal e1 && not (is_elist e1)
  | UnOp (_, e1) -> normal e1
  | BinOp (_, e1, e2) -> normal e1 && normal e2
(*@ r = normal e
      variant e *)

and[@logic] normal_list (es : expr list) : bool =
  match es with
  | [] -> true
  | e :: tl -> normal e && normal_list tl
(*@ r = normal_list es
      variant es *)

(* GOSPEL types a multi-argument constructor applied in a specification as a
   tuple, so the specifications below build LstNth through this helper. *)
let[@logic] mk_nth (n1 : expr) (n2 : expr) : expr = LstNth (n1, n2)


(* Tags 401 and 402: Expr.from_lit_list - Lifting literal lists to lists of expression *)
let[@logic] rec from_lit (v : value) : expr =
  match v with
  (* tag 401 *)
  | VList vl -> EList (map_lit vl)
  (* tag 402 *)
  | VInt n -> Lit (VInt n)
  | VOther i -> Lit (VOther i)
  | VUndef -> Lit VUndef
(*@ r = from_lit v
      variant v
      ensures forall s. eval s r = v
      ensures normal r
      ensures not (is_list_lit v) -> r = Lit v *)

and[@logic] map_lit (vl : value list) : expr list =
  match vl with
  | [] -> []
  | v :: tl -> from_lit v :: map_lit tl
(*@ r = map_lit vl
      variant vl
      ensures forall s. eval_list s r = vl
      ensures normal_list r *)

(* Tag 404_1: LstNth of an explicit list.  404_7 is its fall-back arm,
   the one Gillian takes when no reduction applies and it rebuilds the
   term as it was; it is here because the match has to be total, and
   because 404_1 only says something once that alternative is pinned.

   Deviation from Gillian: on a literal index that is out of range Gillian
   raises (tag 404_2).  A [@logic] function cannot raise, so the model
   rebuilds the term instead; the theorem is about this total extension. *)
let[@logic] rec nth_e (es : expr list) (n : int) : expr =
  match es with
  | [] -> Lit VUndef
  | e :: tl ->
      if n = 0 then e else if n < 0 then Lit VUndef else nth_e tl (n - 1)
(*@ r = nth_e es n
      variant es
      ensures forall s. eval s r = nth_v (eval_list s es) n
      ensures normal_list es -> normal r *)

let[@logic] nth_step_idx (l : expr list) (n2 : expr) : expr =
  match n2 with
  | Lit (VInt n) ->
      (* tag 404_1 when the index is in range; out of range Gillian raises
         (404_2) and the model rebuilds the term *)
      if 0 <= n && n < List.length l then nth_e l n else LstNth (EList l, n2)
  (* tag 404_7: no reduction, rebuild the term *)
  | _ -> LstNth (EList l, n2)
(*@ r = nth_step_idx l n2
      ensures forall s. eval s r = nth_val (VList (eval_list s l)) (eval s n2)
      ensures normal_list l -> normal n2 -> normal r
      ensures not (in_range_idx l n2) -> r = mk_nth (EList l) n2 *)

let[@logic] nth_step (n1 : expr) (n2 : expr) : expr =
  match n1 with
  (* tags 404_1, 404_7 *)
  | EList l -> nth_step_idx l n2
  (* tag 404_7: no reduction, rebuild the term *)
  | _ -> LstNth (n1, n2)
(*@ r = nth_step n1 n2
      ensures forall s. eval s r = nth_val (eval s n1) (eval s n2)
      ensures normal n1 -> normal n2 -> normal r
      ensures not (nth_redex n1 n2) -> r = mk_nth n1 n2 *)


(* Tag 408_1: LstLen of an explicit list, with fall-back arm 408_3. *)
let[@logic] len_step (n1 : expr) : expr =
  match n1 with
  (* tag 408_1 *)
  | EList l -> Lit (VInt (List.length l))
  (* tag 408_3: no reduction, rebuild the term *)
  | _ -> LstLen n1
(*@ r = len_step n1
      ensures forall s. eval s r = len_val (eval s n1)
      ensures normal n1 -> normal r
      ensures not (is_elist n1) -> r = LstLen n1 *)


(* The pass.  Three postconditions: it preserves the meaning under every
   interpretation, its result is in normal form, and it leaves a term that
   is already in normal form untouched. *)
let[@logic] rec normalise (e : expr) : expr =
  match e with
  (* tags 401, 402 *)
  | Lit v -> from_lit v
  (* tag 402 *)
  | Var x -> Var x
  (* tag 411 *)
  | EList es -> EList (normalise_list es)
  (* tag 404_1, with fall-back 404_7 *)
  | LstNth (e1, e2) -> nth_step (normalise e1) (normalise e2)
  (* tag 408_1, with fall-back 408_3 *)
  | LstLen e1 -> len_step (normalise e1)
  (* tag 409 *)
  | UnOp (op, e1) -> UnOp (op, normalise e1)
  (* tag 405 *)
  | BinOp (op, e1, e2) -> BinOp (op, normalise e1, normalise e2)
(*@ r = normalise e
      variant e
      ensures forall s. eval s r = eval s e
      ensures normal r
      ensures normal e -> r = e *)

and[@logic] normalise_list (es : expr list) : expr list =
  match es with
  | [] -> []
  | e :: tl -> normalise e :: normalise_list tl
(*@ r = normalise_list es
      variant es
      ensures forall s. eval_list s r = eval_list s es
      ensures normal_list r
      ensures normal_list es -> r = es *)

(*@ lemma normalise_idempotent: forall e: expr.
      normalise (normalise e) = normalise e *)
