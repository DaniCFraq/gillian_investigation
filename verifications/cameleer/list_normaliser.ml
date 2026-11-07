type ident = int
type value = 
  | VInt of int
  | VList of value list
  | VOther of ident
  | VUndef

type expr =
  | Lit of value
  | Var of ident
  | EList of expr list
  | LstNth of expr * expr
  | LstLen of expr
  | Plus of expr * expr

type store = ident -> value


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

let plus_val (v1 : value) (v2 : value) : value =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a + b)
  | _ -> VUndef

let[@logic] rec eval (s : store) (e : expr) : value =
  match e with
  | Lit v -> v
  | Var x -> s x
  | EList es -> VList (eval_list s es)
  | LstNth (e1, e2) -> nth_val (eval s e1) (eval s e2)
  | LstLen e1 -> len_val (eval s e1)
  | Plus (e1, e2) -> plus_val (eval s e1) (eval s e2)
(*@ r = eval s e
      variant e *)

and[@logic] eval_list (s : store) (es : expr list) : value list =
  match es with
  | [] -> []
  | e :: tl -> eval s e :: eval_list s tl
(*@ r = eval_list s es
      variant es *)

(*@ lemma eval_list_length: forall s: store, es: expr list.
      List.length (eval_list s es) = List.length es *)


(* The normal form the pass aims at: no literal list anywhere *)
let is_list_lit (v : value) : bool =
  match v with
  | VList _ -> true
  | _ -> false

let[@logic] rec no_lit_list (e : expr) : bool =
  match e with
  | Lit v -> not (is_list_lit v)
  | Var _ -> true
  | EList es -> no_lit_list_list es
  | LstNth (e1, e2) -> no_lit_list e1 && no_lit_list e2
  | LstLen e1 -> no_lit_list e1
  | Plus (e1, e2) -> no_lit_list e1 && no_lit_list e2
(*@ r = no_lit_list e
      variant e *)

and[@logic] no_lit_list_list (es : expr list) : bool =
  match es with
  | [] -> true
  | e :: tl -> no_lit_list e && no_lit_list_list tl
(*@ r = no_lit_list_list es
      variant es *)


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
      ensures no_lit_list r *)

and[@logic] map_lit (vl : value list) : expr list =
  match vl with
  | [] -> []
  | v :: tl -> from_lit v :: map_lit tl
(*@ r = map_lit vl
      variant vl
      ensures forall s. eval_list s r = vl
      ensures no_lit_list_list r *)

(* Tag 404_1: LstNth of an explicit list.  404_7 is its fall-back arm,
   the one Gillian takes when no reduction applies and it rebuilds the
   term as it was; it is here because the match has to be total, and
   because 404_1 only says something once that alternative is pinned. *)
let[@logic] rec nth_e (es : expr list) (n : int) : expr =
  match es with
  | [] -> Lit VUndef
  | e :: tl ->
      if n = 0 then e else if n < 0 then Lit VUndef else nth_e tl (n - 1)
(*@ r = nth_e es n
      variant es
      ensures forall s.
                0 <= n < List.length es ->
                eval s r = nth_v (eval_list s es) n
      ensures no_lit_list_list es -> no_lit_list r *)

let[@logic] nth_step_idx (l : expr list) (n2 : expr) : expr =
  match n2 with
  | Lit (VInt n) ->
      (* tag 404_1 when the index is in range, 404_7 when it is not *)
      if 0 <= n && n < List.length l then nth_e l n else LstNth (EList l, n2)
  (* tag 404_7: no reduction, rebuild the term *)
  | _ -> LstNth (EList l, n2)
(*@ r = nth_step_idx l n2
      ensures forall s. eval s r = nth_val (VList (eval_list s l)) (eval s n2)
      ensures no_lit_list_list l -> no_lit_list n2 -> no_lit_list r *)

let[@logic] nth_step (n1 : expr) (n2 : expr) : expr =
  match n1 with
  (* tags 404_1, 404_7 *)
  | EList l -> nth_step_idx l n2
  (* tag 404_7: no reduction, rebuild the term *)
  | _ -> LstNth (n1, n2)
(*@ r = nth_step n1 n2
      ensures forall s. eval s r = nth_val (eval s n1) (eval s n2)
      ensures no_lit_list n1 -> no_lit_list n2 -> no_lit_list r *)


(* Tag 408_1: LstLen of an explicit list, with fall-back arm 408_3. *)
let[@logic] len_step (n1 : expr) : expr =
  match n1 with
  (* tag 408_1 *)
  | EList l -> Lit (VInt (List.length l))
  (* tag 408_3: no reduction, rebuild the term *)
  | _ -> LstLen n1
(*@ r = len_step n1
      ensures forall s. eval s r = len_val (eval s n1)
      ensures no_lit_list n1 -> no_lit_list r *)


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
  (* tag 405 *)
  | Plus (e1, e2) -> Plus (normalise e1, normalise e2)
(*@ r = normalise e
      variant e
      ensures forall s. eval s r = eval s e
      ensures no_lit_list r *)

and[@logic] normalise_list (es : expr list) : expr list =
  match es with
  | [] -> []
  | e :: tl -> normalise e :: normalise_list tl
(*@ r = normalise_list es
      variant es
      ensures forall s. eval_list s r = eval_list s es
      ensures no_lit_list_list r *)
