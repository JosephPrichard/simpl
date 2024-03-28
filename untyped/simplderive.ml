(* Joseph Hesketh Prichard - JEH190000*)
open Simpltypes
open Simplstore

type configuration =
  | ArithConf of (iarith * lstore)
  | BoolConf of (ibool * lstore)
  | CmdConf of (icmd * lstore)

type converge = 
  | ConvArith of int
  | ConvBool of bool
  | ConvCmd of lstore

type 'conv judgement = (configuration * 'conv)

(* Monad. *)
module Derivation = struct
  type 'conv t = 
    | Axiom of 'conv judgement
    | Rule of (converge t list * 'conv judgement)

  let bind rule f =
    match rule with
    | Axiom (conf, conv) -> Axiom (conf, f conv)
    | Rule (hypo, (conf, conv)) -> Rule (hypo, (conf, f conv))

  let bind_arith rule = bind rule (fun x -> ConvArith x)
  let bind_bool rule = bind rule (fun x -> ConvBool x)
  let bind_cmd rule = bind rule (fun x -> ConvCmd x)

  let ( >>= ) = bind

  let map rules f = List.map (fun rule -> bind rule f) rules
  let map_arith rules = map rules (fun x -> ConvArith x)
  let map_bool rules = map rules (fun x -> ConvBool x)
  let map_cmd rules = map rules (fun x -> ConvCmd x)
end

let update f v y = 
  (fun n ->
     if n = v then y
     else f n)

let rec init_store_f (l : (string * int) list) : string -> int =
  match l with
  | [] -> fun _ -> 0
  | h :: l ->
    let v, x = h in
    update (init_store_f l) v x

let converge_of = function
  | Derivation.Axiom (_, conv) -> conv
  | Rule (_, ( _, conv)) -> conv

let lstep_binop op d1 d2 f conclusion =
  let n = ( op ) (converge_of d1) (converge_of d2) in
  let dlist = Derivation.map [d1; d2] f in
  Derivation.Rule (dlist, (conclusion, n))

let rec lstep_arith (a : iarith) (s : lstore) =
  let conc = ArithConf (a, s) in
  let _, _, f = s in
  match a with 
  | Const x -> Derivation.Axiom (conc, x)
  | Var v -> Axiom (conc, f v)
  | Plus (a1, a2) ->
    lstep_arithop ( + ) a1 a2 s conc
  | Minus (a1, a2) -> 
    lstep_arithop ( - ) a1 a2 s conc
  | Times (a1, a2) -> 
    lstep_arithop ( * ) a1 a2 s conc

and lstep_arithop (op : int -> int -> int) a1 a2 s conc =
  let d1 = lstep_arith a1 s in 
  let d2 = lstep_arith a2 s in 
  lstep_binop op d1 d2 (fun x -> ConvArith x) conc

let rec lstep_bool (b : ibool) (s : lstore) =
  let conc = BoolConf (b, s) in
  match b with
  | True -> Derivation.Axiom (conc, true)
  | False -> Axiom (conc, false)
  | Leq (a1, a2) ->
    lstep_compop ( <= ) a1 a2 s conc
  | Conj (b1, b2) ->
    lstep_boolop ( && ) b1 b2 s conc
  | Disj (b1, b2) -> 
    lstep_boolop ( || ) b1 b2 s conc
  | Neg b -> 
    let d = lstep_bool b s in
    let v = not (converge_of d) in
    Rule (Derivation.map_bool [d], (conc, v))

and lstep_compop (op : int -> int -> bool) a1 a2 s conc = 
  let d1 = lstep_arith a1 s in 
  let d2 = lstep_arith a2 s in 
  lstep_binop op d1 d2 (fun x -> ConvArith x) conc

and lstep_boolop (op : bool -> bool -> bool) b1 b2 s conc = 
  let d1 = lstep_bool b1 s in 
  let d2 = lstep_bool b2 s in 
  lstep_binop op d1 d2 (fun x -> ConvBool x) conc

let rec lstep_cmd (c : icmd) (s : lstore) =
  let conc = CmdConf (c, s) in
  match c with 
  | Skip -> Derivation.Axiom (conc, s)
  | Seq (c1, c2) ->
    let d1 = lstep_cmd c1 s in
    let d2 = lstep_cmd c2 (converge_of d1) in
    let s2 = converge_of d2 in
    Rule (Derivation.map_cmd [d1; d2], (conc, s2))
  | Assign (v, a) ->
    let d = lstep_arith a s in
    let n = (converge_of d) in

    (* Creates a new store linked to the previous one, set with the new binding *)
    let i, _, f = s in
    let s1 = (i + 1, Some (v, n) , update f v n) in

    Rule (Derivation.map_arith [d], (conc, s1))
  | Cond (b, c1, c2) ->
    let d1 = lstep_bool b s in
    let c = if (converge_of d1) then c1 else c2 in
    let d2 = lstep_cmd c s in
    Rule ([Derivation.bind_bool d1; Derivation.bind_cmd d2], (conc, (converge_of d2)))
  | While (b, c1) as c' ->
    lstep_cmd (Cond (b, Seq (c1, c'), Skip)) s

let rec string_of_iarith (a : iarith) =
  match a with 
  | Const x -> string_of_int x
  | Var v -> v
  | Plus (a1, a2) -> string_of_arithop " + " a1 a2
  | Minus (a1, a2) -> string_of_arithop " - " a1 a2
  | Times (a1, a2) -> string_of_arithop " * " a1 a2

and string_of_arithop op a1 a2 =
  Printf.sprintf "(%s%s%s)" (string_of_iarith a1) op (string_of_iarith a2)

let rec string_of_ibool (b : ibool) =
  match b with
  | True -> "true"
  | False -> "false"
  | Leq (a1, a2) -> string_of_arithop " <= " a1 a2
  | Conj (b1, b2) -> string_of_boolop " && " b1 b2
  | Disj (b1, b2) -> string_of_boolop " || " b1 b2
  | Neg b -> Printf.sprintf "(!%s)" (string_of_ibool b)

and string_of_boolop op b1 b2 =
  Printf.sprintf "(%s%s%s)" (string_of_ibool b1) op (string_of_ibool b2)

let rec string_of_icmd (c : icmd) = 
  match c with 
  | Skip -> "Skip"
  | Seq (c1, c2) -> Printf.sprintf "%s; %s" (string_of_icmd c1) (string_of_icmd c2)
  | Assign (v, a) -> Printf.sprintf "%s := %s" v (string_of_iarith a)
  | Cond (b, c1, c2) -> Printf.sprintf "if %s then (%s) else (%s)" (string_of_ibool b) (string_of_icmd c1) (string_of_icmd c2)
  | While (b, c1) -> Printf.sprintf "while %s do (%s)" (string_of_ibool b) (string_of_icmd c1)

(* This version of string_of_store will stringify it with the generation lbl without the mapping*)
let string_of_store i = "\u{03C3}" ^ string_of_int i

(* This version of string_of_store will stringify it as the previous store's lbl + the mapping added in this one *)
let string_of_store' (s : lstore) =
  let i, pair, _ = s in
  match pair with
  | None -> string_of_store i
  | Some (v, n) -> Printf.sprintf "%s[%s->%d]" (string_of_store (i - 1)) v n

let string_of_conf (conf : configuration) =
  let string_of_conf ast (i, _, _) = Printf.sprintf "<%s, %s>" ast (string_of_store i) in
  match conf with
  | ArithConf (a, s) -> string_of_conf (string_of_iarith a) s
  | BoolConf (b, s) -> string_of_conf (string_of_ibool b) s
  | CmdConf (c, s) -> string_of_conf (string_of_icmd c) s

let string_of_judge (j : converge judgement) =
  let string_of_judge conf conv = Printf.sprintf "%s \u{21D3} %s" (string_of_conf conf) conv in
  match j with
  | (conf, ConvArith n) -> string_of_judge conf (string_of_int n)
  | (conf, ConvBool b) -> string_of_judge conf (string_of_bool b)
  | (conf, ConvCmd s) -> string_of_judge conf (string_of_store' s)

module Tree = struct 
  module TreeMap = Map.Make(Int)

  type 'a t = 'a list TreeMap.t

  let empty = TreeMap.empty

  let find_level depth (tree : 'a t) = 
    match TreeMap.find_opt depth tree with
    | Some level -> level
    | None -> []

  let pairs (tree : 'a t) = 
    TreeMap.fold 
      (fun key values acc -> (key, values) :: acc)
      tree
      []

  let add x depth (tree : 'a t) : 'a t = TreeMap.add depth (x :: (find_level depth tree)) tree
end

let rec stringtree_of_lstep (d : converge Derivation.t) =
  let rec loop d depth tree =
    match d with
    | Derivation.Axiom j ->
      Tree.add (string_of_judge j) depth tree
    | Rule (rules, j) ->
      let tree' = Tree.add (string_of_judge j) depth tree in
      List.fold_left 
        (fun tree' d -> loop d (depth + 1) tree')
        tree'
        rules
  in
  loop d 0 Tree.empty

let rec ( ^* ) s n =
  match n with
  | 0 -> ""
  | n' -> s ^ (s ^* (n' - 1))

let rec string_of_stringtree stree =
  let pairs = Tree.pairs stree in
  List.fold_left
    (fun acc (key, values) ->
      let vstr = 
        List.fold_left 
          (fun x acc -> acc ^ (" " ^* 2) ^ x) 
          "" 
          values 
      in
      acc ^ vstr ^ "\n\n")
    ""
    pairs

let main () =
  match (Array.to_list Sys.argv) with
  | [] -> raise (Sys_error "invalid argument list")
  | [_] -> raise (Failure "please specify a program to interpret")
  | _ :: prog :: args ->
    (* Lex then parse entire program into a command *)
    let c = Simplparser.parse_cmd Simpllexer.token (Lexing.from_channel (open_in prog)) in

    let pairs = arg_pairs args in

    (* Stringify the ast also *)
    Printf.printf "%s\n\n" (string_of_icmd c);

    (* Get the derivation *)
    let s_in = (0, None, init_store_f pairs) in
    let d = lstep_cmd c s_in in
    let (_, _, f) = (converge_of d) in
    let ret = f "ret" in

    (* Convert it to a string *)
    let stree = stringtree_of_lstep (Derivation.bind_cmd d) in
    Printf.printf "%s" (string_of_stringtree stree);

    Printf.printf "Ret: %d\n" ret
  ;;

main ();