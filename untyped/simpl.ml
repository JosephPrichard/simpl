(* Joseph Hesketh Prichard - JEH190000*)
open Simpltypes
open Simplstore

let rec eval_arith (s : store) (a : iarith) : int =
  match a with
  | Const x -> x
  | Var v -> s v
  | Plus (a1, a2) ->
    let n1 = eval_arith s a1 in
    let n2 = eval_arith s a2 in
    n1 + n2
  | Minus (a1, a2) ->
    let n1 = eval_arith s a1 in
    let n2 = eval_arith s a2 in
    n1 - n2
  | Times (a1, a2) ->
    let n1 = eval_arith s a1 in
    let n2 = eval_arith s a2 in
    n1 * n2

let rec eval_bool (s : store) (b : ibool) : bool =
  match b with
  | True -> true
  | False -> false
  | Leq (a1, a2) ->
    let n1 = eval_arith s a1 in
    let n2 = eval_arith s a2 in
    n1 <= n2 
  | Conj (b1, b2) ->
    let p = eval_bool s b1 in
    let q = eval_bool s b2 in
    p && q
  | Disj  (b1, b2) ->
    let p = eval_bool s b1 in
    let q = eval_bool s b2 in
    p || q
  | Neg b ->
    let p = eval_bool s b in
    not p
  
let rec exec_cmd (s : store) (c : icmd) : store =
  match c with
  | Skip -> s
  | Seq (c1, c2) -> 
    let s = exec_cmd s c1 in
    exec_cmd s c2
  | Assign (v, a) ->
    let n = eval_arith s a in
    update s v n
  | Cond (b, c1, c2) ->
    if eval_bool s b 
    then exec_cmd s c1 
    else exec_cmd s c2
  | While (b, c) ->
    if eval_bool s b
    then exec_cmd (exec_cmd s c) (While (b, c))
    else exec_cmd s Skip

let main () =
  match (Array.to_list Sys.argv) with
  | [] -> raise (Sys_error "invalid argument list")
  | [_] -> raise (Failure "please specify a program to interpret")
  | _ :: prog :: args ->
    (* Lex then parse entire program into a command *)
    let c = Simplparser.parse_cmd Simpllexer.token (Lexing.from_channel (open_in prog)) in
    
    (* Get the argument pairs from program args *)
    let pairs = arg_pairs args in

    (* Execution of the program is the root command called on the initial store resulting in a new store*)
    let s_in = init_store pairs in
    let s_out = exec_cmd s_in c in
    let ret = s_out "ret" in

    print_string (string_of_int ret);
    print_newline () ;;

main ();