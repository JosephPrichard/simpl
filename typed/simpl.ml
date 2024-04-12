(* Joseph Hesketh Prichard *)
(* JEH190000 *)
(* 3/13/2024 *)

open Simpltypes

type vartyp =
  | Undeclared
  | VTyp of (ityp * bool)

type typctx = varname -> vartyp

type cmdtyp =
  | TypCtx of typctx
  | CTypErr of string

type exprtyp =
  | ExpTyp of ityp
  | ETypErr of string

let update s v i x = if x = v then i else s x

let string_of_vartyp = function 
  | VTyp (TypInt, _) -> "Int"
  | VTyp (TypBool, _) -> "Bool"
  | Undeclared -> "Undeclared"

let init_typctx (l : (varname * vartyp) list) : typctx =
  let rec aux l (acc : typctx) = 
    match l with
    | (v, vtyp) :: l ->
      aux l (update acc v vtyp)
    | [] -> acc
  in
  aux l (fun _ -> Undeclared)

let error s (((l1, c1), (l2, c2)) : lineinfo) = 
  (Printf.sprintf 
    "%s between line %d, column %d and line %d, column %d" s l1 c1 l2 c2)

let binop_error op typ li = 
  ETypErr (error (Printf.sprintf "operator %s must be between two %s types" op typ) li)

let unop_error op typ li =
  ETypErr (error (Printf.sprintf "operator %s must be applied to a %s type" op typ) li)

let rec typchk_expr (tc : typctx) (e : iexpr) : exprtyp =
  match e with
  | Const (n, _) -> ExpTyp TypInt
  | Var (v, li) ->
    (match tc v with
    | Undeclared -> ETypErr (error (Printf.sprintf "variable '%s' is undeclared" v) li)
    | VTyp (ityp, init) ->
      if init then
        ExpTyp ityp
      else
        ETypErr (error (Printf.sprintf "variable '%s' is uninitialized" v) li))
  | Plus expr -> typchk_aop tc "+" expr
  | Minus expr -> typchk_aop tc "-" expr
  | Times expr -> typchk_aop tc "*" expr
  | True _ -> ExpTyp TypBool
  | False _ -> ExpTyp TypBool
  | Leq (e1, e2, li) -> 
    (match typchk_expr tc e1 , typchk_expr tc e2 with
    | (ExpTyp TypInt, ExpTyp TypInt) -> ExpTyp TypBool
    | (ExpTyp _, ExpTyp _) -> binop_error "<=" "bool" li
    | (ETypErr _ as e, _) -> e
    | (_, (ETypErr _ as e)) -> e)
  | Conj expr -> typchk_bop tc "&&" expr
  | Disj expr -> typchk_bop tc "||" expr
  | Neg (e, li) -> 
    (match typchk_expr tc e with
    | ExpTyp TypBool -> ExpTyp TypBool
    | ExpTyp TypInt -> unop_error "!" "bool" li
    | e -> e)

and typchk_aop tc name (e1, e2, li) = 
  (match typchk_expr tc e1, typchk_expr tc e2 with
  | (ExpTyp TypInt, ExpTyp TypInt) -> ExpTyp TypInt
  | (ExpTyp _, ExpTyp _) -> binop_error name "int" li
  | (ETypErr _ as e, _) -> e
  | (_, (ETypErr _ as e)) -> e)

and typchk_bop tc name (e1, e2, li) = 
  (match typchk_expr tc e1, typchk_expr tc e2 with
    | (ExpTyp TypBool, ExpTyp TypBool) -> ExpTyp TypBool
    | (ExpTyp _, ExpTyp _)-> binop_error name "bool" li
    | (ETypErr _ as e, _) -> e
    | (_, (ETypErr _ as e)) -> e)

let typchk_bool_expr tc e li f = 
  (match typchk_expr tc e with
    | ExpTyp TypBool -> f ()
    | ExpTyp _ -> CTypErr (error "cond expr must be bool" li)
    | ETypErr e -> CTypErr e)

let rec typchk_cmd (tc : typctx) (c : icmd) : cmdtyp =
  match c with
  | Skip _ -> TypCtx tc
  | Seq (c1, c2, li) ->
    (match typchk_cmd tc c1 with
    | TypCtx tc1 ->
      (match typchk_cmd tc1 c2 with
      | TypCtx _ as cmdtyp -> cmdtyp
      | e -> e)
    | e -> e)
  | Assign (v, e, li) -> 
    (match tc v with
    | Undeclared -> CTypErr (error (Printf.sprintf "assign to an undeclared variable '%s'" v) li)
    | VTyp (ityp, _) as vtyp ->
      (match (ityp, typchk_expr tc e) with
      | (TypBool, ExpTyp TypBool)
      | (TypInt, ExpTyp TypInt) -> TypCtx (update tc v (VTyp (ityp, true)))
      | (_, ETypErr e) -> CTypErr e
      | _ ->  CTypErr (error (Printf.sprintf "assignment must be same type as declaration %s" (string_of_vartyp vtyp)) li)))
  | Cond (e, c1, c2, li) ->
    typchk_bool_expr tc e li (fun _ -> 
      (* Both c1 and c2 must be well-typed, but we cannot use their type-contexts *)
      (match (typchk_cmd tc c1, typchk_cmd tc c2) with
      | (CTypErr _ as e, _) -> e
      | (TypCtx _, (CTypErr _ as e)) -> e
      | _ -> TypCtx tc))
  | While (e, c1, li) -> 
    typchk_bool_expr tc e li (fun _ -> 
      (* Both c1 well-typed, but we cannot use it's type-contexts *)
      (match (typchk_cmd tc c1) with
      | (CTypErr _ as e) -> e
      | _ -> TypCtx tc))
  | Decl (ityp, v, li) -> 
    (match tc v with
    | Undeclared ->
      let vtyp = VTyp (ityp, false) in
      TypCtx (update tc v vtyp)
    | _ ->  CTypErr (error (Printf.sprintf "redeclaring variable '%s'" v) li))

type store = varname -> int

let init_store (l : (varname * int) list) : store = fun x -> List.assoc x l

let rec eval_expr (s : store) (e : iexpr) : int =
  match e with
  | Const (n, _) -> n
  | Var (x, _) -> s x
  | Plus (e1, e2, _) | Disj (e1, e2, _) -> eval_expr s e1 + eval_expr s e2
  | Minus (e1, e2, _) -> eval_expr s e1 - eval_expr s e2
  | Times (e1, e2, _) | Conj (e1, e2, _) -> eval_expr s e1 * eval_expr s e2
  | True _ -> 1
  | False _ -> 0
  | Leq (e1, e2, _) -> if eval_expr s e1 <= eval_expr s e2 then 1 else 0
  | Neg (e1, _) -> if eval_expr s e1 = 0 then 1 else 0

let rec exec_cmd (s : store) (c : icmd) : store =
  match c with
  | Skip _ | Decl _ -> s
  | Seq (c1, c2, _) -> exec_cmd (exec_cmd s c1) c2
  | Assign (v, e, _) -> update s v (eval_expr s e)
  | Cond (e, c1, c2, _) -> exec_cmd s (if eval_expr s e = 0 then c2 else c1)
  | While (e, c1, li) -> exec_cmd s (Cond (e, Seq (c1, c, li), Skip li, li))

let extract_args f l =
  let f i a = ("arg" ^ string_of_int (i - 2), f i a) in
  List.tl (List.tl (Array.to_list (Array.mapi f l)))

let main () =
  let argval = function
    | "true" -> 1
    | "false" -> 0
    | x -> int_of_string x
  in
  let argtyp = function
    | "true" | "false" -> TypBool
    | _ -> TypInt
  in
  let c =
    Simplparser.parse_cmd
      Simpllexer.token
      (Lexing.from_channel (open_in Sys.argv.(1)))
  in
  let s =
    init_store
      (extract_args (fun i a -> if i >= 2 then argval a else 0) Sys.argv)
  in
  let tc =
    init_typctx (extract_args (fun i a -> VTyp (argtyp a, true)) Sys.argv)
  in
  match typchk_cmd tc c with
  | CTypErr s -> print_string ("Typing error: " ^ s ^ "\n")
  | TypCtx tc' ->
    print_string
      (match tc' "ret" with
      | Undeclared -> "Typing error: return value undeclared"
      | VTyp (_, false) -> "Typing error: return value uninitialized"
      | VTyp (rtyp, true) ->
        let n = exec_cmd s c "ret" in
        if rtyp = TypInt then
          string_of_int n
        else if n = 0 then
          "false"
        else
          "true");
    print_newline ()
;;

main ()