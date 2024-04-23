(* Joseph Hesketh Prichard *)
(* JEH190000 *)
(* 4/11/2024 *)

open Simpltypes

type vartyp =
  | Undeclared
  | VTyp of (ityp * bool)

type typctx = varname -> vartyp

(* These are actually a special name-aliased versions of the result type, I will convert to result when needed... *)
type cmdtyp =
  | TypCtx of typctx
  | CTypErr of string

type exprtyp =
  | ExpTyp of ityp
  | ETypErr of string

let update s v i x = if x = v then i else s x

let init_typctx (l : (varname * vartyp) list) : typctx =
 fun x ->
  try List.assoc x l with
  | Not_found -> Undeclared

let rec string_of_itypl acc l =
  match l with
  | [typ] ->
    (Printf.sprintf 
      "%s%s" 
      acc 
      (string_of_ityp typ))
  | typ :: l ->
    string_of_itypl
      (Printf.sprintf 
        "%s%s->" 
        acc 
        (string_of_ityp typ))
      l
  | [] -> acc

and string_of_ityp = function
  | TypInt -> "Int"
  | TypBool -> "Bool"
  | TypFunc (args, ret) -> 
    Printf.sprintf "fun(%s->%s)" 
      (string_of_itypl "" args)
      (string_of_ityp ret)

let rec string_of_vartyp = function 
  | VTyp (ityp, _) -> string_of_ityp ityp
  | Undeclared -> "Undeclared"

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
  | Abstraction (args, body, li) ->
    let args_typ = 
      List.map (fun (vn, ityp, _) -> ityp) args 
    in
    let args_tc = 
      List.fold_left 
        (* Parameters are always typed and initialized *)
        (fun tc (vn, ityp, _) -> update tc vn (VTyp (ityp, true)))
        tc args
    in
    (match typchk_cmd args_tc body with
    | TypCtx tc -> 
      (match tc "ret" with
      | VTyp (ret_typ, true) -> ExpTyp (TypFunc (args_typ, ret_typ))
      | VTyp (ret_typ, false) ->
        let _ = print_endline "warn: ret variable is declared in function but never initialized" in
        ExpTyp (TypFunc (args_typ, ret_typ))
      | Undeclared -> 
        ETypErr (error "cannot check type: ret variable is undeclared in the function" li))
    | CTypErr e -> ETypErr e)
  | Apply (func, args, li) ->
    (match typchk_expr tc func with
    | ExpTyp (TypFunc (params_typ, ret_typ)) ->
      typchk_arg_params 
        (typchk_arg_list tc args) 
        params_typ 
        ret_typ 
        li
    | ExpTyp ityp ->
      let m = Printf.sprintf "lhs of an application must be a function, got %s" (string_of_ityp ityp) in
      ETypErr (error m li)
    | ETypErr e -> ETypErr e)

and typchk_ret cmdtyp params_typ li =
  match cmdtyp  with
  | TypCtx tc -> 
    (match tc "ret" with
    | VTyp (ret_typ, init) -> 
      ExpTyp (TypFunc (params_typ, ret_typ))
    | Undeclared -> 
      ETypErr (error "cannot check type: ret variable is undeclared in the function" li) )
  | CTypErr e -> ETypErr e

and typchk_arg_params args_result params_typ ret_typ li = 
  match args_result with
  | Ok args_typ -> 
    if args_typ = params_typ then
      ExpTyp ret_typ
    else
      let m = 
        Printf.sprintf 
          "arguments and parameters differ, argument types: %s, parameter types: %s" 
          (string_of_itypl "" args_typ) 
          (string_of_itypl "" params_typ) 
      in
      ETypErr (error m li)
  | Error e -> ETypErr e

and typchk_arg_list tc l =
  let result = 
    List.fold_left
      (fun acc exptyp -> 
        match acc with 
        | Ok acc -> 
          (match typchk_expr tc exptyp with 
          | ETypErr e -> Error e
          | ExpTyp typ -> Ok (typ :: acc))
        | Error e -> Error e)
    (Ok []) l
  in
  match result with 
  | Ok l -> Ok (List.rev l)
  | Error e -> Error e 

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

and typchk_bool_expr tc e li f = 
  (match typchk_expr tc e with
    | ExpTyp TypBool -> f ()
    | ExpTyp _ -> CTypErr (error "cond expr must be bool" li)
    | ETypErr e -> CTypErr e)

and typchk_cmd (tc : typctx) (c : icmd) : cmdtyp =
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
      let assign_typ = typchk_expr tc e in
      (match (ityp, assign_typ) with
      | (TypBool, ExpTyp TypBool)
      | (TypInt, ExpTyp TypInt) -> TypCtx (update tc v (VTyp (ityp, true)))
      | (TypFunc lhs_typ, ExpTyp TypFunc rhs_typ) -> 
        if lhs_typ = rhs_typ then
          TypCtx (update tc v (VTyp (ityp, true)))
        else
          let m = (Printf.sprintf "assignment must be same function type signature as declaration %s" (string_of_vartyp vtyp)) in
          CTypErr (error m li)
      | (_, ETypErr e) -> CTypErr e
      | _ -> 
        let m = (Printf.sprintf "assignment must be same type as declaration %s" (string_of_vartyp vtyp)) in
        CTypErr (error m li)))
  | Cond (e, c1, c2, li) ->
    typchk_bool_expr tc e li (fun _ -> 
      (* Both c1 and c2 must be well-typed, but we cannot use their type-contexts *)
      (match (typchk_cmd tc c1, typchk_cmd tc c2) with
      | (CTypErr _ as e, _) -> e
      | (TypCtx _, (CTypErr _ as e)) -> e
      | (TypCtx _, TypCtx _) -> TypCtx tc))
  | While (e, c1, li) -> 
    typchk_bool_expr tc e li (fun _ -> 
      (* c1 is well-typed, but we cannot use it's type-contexts *)
      (match (typchk_cmd tc c1) with
      | (CTypErr _ as e) -> e
      | TypCtx _ -> TypCtx tc))
  | Decl (ityp, v, li) ->
    (match tc v with
    | Undeclared ->
      let vtyp = VTyp (ityp, false) in
      TypCtx (update tc v vtyp)
    | VTyp _ ->  CTypErr (error (Printf.sprintf "redeclaring variable '%s'" v) li))

(* I've added an error message to our segmentation fault error so we don't make the same mistakes C and C++ do! *)
exception SegFault of string

type heapval =
  | Data of int
  | Code of (varname list * icmd)

type store = varname -> heapval

let init_store (l : (varname * heapval) list) : store = 
  fun x -> 
    match List.assoc_opt x l with
    | Some v -> v
    | None -> raise (SegFault (Printf.sprintf "cannot find variable '%s' in the store" x))

let rec eval_expr (s : store) (e : iexpr) : heapval =
  let eval_intop f (e1, e2, li) =
    match (eval_expr s e1, eval_expr s e2) with
    | Data n1, Data n2 -> Data (f n1 n2)
    | _ -> raise (SegFault (error "intop can only be applied to two data types" li))
  in

  let eval_boolop f =
    eval_intop (fun x y -> if f (x <> 0) (y <> 0) then 1 else 0)
  in

  match e with
  | Const (n, _) -> Data n
  | Var (x, _) -> s x
  | Plus z -> eval_intop ( + ) z
  | Minus z -> eval_intop ( - ) z
  | Times z -> eval_intop ( * ) z
  | True _ -> Data 1
  | False _ -> Data 0
  | Leq z -> eval_intop (fun x y -> if x <= y then 1 else 0) z
  | Conj z -> eval_boolop ( && ) z
  | Disj z -> eval_boolop ( || ) z
  | Neg (e1, li) -> eval_boolop (fun x _ -> not x) (e1, True li, li)
  | Abstraction (al, c, _) ->
    Code (List.map (fun (name, _, _) -> name) al, c)
  | Apply (e, arg_exprs, li) ->
    match eval_expr s e with
    | Code (varnames, func_body) -> eval_code s varnames arg_exprs func_body li
    | _ -> 
      raise (SegFault (error 
        "The lhs of an application must evaulate to a function" li))

and eval_code s varnames arg_exprs func_body li = 
  let rec join_args varnames arg_vals acc =
    match (varnames, arg_vals) with
    | ([], []) -> acc
    | (vn :: varnames, av :: arg_vals) -> 
      join_args varnames arg_vals ((vn, av) :: acc)
    | (vn :: varnames, []) ->
      let m = Printf.sprintf "function application needs %d more arguments" ((List.length varnames) + 1) in
      raise (SegFault (error m li))
    | ([], arg_vals) ->
      let m = (Printf.sprintf "function application given %d more arguments than needed" (List.length arg_vals)) in
      raise (SegFault (error m li))
  in
  let arg_pairs = 
    List.rev 
      (join_args 
        varnames 
        (List.map (fun e -> eval_expr s e) arg_exprs) 
        [])
  in
  let s_args = 
    List.fold_left (fun s (vn, hv) -> update s vn hv) s arg_pairs 
  in
  (exec_cmd s_args func_body) "ret"

and exec_cmd (s : store) (c : icmd) : store =
  match c with
  | Skip _ | Decl _ -> s
  | Seq (c1, c2, _) -> exec_cmd (exec_cmd s c1) c2
  | Assign (v, e, _) -> update s v (eval_expr s e)
  | Cond (e, c1, c2, _) ->
    exec_cmd s (if eval_expr s e = Data 0 then c2 else c1)
  | While (e, c1, li) -> exec_cmd s (Cond (e, Seq (c1, c, li), Skip li, li))

let argval = function
  | "true" -> 1
  | "false" -> 0
  | x -> int_of_string x

let argtyp = function
  | "true" | "false" -> TypBool
  | _ -> TypInt

let main () =
  let path, args =
    match Array.to_list Sys.argv with
    | _ :: path :: argv -> (path, argv)
    | argv -> raise (Invalid_argument "Usage: <exe> ./path/to/program <arg1> <arg2> ... <argn>")
  in
  let c = Simplparser.parse_cmd Simpllexer.token (Lexing.from_channel (open_in path)) in

  let s_pairs = 
    List.mapi
      (fun i a ->
        let arg = "arg" ^ string_of_int i in
        let data = Data (argval a) in
        (arg, data))
      args
  in
  let s = init_store s_pairs in

  let typ_pairs = 
    List.mapi
      (fun i a ->
        let arg = "arg" ^ string_of_int i in
        let vtyp = VTyp (argtyp a, true) in
        (arg, vtyp))  
      args
  in
  let tc = init_typctx typ_pairs in

  match typchk_cmd tc c with
  | CTypErr s -> print_string ("Typing error: " ^ s ^ "\n")
  | TypCtx tc' ->
    print_string
      (match tc' "ret" with
      | Undeclared -> "Typing error: return value undeclared"
      | VTyp (_, false) -> "Typing error: return value uninitialized"
      | VTyp (rtyp, true) ->
        (match exec_cmd s c "ret" with
        | Code _ -> "<code>"
        | Data n ->
          if rtyp = TypInt then
            string_of_int n
          else if n = 0 then
            "false"
          else
            "true"));
    print_newline ()
;;

main ()
