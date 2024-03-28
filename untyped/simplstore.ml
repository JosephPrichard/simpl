(* A store maps variable names to integers *)
type store = string -> int 

(* A labled store keeps track of what generation it is and the mapping applied to it *)
type lstore = (int * (string * int) option * store)

let update f v y = 
  (fun n ->
     if n = v then y
     else f n)

let rec init_store (l : (string * int) list) : store =
  match l with
  | [] -> (fun _ -> 0) (* Base case: variable doesn't exist *)
  | h :: l ->
    let v, x = h in
    update (init_store l) v x

let arg_pairs args = 
  List.mapi
    (fun i a -> 
      let varname = "arg" ^ string_of_int i in
      let argv = 
        try int_of_string a 
        with Failure _ -> raise (Failure "args must be ints") in
      (varname, argv))
    args

