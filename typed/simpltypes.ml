type varname = string

(* SIMPL types consist of integers and booleans *)
type ityp =
        TypInt
      | TypBool

(* For error reporting purposes, each expression and command now includes
 * information that records where it appeared in the original source file.
 * For example, the lineinfo value ((1,2),(3,4)) indicates that the
 * expression or command started on line 1, column 2 and ended on line 3,
 * column 4 in the original source. *)
type lineinfo = (int * int) * (int * int)

(* The new iexpr type merges the iarith and ibool types
 * from the previous assignment. *)
type iexpr =
        Const of (int * lineinfo)
      | Var of (varname * lineinfo)
      | Plus of (iexpr * iexpr * lineinfo)
      | Minus of (iexpr * iexpr * lineinfo)
      | Times of (iexpr * iexpr * lineinfo)
      | True of lineinfo
      | False of lineinfo
      | Leq of (iexpr * iexpr * lineinfo)
      | Conj of (iexpr * iexpr * lineinfo)
      | Disj of (iexpr * iexpr * lineinfo)
      | Neg of (iexpr * lineinfo)

(* The icmd type is the same as before, except that all
 * iarith and ibool clauses have been changed to iexpr
 * clauses.  There is also a new Decl command that declares
 * a new SIMPL program variable.
 *)
type icmd =
        Skip of lineinfo
      | Seq of (icmd * icmd * lineinfo)
      | Assign of (varname * iexpr * lineinfo)
      | Cond of (iexpr * icmd * icmd * lineinfo)
      | While of (iexpr * icmd * lineinfo)
      | Decl of (ityp * varname * lineinfo)

