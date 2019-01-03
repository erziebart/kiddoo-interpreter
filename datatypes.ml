open Ast
open Semant

module StringMap = Map.Make(String)

(* enhanced expressions *)
(* type express =
  | E of Ast.expr
  | S of express * condata StringMap.t * fundata StringMap.t * fundata StringMap.t  *)

(* translation data type *)
type tdata =
  | Data of float * bool
  | Exprs of expr list

(* language data type *)
type ldata = typ * bool
and typ = 
  | Value of float
  | Tupl of ldata list

let rec string_of_data (v,u) = if u then "undef" else match v with
  | Value(v) -> string_of_float v
  | Tupl(ls) -> "(" ^ String.concat ", " (List.map string_of_data ls) ^ ")"

let data_of_list dl = match dl with
  | [data] -> data
  | _ -> (
      let undefs = List.map (snd) dl in
      let is_undef = List.fold_left (&&) true undefs in
      Tupl(dl),is_undef)

let raise_incompatible l1 l2 = raise(Failure("incompatible tuple lengths: " 
  ^ string_of_int(List.length l1) ^ "!=" ^ string_of_int(List.length l2)))

let rec expr_of_ldata = function
  | Value(v),u -> FloatLit(v,u)
  | Tupl(dl),u -> if u then FloatLit(0.,u) else Tuple(List.map expr_of_ldata dl)