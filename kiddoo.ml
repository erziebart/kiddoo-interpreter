open Ast
open Printf
open Translate

module StringMap = Map.Make(String)

let _ =
  match Array.length Sys.argv with
    (*| 1 -> ( (* run command line interpreter *)
        try 
          let lexbuf = Lexing.from_channel stdin in
          let rec parse_stmt (calltree, consts) = 
            print_string "\n$ "; flush stdout;
            try 
              let ast = Parser.program Scanner.token lexbuf in
              parse_stmt (Translate.translate calltree consts ast)
            with Failure(s) -> print_endline s;
          in
          parse_stmt (Root, StringMap.empty)
        with Sys_error(s) -> print_endline s; exit 0)*)
    | 2 -> ( (* translate a file as input *)
        try
          let infile = Sys.argv.(1) in
          let ic = open_in infile in
          let lexbuf = Lexing.from_channel ic in
          let ast = Parser.program Scanner.token lexbuf in
          ignore (Translate.translate Root StringMap.empty ast)
        with 
          | Failure(s) -> print_endline s; exit 0 
          | Sys_error(s) -> print_endline s; exit 0)
    | _ -> print_endline ("Usage: " ^ Sys.argv.(0) ^ " <input_file>")
