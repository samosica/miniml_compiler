open Syntax
open Eval
open Typing

let next_lexbuf = ref (fun () -> Lexing.from_channel stdin)
let is_interactive = ref true
                   
let rec read_eval_print () =
  let input_lexbuf = !next_lexbuf () in
  let prompt = if !is_interactive then "# " else "" in
  print_string prompt;
  flush stdout;
  try
    let exp = Parser.toplevel Lexer.main input_lexbuf in
    let ty = ty_exp Environment.empty exp in
    let v = eval_exp Environment.empty exp in
    print_string "val - : ";
    pp_ty ty;
    print_string " = ";
    pp_val v;
    print_newline();
    read_eval_print()
  with
    Failure message ->
      print_endline message;
      read_eval_print()
  | Parser.Error ->
      print_endline "Parse error";
      read_eval_print()
  | Typing.Error _ as err -> (* Type error *)
     Typing.print_error ~is_interactive:!is_interactive input_lexbuf err;
     read_eval_print()
      
let interact () = read_eval_print()

let batch path =
  if not (Sys.file_exists path) then
    begin
      Printf.fprintf stderr "Cannot find file: %s\n" path;
      exit 1
    end;
  let relative_path =
    if Filename.is_implicit path
    then Filename.concat Filename.current_dir_name path
    else path in
  let ch = open_in path in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.Lexing.lex_curr_p <-
    { Lexing.pos_fname = relative_path
    ; Lexing.pos_lnum = 1
    ; Lexing.pos_cnum = 0
    ; Lexing.pos_bol = 0
    };  
  next_lexbuf := (fun () -> lexbuf);
  is_interactive := false;
  read_eval_print()
  
let () =
  if Array.length Sys.argv < 2 then
    interact()
  else
    batch Sys.argv.(1)
