
open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

let dbg = ref false;;

let string_of_operation = function
    LnOpen(s) -> print_endline ("LnOpen("^s^")")
  | LnInst(s) -> print_endline ("LnInst("^s^")")
  | LnQuit -> print_endline ("LnQuit")
;;
  
let rec string_of_operation_list = function 
    [] -> ()
  | h::t -> string_of_operation h; string_of_operation_list t
;;

let rec read_multiline str = 
  match (s1 multilinetoken (from_string str)) with
      ( Some x, true) -> string_of_operation_list(x); x
      (* ( Some x, true) -> x *)
    | ( None, true) -> []
    | (_ , false) -> read_multiline (str^read_line())
;;

let read_whole_file filename =
  let ch = open_in filename 
  in
    let s = really_input_string ch (in_channel_length ch) 
    in close_in ch; print_endline s; s
;;

let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";  
  let speclist = [("-d", Arg.Set dbg, "Activates debug mode");] in
  let rec loop ctx dbg =
    print_string ">> ";
    flush stdout;
    try

      let rec process_instruction i =
        let inst_l = match i with 
            LnOpen f -> s2_list token (from_string (read_whole_file f))
          | LnInst i' -> s2_list token (from_string (i'^";;"))
          | LnQuit -> raise End_of_file
        in 
          let rec process_list_inst l = match l with
            [] -> ()
            | h::t -> exec ctx h dbg; process_list_inst t
          in process_list_inst inst_l
      in 
        let rec process_lines l = match l with 
            [] -> loop ctx dbg 
          | h::t -> process_instruction h; process_lines t
        in 
          process_lines (read_multiline (read_line()))
      
    with
       Lexical_error ->
         print_endline "lexical error";
         loop ctx dbg
     | Parse_error ->
         print_endline "syntax error";
         loop ctx dbg
     | Type_error e ->
         print_endline ("type error: " ^ e);
         loop ctx dbg
     | Index_error e -> 
         print_endline ("index error:" ^ e);
         loop ctx dbg
     | Sys_error e -> 
        print_endline("Sys error:"^e);
          loop ctx dbg
     | End_of_file ->
         print_endline "...bye!!!"

         
  in let usage_msg = "Top Lambda, Options available:"
  in Arg.parse speclist print_endline usage_msg;

  if (!dbg) then 
    print_endline "debugmode active\n"
  else 
    print_endline "normal mode\n";
  loop emptyctx (!dbg)
  ;;

top_level_loop ()
;;


