open String
open List

(* Interpreter assignment for CS320F20 *)
(*************************************************************************************************)
(* HELPER FUNCTIONS *)
type const = Int of int | Bool of bool | Error of string | Unit of string | String of string | Name of string

type com = Push | Swap | Pop 
          | Add | Sub | Mul | Div | Rem | Neg
          | And | Or | Not
          | Quit

let explode (s: string) : char list = 
  let rec expl i l = 
    if i < 0 then l 
    else expl (i - 1) (String.get s i :: l) in 
  expl (String.length s - 1) []

let implode (cl: char list) : string = 
  String.concat "" (List.map (String.make 1) cl)

let is_letter = function 
  'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_digit = function 
  '0' .. '9' -> true | _ -> false

let is_underscore = function
  '_' -> true | _ -> false

let const_to_str (c: const): string = 
  match c with
  | Int n -> string_of_int n
  | Bool b -> "<" ^ string_of_bool b ^ ">"
  | Error s | Unit s | Name s | String s -> s

let read_input_file (f_name: string): string list = 
  let ic = open_in f_name in 
  let rec read_lines (ic: in_channel): string list = 
    match input_line ic with
    | exception End_of_file -> close_in ic; []
    | l -> if l <> "" then l :: read_lines ic else read_lines ic
  in read_lines ic

let write_to_file (const_lst: const list) (f_name: string): unit = 
  let oc = open_out f_name in 
  let rec write_str (oc: out_channel) (lst: const list): unit = 
    match lst with
    | [] -> close_out oc; ()
    | hd::tl -> Printf.fprintf oc "%s\n" (const_to_str hd); write_str oc tl
  in write_str oc const_lst

(* function to check if the first character of a string is a quotation mark *)
let fc_isq (str: string): bool = 
  match explode str with
  | [] -> false
  | hd::tl -> if hd = '"' then true else false

let simpleAscii (str: string): string = 
  let lst = explode str in 
  let rec helper (lst: char list): string = 
    match lst with 
    | [] -> ""
    | hd::tl -> 
      let res = helper tl in 
      if (hd = '"') || (hd = '\\') then res else (make 1 hd) ^ res
  in helper lst

let str_to_com (s: string): com option= 
  match s with
  | "Push" -> Some Push
  | "Swap" -> Some Swap
  | "Pop" -> Some Pop
  | "Add" -> Some Add
  | "Sub" -> Some Sub
  | "Mul" -> Some Mul
  | "Div" -> Some Div
  | "Rem" -> Some Rem
  | "Neg" -> Some Neg
  | "And" -> Some And
  | "Or" -> Some Or
  | "Not" -> Some Not
  | "Quit" -> Some Quit
  | _ -> None

(* check if the const is an int *)
let is_int (x: const): bool = 
  match x with
  | Int _ -> true
  | _ -> false

(* checks if the const is zero *)
let is_zero (x: const): bool = 
  match x with
  | Int 0 -> true
  | _ -> false

(* function that performs pop operation on stack *)
let pop_stack (stack: const list): const list = 
  match stack with 
  | [] -> let stack = Error ("<error>") :: stack in stack
  | hd::tl -> tl

(* function that pushes a const to the stack *)
let push_stack (x: const) (stack: const list): const list = 
  x :: stack

(* function that performs add operation on two int const *)
let add (x: const) (y: const): const = 
  match x, y with
  | Int a, Int b -> Int (a+b)

(* performs add command on the stack *)
let add_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> 
    (if is_int h1 && is_int h2 then (add h1 h2)::tl else push_stack (Error "<error>") stack )
  | _ -> push_stack (Error "<error>") stack

(* function that performs subtraction on two int const *)
let sub (x: const) (y: const): const = 
  match x, y with
  | Int a, Int b -> Int (a-b)

(* function that performs sub command on stack *)
let sub_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> 
    (if is_int h1 && is_int h2 then (sub h1 h2)::tl else push_stack (Error "<error>") stack)
  | _ -> push_stack (Error "<error>") stack

(* function that performs multiplication on two int const *)
let mul (x: const) (y: const): const = 
  match x, y with
  | Int a, Int b -> Int (a*b)

(* function that performs mul command on stack *)
let mul_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> 
    (if is_int h1 && is_int h2 then (mul h1 h2)::tl else push_stack (Error "<error>") stack)
  | _ -> push_stack (Error "<error>") stack

(* function that performs int division on two int const *)
let div (x: const) (y: const): const = 
  match x, y with
  | Int a, Int b -> Int (a / b)

(* function that performs div command on stack *)
let div_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> 
    (if is_int h1 && is_int h2 && not (is_zero h2) then (div h1 h2)::tl else push_stack (Error "<error>") stack)
  | _ -> push_stack (Error "<error>") stack

(* function that performs mod on two int const *)
let rem (x: const) (y: const): const = 
  match x, y with
  | Int a, Int b -> Int (a mod b)

(* function that performs rem command on stack *)
let rem_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> 
    (if is_int h1 && is_int h2 && not (is_zero h2) then (rem h1 h2)::tl else push_stack (Error "<error>") stack)
  | _ -> push_stack (Error "<error>") stack

(* function that negates a int const *)
let neg (x: const): const = 
  match x with
  | Int a -> Int (-a)

(* function that performs neg command on stack *)
let neg_stack (stack: const list): const list = 
  match stack with
  | hd::tl -> 
    (if is_int hd then (neg hd)::tl else push_stack (Error "<error>") stack)
  | [] -> push_stack (Error "<error>") stack

(* function that performs swap command on stack *)
let swap_stack (stack: const list): const list = 
  match stack with
  | h1::h2::tl -> h2::h1::tl
  | _ -> push_stack (Error "<error>") stack
(*************************************************************************************************)


(*************************************************************************************************)
(* INTERPRETER FUNCTION *)
(* defining a polymorphic parser *)
type 'a parser = Parser of (string -> ('a option * string))

(* the parse function *)
let parse (p:'a parser) (s:string) : ('a  option * string) = 
  match p with Parser f-> f s

(* char parser used to parse the first character of a string *)
let item_p : char parser = 
  Parser ( fun s -> match explode s with 
                      [] -> (None, "") (*check whether the string is empty *)
                    | x::xs-> (Some x, implode xs))

let str_item_p: string parser = 
  Parser (fun s -> match explode s with
                  | [] -> (None, "")
                  | x::xs -> (Some (make 1 x), implode xs))

(* defining empty parser that simply returns back empty list
   always*)   
let empty_p :'a parser  =  Parser (fun s -> (None,""))

(* defining return parser*)      
let return_p (x:'a) : 'a parser =  Parser (fun s -> (Some x,s))

(* defining choice parser*)      
let (<|>) (p:'a parser) (q:'a parser) : 'a parser = 
  Parser ( fun s -> match parse p s with 
      (None,_) -> parse q s (*return the result of the second parser if the first parser fails *)
      | d -> d  (* return the result of the first parser *)
    )

(* defining let* function *)
let (let*) (p:'a parser) (f:'a -> 'b parser) : 'b parser  = 
  Parser (fun s ->  match (parse p s) with 
                        (None,rs) -> (None, s)
                      |(Some v,rs) -> parse (f v) rs)

(* return a char paser if the condition is satisfied *)
let sat_p (p:char -> bool) : char parser  = 
let* x= item_p in
if p x then return_p x else empty_p

(* 8. defining digit parser*)        
let digit_p : char parser = sat_p is_digit

(* 9. defining letter parser*)      
let letter_p: char parser = sat_p is_letter

(* 10. defining character parser*)      
let char_p (x:char) : char parser = sat_p (fun y -> y=x) 

(* recursive list parser *)
let rec many_p (p: 'a parser): 'a list parser =
  (let* a = p in
   let* ls = many_p p in
   return_p (a :: ls))  <|>  return_p []

(* defining a recursive parser which fails on empty *)
let many1_p (p: 'a parser): 'a list parser =
  let* a = p in
  let* ls = many_p p in 
  return_p (a :: ls)

(* recursive string parser that parses string up to first white space *)
let rec many_p_str (p: 'a parser): string parser = 
  (let* x = p in 
  let* s = many_p_str p in 
  return_p (make 1 x ^ s)) <|> return_p ""

(* recursive string parser that fails on empty *)
let rec many1_p_str (p: 'a parser): string parser = 
  let* x = p in 
  let* s = many_p_str p in 
  return_p (make 1 x ^ s)

(* parser for unsigned integer *)
let nat_p : 'a parser = 
  let* xs = (many1_p digit_p) in
  return_p (int_of_string (implode xs))

(* 14. defining a parser for integers*)      
let int_p :'a parser = 
  (let* _ = (char_p '-') in
  let* n = nat_p in
  return_p (-n)) <|> nat_p

(* defining a boolean parser *)
let b_p: bool parser = 
  let* b = (many1_p letter_p) in 
  let x = implode b in 
  if x = "true" || x = "false" then return_p (bool_of_string x) else empty_p

(* a parser for character in name, invalid character would cause the parser to fail*)
let name_sat_p: 'a parser = 
  sat_p is_underscore <|>
  sat_p is_letter <|>
  sat_p is_digit <|> empty_p

(* a string parser for name *)
let n_p: string parser = many1_p_str name_sat_p

(* a string parser that returns the whole string *)
let str_p: string parser = Parser (fun s -> (Some s, ""))

(* parser for white space *)
let whitespace_p : 'a parser = 
  char_p ' ' <|> char_p '\n' <|> char_p '\t' <|> char_p '\r'

(* 16. defining a parser for sequences of whitespaces*)      
let space_p = many_p whitespace_p 

(* 16. defining a parser for tokens*)                
let token_p (p:'a parser) : 'a parser = 
  let* _ = space_p in
  let* v = p in
  let* _ = space_p in
  return_p v

(* const parser for Int *)
let integer_p :const parser = 
  (let* _ = space_p in 
  let* v = int_p in 
  return_p (Int v)) <|> empty_p

let string_p: const parser = 
  let* _ = space_p in 
  let* v = str_p in 
  if fc_isq v then return_p (String (simpleAscii v)) else empty_p

let bool_p: const parser = 
  (let* _ = space_p in 
  let* _ = char_p '<' in 
  let* v = b_p in 
  let* _ = char_p '>' in 
  return_p (Bool v)) <|> empty_p

let unit_p: const parser = 
  let* _ = space_p in 
  let* v = str_p in 
  if v = "<unit>" then return_p (Unit v) else empty_p

let error_p: const parser = 
  let* _ = space_p in 
  let* v = str_p in 
  if v = "<error>" then return_p (Error v) else empty_p

let name_p: const parser = 
  (let* _ = space_p in 
  let* v = n_p in 
  return_p (Name v)) <|> empty_p

let const_p: const parser = 
  integer_p <|>
  bool_p <|>
  string_p <|>
  unit_p <|>
  error_p <|>
  name_p

  
let com_p: com parser = 
  Parser (fun s -> match parse (many_p_str letter_p) s with
            | (Some x, xs) -> (str_to_com x, xs))

let interpret_com (s: string) (stack: const list): (const list * bool) = 
  match parse com_p s with
  | (Some Push, c) -> 
    (match parse const_p c with
    | (Some x, _) -> (push_stack x stack, false)
    | _ -> (stack, false))
  | (Some Pop, _) -> (pop_stack stack, false)
  | (Some Add, _) -> (add_stack stack, false)
  | (Some Sub, _) -> (sub_stack stack, false)
  | (Some Mul, _) -> (mul_stack stack, false)
  | (Some Div, _) -> (div_stack stack, false)
  | (Some Rem, _) -> (rem_stack stack, false)
  | (Some Neg, _) -> (neg_stack stack, false)
  | (Some Swap, _) -> (swap_stack stack, false)
  | (Some Quit, _) -> (stack, true)


let rec interpret_prog (lst: string list) (stack: const list) (outputFile: string): unit =  
  match lst with 
  | [] -> write_to_file stack outputFile
  | hd::tl -> 
    let (stack, quit) = interpret_com hd stack in 
    if quit then write_to_file stack outputFile else interpret_prog tl stack outputFile

let run_prog (inputFile: string) (outputFile: string): unit = 
  let lst = read_input_file inputFile in  
  interpret_prog lst [] outputFile

  



(*************************************************************************************************)
let interpreter (inputFile : string) (outputFile : string): unit = 
  run_prog inputFile outputFile
