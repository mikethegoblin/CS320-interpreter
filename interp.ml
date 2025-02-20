(* Reference implementation of full interpreter for BU Fall2020 CS320 *)

(* utility functions *)

let rec implode (cs: char list): string =
  match cs with
  | c :: cs -> (String.make 1 c) ^ implode cs
  | [] -> ""

let rec explode (s: string): char list =
  let len = String.length s in
  let rec loop i =
    if i < len then (String.get s i) :: loop (i + 1)
    else []
  in loop 0

let readlines fname =
  let ic = open_in fname in
  let rec loop ic =
    match input_line ic with
    | s -> s :: loop ic
    | exception _ -> []
  in
  let s = loop ic in
  let () = close_in ic in
  s


(* Abstract syntax *)

type name = string

type value =
  | B of bool
  | I of int
  | S of string
  | N of name
  | U
  | E
  | C of closure 

and closure = (name * commands * env_lst)

and command =
  | Push of value | Swap | Pop
  | Add | Sub | Mul | Div | Rem | Neg
  | Cat
  | And | Or | Not | Eq
  | Lte | Lt | Gte | Gt 
  | Bnd
  | BeginEnd of commands
  | IfThenElse of (commands * commands * commands)
  | Fun of (name * name * commands)
  | Call
  | Return
  | TryWith of (commands * commands)
  | Quit

and commands = command list

and stack = value list

and env = (string * value) list

and env_lst = env list

let tw_stack: bool list ref = ref [] (** not sure if global variable works *)

let fprint_value oc cst =
  Printf.
    (match cst with
     | B b -> fprintf oc "<%b>" b
     | I i -> fprintf oc "%d" i
     | S s -> fprintf oc "%s" s
     | N n -> fprintf oc "%s" n
     | U -> fprintf oc "<unit>"
     | E -> fprintf oc "<error>"
     | C c -> fprintf oc "<CLOSURE>")

let rec fprint_command oc com =
  Printf.
    (match com with
    | Push cst ->
      fprintf oc "Push %a\n" fprint_value cst;
    | Swap -> fprintf oc "Swap\n"
    | Pop -> fprintf oc "Pop\n"
    | Add -> fprintf oc "Add\n"
    | Sub -> fprintf oc "Sub\n"
    | Mul -> fprintf oc "Mul\n"
    | Div -> fprintf oc "Div\n"
    | Rem -> fprintf oc "Rem\n"
    | Neg -> fprintf oc "Neg\n"
    | Cat -> fprintf oc "Cat\n"
    | And -> fprintf oc "And\n"
    | Or -> fprintf oc "Or\n"
    | Not -> fprintf oc "Not\n"
    | Eq -> fprintf oc "Eq\n"
    | Lte -> fprintf oc "Lte\n"
    | Lt -> fprintf oc "Lt\n"
    | Gte -> fprintf oc "Gte\n"
    | Gt -> fprintf oc "Gt\n"
    | Bnd -> fprintf oc "Bnd\n"
    | BeginEnd coms -> 
    fprintf oc "Begin\n"; fprint_commands oc coms; fprintf oc "End\n"
    | IfThenElse (test, true_coms, false_coms) -> 
    fprintf oc "If\n"; fprint_commands oc test; fprintf oc "Then\n"; fprint_commands oc true_coms;
    fprintf oc "Else\n"; fprint_commands oc false_coms; fprintf oc "EndIf\n"
    | Fun (fname, arg, coms) -> 
    fprintf oc "Fun "; fprintf oc "%s " fname; fprintf oc "%s\n" arg;
    fprint_commands oc coms; fprintf oc "EndFun\n"
    | Call -> fprintf oc "Call\n"
    | Return -> fprintf oc "Return\n"
    | TryWith (coms1, coms2) -> 
      fprintf oc "Try\n"; fprint_commands oc coms1; fprintf oc "With\n"; fprint_commands oc coms2;
      fprintf oc "EndTry\n"
    | Quit -> fprintf oc "Quit\n")

and fprint_commands oc coms =
  List.iter (fprint_command oc) coms

let fprint_stack oc st =
  Printf.
    (List.iter (fun sv -> fprint_value oc sv; fprintf oc "\n") st)

let print_value = fprint_value stdout
let print_command = fprint_command stdout
let print_commands = fprint_commands stdout
let print_stack = fprint_stack stdout

(* Parser *)

type 'a parser = char list -> 'a option * char list

let return (a: 'a): 'a parser  = fun cs -> (Some a, cs)

let bind (p: 'a parser) (f: 'a -> 'b parser): 'b parser =
  fun cs ->
  let a, cs' = p cs in
  match a with
  | Some a -> f a cs'
  | None -> (None, cs)

let (let*) = bind

(* defining another bind operator, f transforms type 'a to type 'b *)
let (|>>) (p: 'a parser) (f: 'a -> 'b): 'b parser =
  let* a = p in
  return (f a)

(* parse using 'a parser and then return 'b parser *)
let (>>) (p: 'a parser) (q: 'b parser): 'b parser =
  let* _ = p in
  q

(* used to parse a part of the string using 'a parser and the rest using 'b parser
keep the first part *)
let (<<) (p: 'a parser) (q: 'b parser): 'a parser =
  let* a = p in
  let* _ = q in
  return a

let fail: 'a parser = fun cs -> (None, cs)

(* simply returns a unit parser *)
let delay (): unit parser = return ()

let (<|>) (p: 'a parser) (q: 'a parser): 'a parser =
  fun cs ->
  match p cs with
  | (Some a, cs) -> (Some a, cs)
  | (None, _) -> q cs

let choice (ps: 'a parser list): 'a parser =
  List.fold_right (fun p acc -> p <|> acc) ps fail

let rec many (p: 'a parser): 'a list parser =
  (let* a = p in
   let* ls = many p in
   return(a :: ls))
  <|>
  return[]

(* recursive parser that fails on empty *)
let many1 (p: 'a parser): 'a list parser =
  let* a = p in
  let* ls = many p in
  return(a :: ls)

let opt (p: 'a parser): 'a option parser =
  (let* a = p in
   return (Some a))
  <|>
  return None

let read: char parser =
  fun cs ->
  match cs with
  | c :: cs -> (Some c, cs)
  | [] -> (None, cs)

let rec readn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = readn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let rec peak: char parser =
  fun cs ->
  match cs with
  | c :: _ -> (Some c, cs)
  | [] -> (None, cs)

let rec peakn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = peakn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let sat (f: char -> bool): char parser =
  let* c = read in
  if f c then return c
  else fail

let char (c: char): char parser =
  sat ((=) c)

let digit: char parser =
  sat (fun x -> '0' <= x && x <= '9')

let lower: char parser =
  sat (fun x -> 'a' <= x && x <= 'z')

let upper: char parser =
  sat (fun x -> 'A' <= x && x <= 'Z')

let alpha: char parser =
  lower <|> upper

let alphanum: char parser =
  alpha <|> digit

let string (str: string): unit parser =
  let len = String.length str in
  let* str' = readn len in
  if str = str' then return ()
  else fail

(* a parser that strips away white space/carriage return/tab *)
let w: unit parser =
  let* _ = sat (String.contains " \r\n\t") in
  return ()

(* recursive version of parser w  *)
let ws: unit parser =
  let* _ = many w in
  return ()

let ws1: unit parser =
  let* _ = w in
  let* _ = ws in
  return ()

let reserved (s: string): unit parser =
  string s >> ws

(* delimiter parser that strips away left most and right most elements *)
let delimit l p r =
  let* _ = l in
  let* res = p in
  let* _ = r in
  return res

let int: int parser =
  let* sgn = opt (reserved "-") in
  let* cs = many1 digit in
  let n = List.fold_left
      (fun acc c -> acc * 10 + (int_of_char c) - (int_of_char '0'))
      0 cs
  in
  match sgn with
  | Some _ -> return (-n)
  | None -> return n

let bool: bool parser =
  let b = (string "true" >> return true) <|>
          (string "false" >> return false)
  in
  delimit (string "<") b (string ">")

let error: unit parser =
  string "<error>"

let unit: unit parser =
  string "<unit>"

let str: string parser =
  let* cs = delimit (char '"') (many (sat ((!=) '"'))) (char '"') in
  return (implode cs)

let name: string parser =
  let* os = many (char '_') in
  let* c = alpha in
  let* cs = many (alphanum <|> char '_') in
  return ((implode os) ^ (implode (c :: cs)))

let value: value parser =
  choice
    [ (int   |>> fun n -> I n);
      (bool  |>> fun b -> B b);
      (error |>> fun e -> E);
      (str   |>> fun s -> S s);
      (name  |>> fun n -> N n);
      (unit  |>> fun u -> U); ]

let push: command parser =
  let* _ = reserved "Push" in
  let* cst = value << ws in
  return (Push cst)

let swap: command parser =
  let* _ = reserved "Swap" in
  return Swap

let pop: command parser =
  let* _ = reserved "Pop" in
  return Pop

let add: command parser =
  let* _ = reserved "Add" in
  return Add

let sub: command parser =
  let* _ = reserved "Sub" in
  return Sub

let mul: command parser =
  let* _ = reserved "Mul" in
  return Mul

let div: command parser =
  let* _ = reserved "Div" in
  return Div

let rem: command parser =
  let* _ = reserved "Rem" in
  return Rem

let neg: command parser =
  let* _ = reserved "Neg" in
  return Neg

let quit: command parser =
  let* _ = reserved "Quit" in
  return Quit

let cat: command parser = 
  let* _ = reserved "Cat" in 
  return Cat

let _and: command parser = 
  let* _ = reserved "And" in 
  return And

let _or: command parser = 
  let* _ = reserved "Or" in 
  return Or

let _not: command parser = 
  let* _ = reserved "Not" in 
  return Not

let eq: command parser = 
  let* _ = reserved "Eq" in 
  return Eq

let lte: command parser = 
  let* _ = reserved "Lte" in 
  return Lte

let lt: command parser = 
  let* _ = reserved "Lt" in 
  return Lt

let gte: command parser = 
  let* _ = reserved "Gte" in 
  return Gte

let gt: command parser = 
  let* _ = reserved "Gt" in 
  return Gt

let bnd: command parser = 
  let* _ = reserved "Bnd" in 
  return Bnd

let call: command parser = 
  let* _ = reserved "Call" in 
  return Call

let rtn: command parser = 
  let* _ = reserved "Return" in 
  return Return

let rec command () =
  let* _ = delay() in
  choice
    [ push; swap; pop;
      add; sub; mul; div; rem; neg;
      cat; _and; _or; _not; eq;
      lte; lt; gte; gt;
      bnd;
      begin_end ();
      if_then_else ();
      _fun ();
      call;
      rtn;
      try_with();
      quit; ]

and commands () =
  let* _ = delay() in
  many1 (command ())

and begin_end () = 
  let* _ = reserved "Begin" in 
  let* coms = commands () in 
  let* _ = reserved "End" in 
  return (BeginEnd coms)

and if_then_else () = 
  let* _ = reserved "If" in 
  let* test = commands () in 
  let* _ = reserved "Then" in 
  let* true_coms = commands () in 
  let* _ = reserved "Else" in 
  let* false_coms = commands () in 
  let* _ = reserved "EndIf" in 
  return (IfThenElse (test, true_coms, false_coms))

and _fun () = 
  let* _ = reserved "Fun" in 
  let* fname = name << ws in 
  let* arg = name << ws in 
  let* coms = commands () in 
  let* _ = reserved "EndFun" in 
  return (Fun (fname, arg, coms))

and try_with () = 
  let* _ = reserved "Try" in 
  let* coms1 = commands () in 
  let* _ = reserved "With" in 
  let* coms2 = commands () in 
  let* _ = reserved "EndTry" in 
  return (TryWith (coms1, coms2))


(* evaluation *)

let get_int x =
  match x with
  | I i -> Some i
  | _ -> None

let get_bool x =
  match x with
  | B b -> Some b
  | _ -> None

let get_string x =
  match x with
  | S s -> Some s
  | _ -> None

let get_name x =
  match x with
  | N n -> Some n
  | _ -> None

(* search for key x in the current environment *)
let rec search_env (x: string) (env: env): value option = 
  match env with
  | (k, v)::env' -> if k = x then Some v else search_env x env'
  | [] -> None

(* search for key x in all environments, search from cur env to outer env*)
let rec search_envs (x: string) (envs: env_lst): value option = 
  match envs with
  | e::envs' -> 
    (match search_env x e with
    | Some v -> Some v
    | None -> search_envs x envs')
  | [] -> None

(* updates the binding of a bounded name in the current environment *)
let rec update_bnd (key: string) (x: value) (env: env) = 
  match env with
  | [] -> []
  | (k, v)::tl -> if k = key then (k, x)::(update_bnd key x tl) else (k, v)::(update_bnd key x tl)

(* performs add command on stack *)
let add_stack (x: value) (y: value) (envs: env_lst) (stack: stack)=
  match x, y with
  | I a, I b -> I (a + b) :: stack
  | (I a, N b) | (N b, I a) ->  
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> I (a + i) :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> I (i1 + i2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs sub command on stack *)
let sub_stack (x: value) (y:value) (envs: env_lst) (stack: stack)= 
  match x, y with
  | I a, I b -> I (a - b) :: stack
  | (I a, N b) ->  
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> I (a - i) :: stack
      | None -> E :: x :: y :: stack)
  | (N b, I a) -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> I (i - a) :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> I (i1 - i2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs div command on stack *)
let div_stack (x: value) (y: value) (envs: env_lst) (stack: stack)= 
  match x, y with
  | I a, I b -> if b <> 0 then I (a/b) :: stack else E :: x :: y :: stack
  | (I a, N b) ->  
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> if i <> 0 then I (a/i) :: stack else E :: x :: y :: stack
      | None -> E :: x :: y :: stack)
  | (N b, I a) -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> if a <> 0 then I (i/a) :: stack else E :: x :: y :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> I (i1 - i2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs rem command on stack *)
let rem_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if b <> 0 then I (a mod b) :: stack else E :: x :: y :: stack
  | (I a, N b) ->  
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> if i <> 0 then I (a mod i) :: stack else E :: x :: y :: stack
      | None -> E :: x :: y :: stack)
  | (N b, I a) -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> if a <> 0 then I (i mod a) :: stack else E :: x :: y :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> I (i1 - i2) :: stack 
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs mul command on stack *)
let mul_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> I (a * b) :: stack
  | (I a, N b) | (N b, I a) ->  
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | Some i -> I (a * i) :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> I (i1 * i2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs neg command on stack *)
let neg_stack (x: value) (envs: env_lst) (stack: stack) = 
  match x with
  | I a -> I (-a) :: stack
  | N a -> 
    (match search_envs a envs with
    | None -> E :: x :: stack
    | Some v ->
      match get_int v with
      | None -> E :: x :: stack
      | Some i -> I (-i) :: stack) 
  | _ -> E :: x :: stack

(* performs cat command on stack *)
let cat_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | S a, S b -> S (a ^ b) :: stack
  | N a, S b -> 
    (match search_envs a envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_string v with
      | Some s -> S (s ^ b) :: stack
      | None -> E :: x :: y :: stack)
  | S b, N a -> 
    (match search_envs a envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_string v with
      | Some s -> S (b ^ s) :: stack
      | None -> E :: x :: y :: stack)
  | N a , N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_string v1, get_string v2 with
      | Some s1, Some s2 -> S (s1 ^ s2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs and command on stack *)
let and_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | B a, B b -> B (a && b) :: stack
  | B a, N b | N b, B a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_bool v with
      | Some t -> B (a && t) :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_bool v1, get_bool v2 with
      | Some t1, Some t2 -> B (t1 && t2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs or command on stack *)
let or_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | B a, B b -> B (a || b) :: stack
  | B a, N b | N b, B a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_bool v with
      | Some t -> B (a || t) :: stack
      | None -> E :: x :: y :: stack)
  | N a, N b -> 
    (match (search_envs a envs), (search_envs b envs) with
    | Some v1, Some v2 -> 
      (match get_bool v1, get_bool v2 with
      | Some t1, Some t2 -> B (t1 || t2) :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs not command on stack *)
let not_stack (x: value) (envs: env_lst) (stack: stack) = 
  match x with
  | B a -> B (not a) :: stack
  | N a -> 
    (match search_envs a envs with
    | None -> E :: x :: stack
    | Some v -> 
      match get_bool v with
      | Some b -> B (not b) :: stack
      | None -> E :: x :: stack)
  | _ -> E :: x :: stack

(* performs eq command on stack *)
let eq_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if a = b then B true :: stack else B false :: stack
  | I a, N b | N b, I a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if a = i then B true :: stack else B false :: stack)
  | N a, N b -> 
    (match search_envs a envs, search_envs b envs with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> if i1 = i2 then B true :: stack else B false :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs lte command on stack *)
let lte_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if a <= b then B true :: stack else B false :: stack
  | I a, N b -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if a <= i then B true :: stack else B false :: stack)
  | N b, I a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if i <= a then B true :: stack else B false :: stack)
  | N a, N b -> 
    (match search_envs a envs, search_envs b envs with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> if i1 <= i2 then B true :: stack else B false :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs lt command on stack *)
let lt_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if a < b then B true :: stack else B false :: stack
  | I a, N b -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if a < i then B true :: stack else B false :: stack)
  | N b, I a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if i < a then B true :: stack else B false :: stack)
  | N a, N b -> 
    (match search_envs a envs, search_envs b envs with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> if i1 < i2 then B true :: stack else B false :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs gte command on stack *)
let gte_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if a >= b then B true :: stack else B false :: stack
  | I a, N b -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if a >= i then B true :: stack else B false :: stack)
  | N b, I a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if i >= a then B true :: stack else B false :: stack)
  | N a, N b -> 
    (match search_envs a envs, search_envs b envs with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> if i1 >= i2 then B true :: stack else B false :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs gt command on stack *)
let gt_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  match x, y with
  | I a, I b -> if a > b then B true :: stack else B false :: stack
  | I a, N b -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if a > i then B true :: stack else B false :: stack)
  | N b, I a -> 
    (match search_envs b envs with
    | None -> E :: x :: y :: stack
    | Some v -> 
      match get_int v with
      | None -> E :: x :: y :: stack
      | Some i -> if i > a then B true :: stack else B false :: stack)
  | N a, N b -> 
    (match search_envs a envs, search_envs b envs with
    | Some v1, Some v2 -> 
      (match get_int v1, get_int v2 with
      | Some i1, Some i2 -> if i1 > i2 then B true :: stack else B false :: stack
      | _ -> E :: x :: y :: stack)
    | _ -> E :: x :: y :: stack)
  | _ -> E :: x :: y :: stack

(* performs bnd command on stack *)
let bnd_stack (x: value) (y: value) (envs: env_lst) (stack: stack) = 
  let env_tp, rest = 
    (match envs with
    | hd::tl -> hd, tl)
  in
  let cur_env = env_tp in 
  match x, y with
  | _, E -> envs, (E :: x :: y :: stack)
  | N a, N b ->
    (match search_envs b envs with
    | None -> envs, (E :: x :: y :: stack)
    | Some v -> 
      match search_env a cur_env with
      | Some v -> ((update_bnd a v cur_env) :: rest), U :: stack
      | None -> ((a, v)::cur_env) :: rest, U :: stack)
  | N a, b -> 
    (match search_env a cur_env with
    | Some v -> (((update_bnd a b cur_env)) :: rest), U :: stack
    | None -> ((a, b)::cur_env) :: rest, U :: stack
    )
  | _ -> envs, (E :: x :: y :: stack)

(* process the end of BeginEnd block, delete current env
and return last stack frame to original stack *)
(* let end_env (stack: stack) (envs: env_lst) = 
  let cur_len = List.length stack in 
  let old_len = 
    (match envs with
    | (env, n)::tl -> n) in 
  let top_frame = 
    (match stack with
    | tf::rest -> tf) in 
  let rec flush_stack (stack: stack) (num: int): stack = 
    match num with
    | 0 -> stack
    | n -> 
      (match stack with
      | [] -> []
      | hd :: tl -> flush_stack tl (num - 1))
  in
  top_frame :: (flush_stack stack (cur_len - old_len)) *)

(* let eval_test (stack: stack) (envs: env_lst): bool option = 
  match stack with
  | (B true)::tl -> Some true
  | (B false)::tl -> Some false
  | (N a) :: tl -> 
    (match search_envs a envs with
    | Some (B true) -> Some true
    | Some (B false) -> Some false
    | _ -> None)
  | _ -> None *)

let eval_test (x: value) (envs: env_lst): bool option = 
  match x with
  | B true -> Some true
  | B false -> Some false
  | N a ->
    (match search_envs a envs with
    | Some (B true) -> Some true
    | Some (B false) -> Some false
    | _ -> None)
  | _ -> None

let bind_closure (fname: name) (arg: name) (coms: commands) (envs: env_lst): env_lst = 
  let closure = (arg, coms, envs) in 
  match envs with
  | e::tl -> ((fname, C closure)::e)::tl

let resolve_name (x: name) (envs: env_lst) = 
  match search_envs x envs with
  | Some v -> v
  

  

let rec interp coms stack (envs: env_lst): stack * bool =
  match coms, stack with
  | Push v :: coms, _ ->
    let new_stack = v :: stack in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Swap :: coms, x :: y :: stack ->
    interp coms (y :: x :: stack) envs
  | Pop :: coms, x :: stack ->
    interp coms stack envs
  | Add :: coms, x :: y :: stack' ->
    let new_stack = add_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Sub :: coms, x :: y :: stack' ->
    let new_stack = sub_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Mul :: coms, x :: y :: stack' ->
    let new_stack = mul_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Div :: coms, x :: y :: stack' ->
    let new_stack = div_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Rem :: coms, x :: y :: stack' ->
    let new_stack = rem_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Neg :: coms, x :: stack' ->
    let new_stack = neg_stack x envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Cat :: coms, x :: y :: stack' -> 
    let new_stack = cat_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | And :: coms, x :: y :: stack' -> 
    let new_stack = and_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Or :: coms, x :: y :: stack' -> 
    let new_stack = or_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Not :: coms, x :: stack' -> 
    let new_stack = not_stack x envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Eq :: coms, x :: y :: stack' -> 
    let new_stack = eq_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Lte :: coms, x :: y :: stack' -> 
    let new_stack = lte_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Lt :: coms, x :: y :: stack' -> 
    let new_stack = lt_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Gte :: coms, x :: y :: stack' -> 
    let new_stack = gte_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Gt :: coms, x :: y :: stack' ->
    let new_stack = gt_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack envs)
    | [] -> interp coms new_stack envs)
  | Bnd :: coms, x :: y :: stack' -> 
    let new_envs, new_stack = bnd_stack x y envs stack' in 
    (match !tw_stack with
    | hd :: tl -> 
      (match new_stack with
      | E :: s -> 
        tw_stack := true :: tl; (new_stack, false)
      | _ -> interp coms new_stack new_envs)
    | [] -> interp coms new_stack new_envs)
  | BeginEnd coms :: coms', stack -> 
    let envs' = [] :: envs in 
    let stack', quit = interp coms stack envs' in 
    if quit then (stack', true) else
    let top_frame = 
      (match stack' with
      | hd::tl -> hd
    ) in 
    (match !tw_stack with
    | true :: tl -> (stack', false)
    | _ -> interp coms' (top_frame::stack) envs)
  | IfThenElse (test, true_coms, false_coms) :: coms, stack ->
    let envs' = []::envs in 
    let stack1, quit = interp test stack envs' in 
    if quit then (stack1, true) else
    let top_frame = 
    (match stack1 with 
    | hd::tl -> hd) in 
    (match !tw_stack with
    | true :: tl -> (stack1, false)
    | _ -> 
      (match eval_test top_frame envs with
      | None -> 
        (match !tw_stack with
        | hd :: tl -> tw_stack := true :: tl; (stack1, false)
        | [] -> interp coms (E :: stack) envs)
      | Some true -> 
        let envs' = [] :: envs in 
        let stack1, quit = interp true_coms stack envs' in 
        if quit then (stack1, true) else
        let top_frame = 
          (match stack1 with
          | hd::tl -> hd
        ) in  
        (match !tw_stack with
        | true :: tl -> (stack1, false)
        | _ -> interp coms (top_frame::stack) envs)
      | Some false -> 
        let envs' = [] :: envs in 
        let stack1, quit = interp false_coms stack envs' in 
        if quit then (stack1, true) else 
        let top_frame = 
          (match stack1 with
          | hd::tl -> hd
        ) in  
        (match !tw_stack with
        | true :: tl -> (stack1, false)
        | _ -> interp coms (top_frame::stack) envs)))
  | Fun (fname, arg, coms) :: coms', stack -> 
    let envs' = bind_closure fname arg coms envs in 
    interp coms' (U::stack) envs'
  | Call :: coms, x :: y :: stack' ->
    (match x, y with
    | x, C (arg, coms', envs') -> 
      (match x with
      | N a -> 
        (match search_envs a envs with
        | Some v -> 
          (match envs' with
          | e::tl -> 
            let new_envs = ((arg, v) :: e) :: tl in 
            let stack1, quit = interp coms' stack' new_envs in 
            if quit then (stack1, true) else 
            let top_frame = 
              (match stack1 with
              | hd::tl -> hd) in 
            (match !tw_stack with
            | true :: tl -> (stack1, false)
            | _ -> interp coms (top_frame::stack') envs))
        | _ -> 
          (match !tw_stack with
          | hd :: tl -> tw_stack := true :: tl; (stack, false)
          | [] -> interp coms (E :: x :: y :: stack') envs))
      | v -> 
        (match envs' with
          | e::tl -> 
            let new_envs = ((arg, v) :: e) :: tl in 
            let stack1, quit = interp coms' stack' new_envs in 
            if quit then (stack1, true) else 
            let top_frame = 
              (match stack1 with
              | hd::tl -> hd) in 
            (match !tw_stack with
            | true :: tl -> (stack1, false)
            | _ -> interp coms (top_frame::stack') envs)))
    | N a, N fname ->
      (match search_envs a envs, search_envs fname envs with
      | Some v, Some (C (arg, coms', envs') as clos) ->
        (match envs' with
        | e::tl -> 
          let new_envs = 
            (match search_envs fname envs' with
            | Some f -> ((arg, v) :: e) :: tl
            | None -> ((arg, v) :: (fname, clos) :: e) :: tl) in 
          let stack1, quit = interp coms' stack' new_envs in 
          if quit then (stack1, true) else
          let top_frame = 
            (match stack1 with
            | hd::tl -> hd) in 
          (match !tw_stack with
          | true :: tl -> (stack1, false)
          | _ -> interp coms (top_frame::stack') envs))
      | _ -> 
        (match !tw_stack with
        | hd :: tl -> tw_stack := true :: tl; (stack, false)
        | [] -> interp coms (E :: x :: y :: stack') envs))
    | v, N fname -> 
      (match search_envs fname envs with
      | Some (C (arg, coms', envs') as clos) -> 
        (match envs' with
        | e::tl -> 
          let new_envs = 
            (match search_envs fname envs' with
            | Some f -> ((arg, v) :: e) :: tl
            | None -> ((arg, v) :: (fname, clos) :: e) :: tl) in 
          let stack1, quit = interp coms' stack' new_envs in 
          if quit then (stack1, true) else 
          let top_frame = 
            (match stack1 with 
            | hd::tl -> hd) in 
          (match !tw_stack with
          | true :: tl -> (stack1, false)
          | _ -> interp coms (top_frame::stack') envs))
      | _ -> 
        (match !tw_stack with
        | hd :: tl -> tw_stack := true :: tl; (stack, false)
        | [] -> interp coms (E :: x :: y :: stack') envs))
    | _ -> 
      (match !tw_stack with
      | hd :: tl -> tw_stack := true :: tl; (stack, false)
      | [] -> interp coms (E :: x :: y :: stack') envs))
  | Return :: coms, x :: stack -> 
    (match x with
    | N a -> [resolve_name a envs], false
    | _ -> [x], false)
  | TryWith (coms1, coms2) :: coms, stack -> 
    tw_stack := false :: !tw_stack;
    let new_envs = [] :: envs in 
    let stack1, quit = interp coms1 stack new_envs in 
    if quit then (stack1, true) else 
    let top_frame = 
      (match stack1 with
      | hd :: tl -> hd
      ) in 
    (match !tw_stack with
    | false :: tl -> tw_stack := tl; interp coms (top_frame :: stack) envs
    | true :: tl -> 
      tw_stack := tl; 
      let new_envs = [] :: envs in 
      let stack1, quit = interp coms2 stack new_envs in 
      if quit then (stack1, true) else 
      let top_frame = 
        (match stack1 with
        | hd :: tl -> hd
        ) in 
      (match !tw_stack with
      | true :: tl -> (stack1, false)
      | _ -> interp coms (top_frame :: stack) envs))
  | Quit :: coms, _ -> stack, true
  | [], _ -> stack, false
  | _ :: coms, _ ->
    (match !tw_stack with
    | hd :: tl -> tw_stack := true :: tl; (E :: stack, false)
    | [] -> interp coms (E :: stack) envs)

(* testing *)

let parse fname =
  let strs = readlines fname in
  let css = List.map explode strs in
  let cs = List.fold_right (fun cs acc -> cs @ ['\n'] @ acc) css [] in
  match (ws >> commands ()) cs with
  | Some coms, [] -> coms
  | _, cs -> failwith (implode cs)

let interpreter (inputFile : string) (outputFile : string) =
  let coms = parse inputFile in
  let oc = open_out outputFile in
  let init_env = [] in 
  let stack, _ = interp coms [] (init_env::[]) in
  let _ = fprint_stack oc stack in
  close_out oc

let debug (fname: string) = 
  let strs = readlines fname in
  let css = List.map explode strs in
  let cs = List.fold_right (fun cs acc -> cs @ ['\n'] @ acc) css [] in
  match (ws >> commands ()) cs with
  | Some coms, [] -> print_commands coms
