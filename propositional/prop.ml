open Printf

(* Types *)

type prop =
  | Atom of string
  | Neg of prop
  | Conj of prop * prop
  | Disj of prop * prop
  | Impl of prop * prop

type signed =
  | T of prop
  | F of prop

(* Brute-Force Checker Without LaTeX Output:
Tears connectives apart until you find a contradiction;
if you only have atoms left and none are contradictions then return false.
Completely useless unless you just want a yes/no answer to your proposition.
*)

(* Check for contradictions *)

let rec dup (l1 : signed list) (l2 : signed list) : bool =
  match l1 with
  | [] -> false
  | x :: xs ->
    match x with
    | T p ->
      if (List.mem (F p) xs || List.mem (F p) l2) then true else dup xs l2
    | F p ->
      if (List.mem (T p) xs || List.mem (T p) l2) then true else dup xs l2 

(* Here's the main prover function.  It's a pretty hacky implementation because
the tableau method is syntactic and just requires you to break down connectives,
but it works.  Basically the first step is to check if there are any duplicates
(contradictions) and if not then process the propositions and apply the
recursive call.  If you find a contradiction then return true because you've
closed the branch, but if you've processed all the propositions and there are no
contradictions then return false. *)

let rec prover (l1 : signed list) (l2 : signed list) : bool =
  if dup l1 l2 then true else move l1 l2 
and
  move (l1 : signed list) (l2 : signed list) : bool =
    match l1 with
    | [] -> false
    | x :: xs ->
      (match x with
      | T p ->
        (match p with
        | Atom a -> prover xs (T p :: l2)
        | Neg a -> prover (F a :: xs) (T p :: l2)
        | Conj (a , b) -> prover (T a :: T b :: xs) (T p :: l2)
        | Disj (a , b) ->
          (prover (T a :: xs) (T p :: l2)) && (prover (T b :: xs) (T p :: l2))
        | Impl (a , b) -> 
          (prover (F a :: xs) (T p :: l2)) && (prover (T b :: xs) (T p :: l2))
        )
      | F p ->
        (match p with
        | Atom a -> prover xs (F p :: l2)
        | Neg a -> prover (T a :: xs) (F p :: l2)
        | Disj (a , b) -> prover (F a :: F b :: xs) (F p :: l2)
        | Impl (a , b) -> prover (T a :: F b :: xs) (F p :: l2)
        | Conj (a , b) ->
          (prover (F a :: xs) (F p :: l2)) && (prover (F b :: xs) (F p :: l2))
        )
      )

(* Initialize the tableau:
Given a proposition p, root the tableau with F p.
The empty list is the list of propositions we have processed,
since we are using a destructive method.  It it necessary to keep track
of the destroyed propositions so we can check for contradictions. *)

let solve (p : prop) : string =
  let k = prover [F p] [] in
  if k then "All branches are closed" else "There are open branches"

(* A More Careful Approach:
This one actually keeps track of things so you can print out the tableau in
LaTeX.  A first approach would be to just print out each branch of the tableau
(you can get that going without too much trouble), but you can't easily
reconstruct the tableau given a list of branches.  Instead you just
construct the tableau gradually as you use the tableau rules.
*)

(* if all the items in the list are atoms and there is no contradiction,
then the tableau is open. *)

let rec all_atoms (s : signed list) : bool =
  match s with
  | [] -> true
  | x :: xs ->
    (match x with
    | T p ->
      (match p with
      | Atom a -> all_atoms xs
      | _ -> false
      )
    | F p ->
      (match p with
      | Atom a -> all_atoms xs
      | _ -> false
      )
    )

(* LaTeX-friendly printing with $ and mathmode stuff *)

let rec print_signed (s : signed) : string =
  match s with
  | T p -> "$T" ^ print_prop p ^ "$"
  | F p -> "$F" ^ print_prop p ^ "$"
and
  print_prop (p : prop) : string =
    match p with
    | Atom a -> String.uppercase a
    | Neg a -> "(\\neg " ^ print_prop a ^ ")"
    | Conj (a , b) -> "(" ^ print_prop a ^ " \wedge " ^ print_prop b ^ ")"
    | Impl (a , b) -> "(" ^ print_prop a ^ " \Rightarrow " ^ print_prop b ^ ")"
    | Disj (a , b) -> "(" ^ print_prop a ^ " \vee " ^ print_prop b ^ ")"

(* This is the function which makes the tableau in a string form which is
suitable for LaTeX output with the synttree package.  With synttree, a single
branch from A to B is written [A[B]] and a branching rule from A to B and C is
written [A[B][C]].  Tableau is the French word for table so I named my
tableau-making function 'table'.  I have no idea why I named the helper function
'chair'.  I apologize for the horrible function names. *)

let rec table (l1 : signed list) (l2 : signed list) : string =
  if (dup l1 l2 || all_atoms l1) then "" else chair l1 l2
and
  chair (l1 : signed list) (l2 : signed list) : string =
    match l1 with
    | [] -> ""
    | x :: xs ->
      (match x with
      | T p ->
        (match p with
        | Atom a ->
          (table xs (l2 @ [x])) 
        | Neg a ->
            "[" ^ print_signed (F a) ^ (table (xs @ [F a]) (l2 @ [x])) ^ "]"
        | Conj (a , b) ->
            "[" ^ print_signed (T a) ^ "," ^ print_signed (T b) ^
              (table (xs @ [T a] @ [T b]) (l2 @ [x])) ^
            "]"
        | Disj (a , b) ->
            "[" ^ print_signed (T a) ^ (table (xs @ [T a]) (l2 @ [x])) ^ "]" ^
            "[" ^ print_signed (T b) ^ (table (xs @ [T b]) (l2 @ [x])) ^ "]"
        | Impl (a , b) -> 
            "[" ^ print_signed (F a) ^ (table (xs @ [F a]) (l2 @ [x])) ^ "]" ^
            "[" ^ print_signed (T b) ^ (table (xs @ [T b]) (l2 @ [x])) ^ "]"
        )
      | F p ->
        (match p with
        | Atom a ->
          (table xs (l2 @ [x])) 
        | Neg a -> 
            "[" ^ print_signed (T a) ^ (table (xs @ [T a]) (l2 @ [x])) ^ "]"
        | Disj (a , b) -> 
            "[" ^ print_signed (F a) ^ "," ^ print_signed (F b) ^
              (table (xs @ [F a] @ [F b]) (l2 @ [x])) ^ "]"
        | Impl (a , b) ->
            "[" ^ print_signed (T a) ^ "," ^ print_signed (F b) ^
              (table (xs @ [T a] @ [F b]) (l2 @ [x])) ^ "]"
        | Conj (a , b) ->
            "[" ^ print_signed (F a) ^ (table (xs @ [F a]) (l2 @ [x])) ^ "]" ^
            "[" ^ print_signed (F b) ^ (table (xs @ [F b]) (l2 @ [x])) ^ "]"
        )
      )

(* Basic prop to string printing if you just want REPL output *)

let rec print_aux (s : signed) : string =
  match s with
  | T p -> "T" ^ print_prop2 p
  | F p -> "F" ^ print_prop2 p
and
  print_prop2 (p : prop) : string =
    match p with
    | Atom a -> String.uppercase a
    | Neg a -> "(not " ^ print_prop2 a ^ ")"
    | Conj (a , b) -> "(" ^ print_prop2 a ^ " ^ " ^ print_prop2 b ^ ")"
    | Impl (a , b) -> "(" ^ print_prop2 a ^ " -> " ^ print_prop2 b ^ ")"
    | Disj (a , b) -> "(" ^ print_prop2 a ^ " v " ^ print_prop2 b ^ ")"

(* Stuff you can test! *)
let p1 = Impl(Disj(Atom "a",Atom "b"),Disj(Atom "b",Atom "a"))
let p2 = Impl(Conj(Impl(Atom "a",Atom "b"),Atom "a"),Atom "b")
let p3 = Impl(Conj(Impl(Atom "a",Atom "b"),Neg(Atom "b")),Neg(Atom "a"))
let p4 = Impl(Conj(Impl(Atom "a",Atom "b"),Impl(Atom "b",Atom "c")),Impl(Atom "a",Atom "c"))
let p5 = Impl(Atom "a",Disj(Atom "a",Atom "b"))
let p6 = Impl(Atom "a",Neg(Atom "a"));;

(* This is the function which does everything for you:
Just give it the proposition you want to try and disprove, and it'll write the
LaTeX output to a file for you.  It also runs a mini bash script which
pdflatex's the .tex file and opens the PDF for you so you don't have to do it
yourself. *)

let itt be =
  let file = "message.tex" in
  let oc = open_out file in
  let top =
  "\documentclass{article} 
  \usepackage{amsmath,fullpage,synttree} 
  \\begin{document} 
  \\title{Your Proof} 
  \author{OCaml} 
  \maketitle \n\n" in
  let body =
  "Here is your proposition: \n\n" ^
  "$" ^ (print_prop be) ^ "$" ^ "\n\n" ^
  (solve be) ^ "\n\n" ^
  "\synttree" ^ "[" ^ (print_signed (F be)) ^
  (table [(F be)] []) ^ "]" in
  let bot = "\end{document}" in
  fprintf oc "%s\n" (top ^ body ^ bot);
  close_out oc;
  Sys.command "./run.sh";
