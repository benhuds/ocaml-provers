exception CONFLICT
exception OCCURS
exception UNIFY_FORMULA
exception UNIFICATION_FAILURE
exception SUBST
exception DECOMP
exception ERR

type term =
  | Var of string
  | Const of string
  | Fun of string * term list (* name, arity, args *)

type formula =
  | FRel of string * int * term list (* name, arity, args *)
  | FConj of formula * formula
  | FDisj of formula * formula
  | FImp of formula * formula
  | FNeg of formula
  | FForall of string * formula
  | FExists of string * formula

(* Propositional symbols are relations with arity 0 *)
let pSym (s : string) : formula = FRel (s, 0, [])

(* (∀x. (R(x)) → ∃x. (R(x))) *)
let e1 = FImp ((FForall ("x", (FRel ("R", 1, [Var "x"])))),
               (FExists ("x", (FRel ("R", 1, [Var "x"])))))

let e2 = FImp ((FExists ("x", (FRel ("R", 1, [Var "x"])))),
               (FExists ("x", (FRel ("R", 1, [Var "x"])))))


(* ∀x. ((∃y. (ϕ(y)) ∨ (∃z. (ψ(z)) → ρ(x)))) *)
let e3 =
  FForall ("x",
           FDisj
             ((FExists ("y", FRel ("ϕ", 1, [Var "y"]))),
              (FImp (FExists ("z", FRel ("ψ", 1, [Var "z"])),
                     (FRel ("ρ", 1, [Var "x"])) ))))

let e4 = FNeg (FDisj (FExists ("x", FRel ("P",1,[Var "x"])),
                      FExists ("x", FRel ("Q",1,[Var "x"]))))

let e5 = FImp (FConj (FImp (pSym "P", pSym "Q"), pSym "P"), pSym "Q")

let rec intersperse (sep : 'a) (xs : 'a list) : 'a list =
  match xs with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> x :: sep :: (intersperse sep xs)

let rec showTerm (t : term) : string =
  match t with
  | Var s -> s
  | Const c -> c
  | Fun(f, xs) ->
      f ^ "(" ^ (String.concat "" (intersperse "," (List.map showTerm xs))) ^ ")"

let rec show (x : formula) : string =
  match x with
  | FConj(y , z) -> "(" ^ show y ^ " ∧ " ^ show z ^ ")"
  | FDisj(y , z) -> "(" ^ show y ^ " ∨ " ^ show z ^ ")"
  | FImp(y , z) -> "(" ^ show y ^ " → " ^ show z ^ ")"
  | FNeg y -> "(" ^ "¬" ^ show y ^ ")"
  | FForall(var , y) -> "∀" ^ var ^ ". " ^ "(" ^ show y ^ ")"
  | FExists(var , y) -> "∃" ^ var ^ ". " ^ "(" ^ show y ^ ")"
  | FRel(name , 0 , []) -> name
  | FRel(name , _ , xs) ->
      name ^ "(" ^ (String.concat "" (intersperse "," (List.map showTerm xs))) ^ ")"

let printFormula (x : formula) : unit = (print_string (show x); print_string "\n")

let applyToSubformula (f : formula -> formula) (x : formula) : formula =
  match x with
  | FConj(y, z) -> FConj (f y, f z)
  | FDisj(y, z) -> FDisj (f y, f z)
  | FImp(y, z) -> FImp (f y, f z)
  | FNeg y -> FNeg (f y)
  | FForall(var, y) -> FForall (var, f y)
  | FExists(var, y) -> FExists (var, f y)
  | _ -> x

let rec isQuantifierFree (x : formula) : bool =
  match x with
  | FConj(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FDisj(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FImp(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FNeg y -> isQuantifierFree y
  | FForall(var, y) -> false
  | FExists(var, y) -> false
  | _ -> true

let rec isPrenex (x : formula) : bool =
  match x with
  | FForall(_, y) -> isPrenex y
  | FExists(_, y) -> isPrenex y
  | _ -> isQuantifierFree x

let freshCount : int ref = ref 0

let rec renameTerm (x : term) (old : string) (fresh : string) : term =
  match x with
  | Var s -> Var (if s = old then fresh else s)
  | Const c -> Const c
  | Fun(name, xs) ->
      Fun(name, List.map (fun t -> (renameTerm t old fresh)) xs)

let rec renameFormula (x : formula) (old : string) (fresh : string) : formula =
  match x with
  | FForall(var, y) ->
      if var = old then x else FForall(var, renameFormula y old fresh)
  | FExists(var, y) ->
      if var = old then x else FExists(var, renameFormula y old fresh)
  | FRel(name, a, xs) ->
      FRel(name, a, List.map (fun t -> renameTerm t old fresh) xs)
  | _ -> applyToSubformula (fun y -> renameFormula y old fresh) x

let rec renameBoundedVars (x : formula) : formula =
  match x with
    FForall(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = "_" ^ string_of_int (!freshCount)
      in FForall(fresh, renameFormula y var fresh)
  | FExists(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = "_" ^ string_of_int (!freshCount)
      in FExists(fresh, renameFormula y var fresh)
  | FRel(name, a, xs) -> x
  | _ -> applyToSubformula renameBoundedVars x

let prenexRule (x : formula) : formula =
  match x with
  (* Negation rules *)
    FNeg(FExists(var, y)) -> FForall(var, FNeg(y))
  | FNeg(FForall(var, y)) -> FExists(var, FNeg(y))
  (* Conjunction rules *)
  | FConj(FForall (var, y), z) -> FForall(var, FConj(y, z))
  | FConj(y, FForall (var, z)) -> FForall(var, FConj(y, z))
  | FConj(FExists (var, y), z) -> FExists(var, FConj(y, z))
  | FConj(y, FExists (var, z)) -> FExists(var, FConj(y, z))
  (* Disjunction rules *)
  | FDisj(FForall (var, y), z) -> FForall(var, FDisj(y, z))
  | FDisj(y, FForall (var, z)) -> FForall(var, FDisj(y, z))
  | FDisj(FExists (var, y), z) -> FExists(var, FDisj(y, z))
  | FDisj(y, FExists (var, z)) -> FExists(var, FDisj(y, z))
  (* Implication antecedent rules *)
  | FImp(FForall(var, y), z) -> FExists(var, FImp(y, z))
  | FImp(FExists(var, y), z) -> FForall(var, FImp(y, z))
  (* Implication consequent rules *)
  | FImp(y, FForall(var, z)) -> FForall(var, FImp(y, z))
  | FImp(y, FExists(var, z)) -> FExists(var, FImp(y, z))
  | _ -> x

let rec applyPrenex (x : formula) : formula =
  if isPrenex x then x
  else applyPrenex (prenexRule (applyToSubformula applyPrenex x))

let compose f g x = f (g x)

let toPrenex = compose applyPrenex renameBoundedVars

(* CNF stuff starts here *)

let a = FRel("A",0,[]);;
let b = FRel("B",0,[]);;
let c = FRel("C",0,[]);;
let d = FRel("D",0,[]);;

(* convert to NNF *)
let rec nnf (f : formula) : formula =
  match f with
  | FImp(a , b) -> FDisj(nnf (FNeg a), nnf b)
  | FNeg a ->
    (match a with
    | FNeg p -> nnf p
    | FConj(p , q) -> FDisj(nnf (FNeg p) , nnf (FNeg q))
    | FDisj(p , q) -> FConj(nnf (FNeg p) , nnf (FNeg q))
    | FImp(p , q) -> nnf(FNeg(FDisj((FNeg p) , q)))
    | _ -> f
    )
  | FConj(a , b) -> FConj(nnf a , nnf b)
  | FDisj(a , b) -> FDisj(nnf a , nnf b)
  | FForall(x , t) -> FForall(x , nnf t)
  | FExists(x , t) -> FForall(x , nnf t)
  | _ -> f

let rec cnf (f : formula) : formula =
  match nnf f with
  | FNeg a -> FNeg a
  | FImp(a , b) -> raise ERR
  | FConj(a , b) -> FConj(cnf a , cnf b)
  | FDisj(a , b) ->
    (match cnf a with
    | FConj(a1 , a2) -> FConj(cnf(FDisj(a1 , b)) , cnf(FDisj(a2 , b)))
    | _ ->
      (match cnf b with
      | FConj(b1 , b2) -> FConj(cnf(FDisj(a , b1)) , cnf(FDisj(a , b2)))
      | _ -> FDisj(a , b))
    )
  | _ -> nnf f

(* let toCnf = compose cnf toPrenex *)

(******** UNIFICATION STUFF STARTS HERE *********)

type substitution = (string * term) list

(* use for the conflict rule of unification *)
let conflict (t1 : term) (t2 : term) : bool =
  match (t1,t2) with
  | (Fun (f,l1) , Fun (g,l2)) -> f <> g
  | _ -> false

(* use for the decomposition rule of unification *)
let rec decomp (t1 : term) (t2 : term) : (term * term) list =
  match (t1,t2) with
  | (Fun (f,l1) , Fun (g,l2)) -> decomp_help l1 l2
  | _ -> raise DECOMP
and
  decomp_help (l1 : term list) (l2 : term list) : (term * term) list =
    match (l1 , l2) with
    | ([] , []) -> []
    | (x :: xs , y :: ys) -> (x , y) :: decomp_help xs ys

(* "does t occur in tm?" *)
let rec occurs_free (t : term) (tm : term) : bool =
  match (t,tm) with
  | (Var x,Var y) -> if x = y then true else false
  | (Var x,Const c) -> false
  | (Var x,Fun (f,l)) ->
    if List.mem true (List.map (fun y -> occurs_free (Var x) y) l) then true
else false
  | _ -> false

(* applies a substitution to a term *)
let rec subst (s : substitution) (t : term) : term =
  match t with
  | Var x -> if List.mem_assoc x s then List.assoc x s else Var x
  | Const c -> Const c
  | Fun (f,l) -> Fun (f,List.map (fun x -> subst s x) l)

let apply_substitution (s : substitution) (tms : term list) : term list =
  List.map (fun x -> subst s x) tms

(* applies a substitution to the list of pairs in our specific format *)
let rec apply_list (s : substitution) (tms : (term * term) list) : (term * term) list =
  match tms with
  | [] -> []
  | (x , y) :: xs ->
    let [x' ; y'] = apply_substitution s [x ; y] in
    (x' , y') :: apply_list s xs

(* composes two substitutions *)
let compose_substitution (g : substitution) (f : substitution) : substitution =
  let f' = List.filter (fun (x',t') -> not (List.mem_assoc x' g)) f in
  let gf = (List.map (fun (x',t') -> (x',subst f t')) g) @ f' in
  List.filter (fun (x',t') -> not (Var x' = t')) gf

(* returns a substitution for two terms *)
let rec find_subst (a : term) (b : term) : substitution =
  match (a,b) with
  | (Var x,Var y) -> if x = y then [] else [x,Var y]
  | (Var x,_) -> if occurs_free (Var x) b then raise OCCURS else [x,b]
  | (_,Var y) -> if occurs_free (Var y) a then raise OCCURS else [y,a]
  | _ -> raise SUBST

let rec subst_formula_possible (f : formula) (g : formula) : substitution option =
  match (f , g) with
  | (FRel(name1 , ar1 , args1) , FRel(name2 , ar2 , args2)) ->
    if name1 <> name2 then None
    else if ar1 <> ar2 then None
    else
    (match (args1 , args2) with
    | ([] , []) -> None
    | (x :: xs , y :: ys) -> Some (find_subst x y)
    )
  | _ -> raise SUBST

(* this is the real unification algorithm.
inversion rules are folded into the implementation.
*)
let rec unif (l : (term * term) list) (s : substitution) : substitution =
  match l with
  | [] -> s
  | (x , y) :: xs ->
    if x = y then unif xs s else
    if conflict x y then raise CONFLICT else
    (match (x , y) with
    | (Var i , _) -> let s' = compose_substitution s (find_subst x y) in
        if occurs_free (Var i) y then raise OCCURS else unif (apply_list s' xs) s'
    | (_ , Var j) -> let s' = compose_substitution s (find_subst x y) in
        if occurs_free (Var j) x then raise OCCURS else unif (apply_list s' xs) s'
    | (Fun (f , l1) , Fun (g , l2)) -> unif (List.append (decomp x y) xs) s
    | _ -> raise UNIFICATION_FAILURE
    )

let rec zip (l1 : 'a list) (l2 : 'a list) : ('a * 'a) list =
  match (l1 , l2) with
  | ([] , []) -> []
  | (x :: xs , y :: ys) -> (x , y) :: zip xs ys

let rec unify_formula' (f1 : formula) (f2 : formula) (s : substitution) : substitution option =
  match (f1 , f2) with
  | (FRel(name1 , ar1 , args1) , FNeg(FRel(name2 , ar2 , args2))) ->
    let k = zip args1 args2 in
    Some (unif k [])
  | (FNeg(FRel(name1 , ar1 , args1)) , FRel(name2 , ar2 , args2)) ->
    let k = zip args1 args2 in
    Some (unif k [])
  | _ -> raise UNIFY_FORMULA

let unify_formula (f1 : formula) (f2 : formula) : substitution option = unify_formula' f1 f2 []

(* basic printing stuff *)
let rec print_subst (s : substitution) : string =
  match s with
  | [] -> ""
  | [(x,t)] -> print_term(t)^"/"^x
  | (x,t)::xs -> print_term(t)^"/"^x^","^(print_subst xs)
and
  print_term (t : term) : string =
    match t with
    | Var x -> String.uppercase x
    | Const c -> c
    | Fun(f,l) -> f^"("^(print_list l)^")"
and
  print_list (l : term list) : string =
    match l with
    | [] -> ""
    | [x] -> print_term x
    | (x::xs) -> (print_term x)^","^(print_list xs)

(* this is the function you run for unification. initializes everything for you.
a set is of the form (t_1=u_1,...,t_n=u_n) but we will just represent this as a
list of pairs [(t_1,u_1),...,(t_n,u_n)] where t_i,u_i are terms.
will return the substitution or raise the appropriate exception if fail.
Notation: constants are lowercase, variables are uppercase.
*)
let unification (l : (term * term) list) : string =
  let s = unif l [] in
  "{"^(print_subst s)^"}"

(********** RESOLUTION STUFF STARTS HERE **********)

(* SKOLEMIZATION STUFF *)

(* applies a substitution to a formula *)
let rec subst_formula (f : formula) (s : substitution) : formula =
  match f with
  | FRel(x , arity , args) -> FRel(x , arity , apply_substitution s args)
  | FNeg a -> FNeg (subst_formula a s)
  | FImp(a , b) -> FImp(subst_formula a s , subst_formula b s)
  | FConj(a , b) -> FConj(subst_formula a s , subst_formula b s)  
  | FDisj(a , b) -> FDisj(subst_formula a s , subst_formula b s)
  | FForall(x , f') -> FForall(x , subst_formula f' s)
  | FExists(x , f') -> FExists(x , subst_formula f' s)

(* eliminate existential quantifiers by skolemization. keeps track of list of
variables bound by universal quantifiers before existential is seen *)
let rec skolem' (f : formula) (l : term list) : formula =
  match f with
  | FForall(x , f') -> FForall(x , (skolem' f' (l @ [Var x])))
  | FExists(x , f') ->
    let () = freshCount := (!freshCount) +1 in
    let str = "f_" ^ string_of_int(!freshCount) in
    let s = [(x , Fun(str , l))] in
    skolem' (subst_formula f' s) l
  | _ -> f

let skolem (f : formula) : formula = skolem' f []

(* eliminate universal quantifiers by using metavariables *)
let rec meta (f : formula) : formula =
  match f with
  | FForall(x , f') ->
    let () = freshCount := (!freshCount) +1 in
    let str = "X_" ^ string_of_int(!freshCount) in
    let s = [(x , Var(str))] in
    meta (subst_formula f' s)
  | _ -> f (* should already be in prenex and not have any existentials *)

(* remove quantifiers from formula in prenex nf *)
let remove_quantifiers = compose meta skolem

(* convert to prenex, then remove quantifiers, then convert to cnf *)
let clean = compose cnf (compose remove_quantifiers toPrenex)

(* turns cnf, quantifier-free formulae into set notation *)
let rec getup (f : formula) : (formula list) list =
  match f with
  | FConj(a , b) -> (getup a) @ (getup b)
  | FDisj(a , b) -> [(standup a) @ (standup b)]
  | _ -> [[f]]
and
  standup (f : formula) : formula list =
    match f with
    | FDisj(a , b) -> (standup a) @ (standup b)
    | _ -> [f]

let negate (x : formula) : formula =
  match x with
  | FNeg f -> f
  | _ -> FNeg x

let rec can_unify (y : formula) (x : formula list) : substitution option =
  match x with
  | [] -> None
  | x' :: xs ->
    (match unify_formula y x' with
    | None -> can_unify y xs
    | Some v -> Some v
    )

(* collect free variables from terms/formulae *)
let rec fv (t : term) : string list =
  match t with
  | Var x -> [x]
  | Const c -> []
  | Fun(f , l) -> fvlist l
and
  fvlist (l : term list) : string list =
    match l with
    | [] -> []
    | x :: xs -> fv x @ fvlist xs

let rec fvformula (f : formula) : string list =
  match f with
  | FRel(name , ar , args) -> fvlist args
  | FNeg(FRel(name , ar , args)) -> fvlist args
  | _ -> raise ERR

let rec collect_fv (l : formula list) : (string list) =
  match l with
  | [] -> []
  | x :: xs -> fvformula x @ collect_fv xs

(* make an arbitrary substitution to rename free variables *)
let rec make_subst (l : string list) : substitution =
  let () = freshCount := (!freshCount) +1 in
  let str = "_" ^ string_of_int(!freshCount) in
  match l with
  | [] -> []
  | x :: xs -> (x , Var(x ^ str)) :: make_subst xs

let rec del (el : 'a) (l : 'a list) : 'a list =
  match l with
  | [] -> []
  | x :: xs -> if el = x then xs else x :: (del el xs)

(* resolution rule *)
let rec resolve' (xs : formula list) (ys : formula list) : (substitution * formula) option =
  match xs with
  | [] -> None
  | x :: xs' ->
    (match can_unify x ys with
    | None -> resolve' xs' ys
    | Some s -> Some (s , x)
    )

let rec resolve (xs : formula list) (ys : formula list) : (formula list) option =
  let s0 = make_subst (collect_fv xs) in
  match (resolve' (List.map (fun k -> subst_formula k s0) xs) ys) with
  | None -> None
  | Some (s , p) ->
    let p' = subst_formula p s in
    let q = subst_formula (negate p) s in
    let k = List.map (fun f -> subst_formula f s) ((List.map (fun y -> subst_formula y s0) xs) @ ys) in
    Some (del p' (del q k))

(* main resolution algorithm, tries to resolve clauses until reach 'box'
(returns true), or failed state (return false or raise appropriate exception) *)
let rec alg (n : (formula list) list) (o : (formula list) list) : bool =
  match n with
  | [] -> false
  | x :: xs -> alg_helper x (xs @ o)
and
alg_helper (l : formula list) (no : (formula list) list) : bool =
  (match no with
  | [] -> false
  | x :: xs ->
    (match resolve l x with
    | None -> alg_helper l xs
    | Some fl ->
      (match fl with
      | [] -> true
      | _ -> alg (fl :: xs) (x :: no)
      )
    )
  )

(* gets a formula, turns it into PNF, skolemizes and eliminates universal
quantifiers, converts to cnf, then makes into set notation *)
let prepare (f : formula) : (formula list) list = getup (clean f)

(* this is the main function to run. sorry it doesn't have support for a sequent
of the form p |- q at the moment; you can instead just convert to |- p -> q.
basically takes your formula you want to resolve, converts it into set notation
using the methods discussed in class, and runs the resolution algorithm until it
reaches empty set (true) or finds an error like during unification. some
examples are below.
*)
let run (f : formula) : bool =
  let q = prepare (negate f) in alg q []

(* random testing stuff *)

(* example from class *)
(* rhs of sequent *)
let r1 = FExists("x" , FRel("P" , 1 , [Var "x"]));;
let r2 = FExists("x" , FRel("Q" , 1 , [Var "x"]));;
let r = FDisj(r1 , r2) ;;
(* lhs of sequent *)
let l1 = FRel("P" , 1 , [Var("x")]);;
let l2 = FRel("Q" , 1 , [Var("x")]);;
let l = FExists("x" , FDisj(l1 , l2));;
(* just try "run FImp(l , r)" at console *)

(* exists implies forall, or vice versa*)
let a1 = FExists("x" , FRel("P" , 1 , [Var "x"]));;
let a2 = FForall("x" , FRel("P" , 1 , [Var "x"]));;
let aaa = FImp (a1 , a2);;
let aaa' = FImp (a2 , a1);;

(* drinker's paradox *)
let d1 = FForall("x" , FRel("D" , 1 , [Var "x"]));;
let d = FExists("y" , FImp(FRel("D" , 1 , [Var "y"]) , d1));;

