(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list // tyvar = int

// Initial environment for type check and type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
]

// type scheme = Forall of tyvar Set * ty
let gamma0_sch = [
    ("+", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("*", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("/", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("%", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("=", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<=", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    (">", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("=>", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<>", Forall(Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("and", Forall(Set.empty, TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("or", Forall(Set.empty, TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("not", Forall(Set.empty, TyArrow (TyBool, TyBool)))
    ("+", Forall(Set.empty, TyArrow (TyInt, TyInt)))
    ("-", Forall(Set.empty, TyArrow (TyInt, TyInt)))

    (*
    ("+.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("-.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("*.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("/.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("%", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("=.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<=.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    (">.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("=>.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<>.", Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("+.", Forall(Set.empty, TyArrow (TyFloat, TyFloat)))
    ("-.", Forall(Set.empty, TyArrow (TyFloat, TyFloat)))
    *)
]

// Used in Unification and Type Inference

let check_type (t1 : ty) (t2 : ty) : int =
    match (t1, t2) with
    | TyInt, TyInt -> 0
    | TyInt, TyFloat
    | TyFloat, TyInt
    | TyFloat, TyFloat -> 1
    | TyString, TyString -> 2
    | _, _ -> 3

// Substitution
//

let rec apply_subst (s : subst) (t : ty) : ty = // t
    match t with
    | TyName _ -> t
    | TyVar tv ->
        let res = List.tryFind (fun (tv1, _) -> tv1 = tv) s
        match res with
        | Some (_, t1) -> t1
        | None -> t
        (*
        try
            let _, t1 = List.find (fun (tv1, _) -> tv1 = tv) s
            in
                t1
        with KeyNotFoundException -> t
        *)
    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)
    | TyTuple ts -> TyTuple (List.map (apply_subst s) ts)

let apply_subst_scheme (s : subst) (sch : scheme) : scheme =
    match sch with
    | Forall (tvs, t) ->
        // For all tyvar in tvs (Set), if in s (subst) then remove them
        // Loop through tvs, exclude them in s
        // tvs is alpha_bar in notes, type tyvar Set
        // let s1 = List.filter (fun (x, _) -> not (List.contains x s)) (Set.toList tvs)
        let s1 = List.filter (fun (x, _) -> not (Set.contains x tvs)) s
        Forall (tvs, apply_subst s1 t)

// Returns a scheme env = (string * scheme) list
let apply_subst_scheme_env (s : subst) (env : scheme env) : scheme env =
    List.map (fun (s1, sch) -> s1, apply_subst_scheme s sch) env


//  Free type variables
//

let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyVar tv -> Set.singleton tv
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    // | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = Set.difference (freevars_ty t) tvs

let freevars_scheme_env (env : scheme env) =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// Composition
//

let compose_subst (s2 : subst) (s1 : subst) : subst =
    let s3 = List.map (fun (tvs, t) -> (tvs, apply_subst s2 t)) s1
    s3 @ s2

(*
let compose_subst (s2 : subst) (s1 : subst) : subst =  // s2 @ s1
    let map_temp (tvs2 : tyvar, t2 : ty) = // input s2
        let res = List.tryFind (fun (tvs, t) -> tvs = t2) s1 // check s2 against s1
        match res with
        | Some (tvs_r, t_r) -> tvs2, t_r // subst * ty
        | None -> tvs2, t2 // if key not exists in s1, keep s2 key:value pairs
    let s3 = List.map map_temp s2 // check and modify s2 and keep s1
    s3 @ s1
*)

// Unification
//

let rec unify (t1 : ty) (t2 : ty) : subst = // (tyvar * ty) list
    match (t1, t2) with
    | TyName s1, TyName s2 when s1 = s2 -> []
    | TyName s1, TyName s2 when check_type t1 t2 < 2 -> [] // Only Int and Float
    | TyVar tv, t
    | t, TyVar tv -> [tv, t]
    | TyArrow (t1, t2), TyArrow (t3, t4) ->
        let s = unify t1 t3
        let t5 = apply_subst s t2
        let t6 = apply_subst s t4
        compose_subst (unify t5 t6) s
    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
    | TyTuple ts1, TyTuple ts2 when List.length ts1 <> List.length ts2 ->
        type_error "cannot unify tuples of different length, %O and %O" t1 t2
    | _ -> type_error "cannot unify types %O and %O" t1 t2

// Instantation
//

let mutable counter = -1

let fresh() : ty =
    counter <- counter + 1
    TyVar counter

(*
let rec inst (s:scheme) : ty =
    match s with
    | Forall (uqv, t) ->
        let freeVars = freevars_ty t
        let toBeRefresh = Set.intersect freeVars (Set uqv)
        // build up a substitution mapping each of the type variable that needs to
        // be refresh, in a new fresh type type variable
        let sub = List.map (fun v -> (v, fresh())) (List.sort (Set.toList toBeRefresh))
        apply_subst sub t //apply_subst (s : subst) (t : ty)
*)

//(*
let rec inst (Forall (tvs, t)) =
    match t with
    | TyName _ -> t
    | TyVar tv -> if (Set.contains(tv) tvs)
                  then fresh()
                  else TyVar tv
    | TyArrow (t1, t2) -> TyArrow (inst (Forall (tvs, t1)), inst (Forall (tvs, t2)))
    | TyTuple ts -> let tuple = List.map (fun t -> inst (Forall (tvs, t))) ts
                    TyTuple tuple
//*)
// unexpected error: eval_expr: unsupported expression: ("hello",  3,  4) [AST: Tuple [Lit (LString "hello"); Lit (LInt 3); Lit (LFloat 4.0)]]
// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    // scheme env = (string * scheme) list
    match e with
    | Lit (LInt _) -> TyInt, []
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | Var x ->
        let res = List.tryFind (fun (y, _) -> x = y) env
        match res with
        | None -> type_error "No scheme available for the variable %O\n" x
        | Some (_, sch) -> inst(sch), []

    | Lambda (x, tyo, e) ->
        let tyo1 = match tyo with
                   | Some tyo1 -> tyo1
                   | None -> fresh()
        let sch = Forall (Set.empty, tyo1)
        let env1 = (x, sch) :: env
        let t2, s1 = typeinfer_expr env1 e
        let t1 = apply_subst s1 tyo1
        let t = TyArrow(t1, t2)
        t, s1
        
    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let env1 = apply_subst_scheme_env s1 env
        let t2, s2 = typeinfer_expr env1 e2
        let alpha = fresh()
        let s3 = unify t1 (TyArrow(t2, alpha))
        let t = apply_subst s3 alpha
        let s4 = compose_subst s3 s2
        t, s4
    
    | Let (x, tyo, e1, e2) ->
        let t1, s0 = typeinfer_expr env e1
        let s1 = match tyo with
                 | Some tyo1 -> compose_subst s0 (unify t1 tyo1)
                 | None -> s0
        let env1 = apply_subst_scheme_env s1 env
        let tvs = Set.difference (freevars_ty t1) (freevars_scheme_env env1)
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        let s3 = compose_subst s2 s1
        t2, s3
    
    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        let s5 = compose_subst s4 s3
        match e3o with
        | None ->
            let s6 = unify t2 TyUnit
            let s7 = compose_subst s6 s5
            t2, s7
        | Some e3 ->
            let env2 = apply_subst_scheme_env s5 env1
            let t3, s6 = typeinfer_expr env2 e3
            let s7 = compose_subst s6 s5
            let s8 = unify (apply_subst s7 t2) (apply_subst s7 t3)
            let t = apply_subst s8 t2
            let s9 = compose_subst s8 s7
            t, s9

    | Tuple es ->
        let f (t, s) e =
            let env = apply_subst_scheme_env s env
            let t1, s1 = typeinfer_expr env e
            // cannot use :: because LHS may not be a single element
            t @ List.singleton(apply_subst s1 t1), compose_subst s1 s
        let t, s = List.fold f ([], []) es
        TyTuple t, s

    | LetRec (f, tyo, e1, e2) ->
        let alpha = fresh()
        let sch = Forall (Set.empty, alpha)
        let t1, s0 = typeinfer_expr ((f, sch) :: env) e1
        let s1 = match tyo with
                 | Some tyo1 -> compose_subst s0 (unify tyo1 t1)
                 | None -> s0
        let env1 = apply_subst_scheme_env s1 env
        let tvs = Set.difference (freevars_ty t1) (freevars_scheme_env env1)
        let sch1 = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((f, sch1) :: env) e2
        let s3 = compose_subst s2 s1
        t2, s3
    
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" | "<" | "<=" | ">" | ">=" | "=" | "<>" | "and" | "or" as op), e2) ->
        typeinfer_expr env (App (App (Var op, e1), e2))
    | BinOp (_, op, _) ->
        unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op
    | UnOp ("not" | "-" as op, e) ->
        typeinfer_expr env (App (Var op, e))
    | UnOp (op, _) ->
        unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op
    
    
    (*
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        printf "typeinfer_expr called BinOp\n"
        let t1, s1 = typeinfer_expr env e1
        let t2, s2  = typeinfer_expr env e2
        let res = check_type t1 t2
        printf "t1 and t2 are %O and %O\n" t1 t2
        printf "s1 and s2 are %O and %O\n" s1 s2
        printf "matching res = %O\n" res
        match res with
        | 0 -> // int
            let s2 = unify TyInt t1
            let s3 = compose_subst s2 s1
            let env1 = apply_subst_scheme_env s3 env
            let t2, s4 = typeinfer_expr env1 e2
            let s5 = unify TyInt t2
            let s6 = compose_subst s5 s4
            printf "Int, returns %O" s6
            TyInt, s6
        | 1 -> // float
            let s2 = unify TyFloat t1
            let s3 = compose_subst s2 s1
            let env1 = apply_subst_scheme_env s3 env
            let t2, s4 = typeinfer_expr env1 e2
            let s5 = unify TyFloat t2
            let s6 = compose_subst s5 s4
            printf "Float, returns %O" s6
            TyFloat, s6
        | 2 -> match op with // string
               | "+" -> 
                    let s2 = unify TyString t1
                    let s3 = compose_subst s2 s1
                    let env1 = apply_subst_scheme_env s3 env
                    let t2, s4 = typeinfer_expr env1 e2
                    let s5 = unify TyString t2
                    let s6 = compose_subst s5 s4
                    printf "String, returns %O" s6
                    TyString, s6
               | _ -> type_error "operator %O cannot be applied to type %O" op t1
        | _ ->
            printf "BinOp matched with nothing\nWe have t1 = %O and t2 = %O\n" t1 t2
            let s0 = unify t2 t1
            printf "Unified as %O\n" s0
            printf "Which subs to compose? s1 = %O and s2 = %O\n" s1 s2
            let s3 = compose_subst s0 (compose_subst s2 s1)
            let t3 = apply_subst s3 t1
            printf "type %O and subst %O\n" t3 s3
            t3, s3

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = unify t1 t2
        printf "s3 is %O\n" s3
        TyBool, s3

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify TyBool t1
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        let s5 = unify TyBool t2
        let s6 = compose_subst s5 s4
        TyBool, s6

    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t1, s1 = typeinfer_expr env e
        let s2 = unify TyBool t1
        apply_subst s2 t1, s2

    | UnOp ("-", e) ->
        let t1, s1 = typeinfer_expr env e
        let s2 = match t1 with
                 | TyInt -> unify TyInt t1
                 | TyFloat -> unify TyFloat t1
                 | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t1)
        apply_subst s2 t1, s2

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op
    *)

    | _ -> failwithf "not implemented"


// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt // _ means remove the "number"
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit
    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env // (name, ty) and we only care about the name
        t
    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e // e shadowed, use line L67 not 52
        TyArrow (t1, t2)
    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)
    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> () // do nothing
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2 // extend the environment with type(x) = t1
    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2
    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)
    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | TyString, TyString -> TyString
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool
    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool
    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op
    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)
    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op
    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e