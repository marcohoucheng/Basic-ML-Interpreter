(*
* TinyML
* Typing.fs: typing algorithms
*)

// This is only a type checking

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt))) 
]

// TODO: Composition
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2

// Unification (Done)
let rec unify (t1 : ty) (t2 : ty) : subst = // []
    match (t1, t2) with
    | TyName s1, TyName s2 when s1 = s2 -> []
    
    | TyVar tv, t
    | t, TyVar tv -> [tv, t]
    
    | TyArrow (t1, t2), TyArrow (t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)

    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)

    | TyTuple ts1, TyTuple ts2 when List.length ts1 <> List.length ts2 ->
        type_error "cannot unify tuples of different length, %O and %O" t1 t2

    | _ -> type_error "cannot unify types %O and %O" t1 t2

// Substitution
let rec apply_subst (s : subst) (t : ty) : ty = // t
    match t with
    | TyName _ -> t
    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)

    | TyVar tv ->
        try
            let _, t1 = List.find (fun (tv1, _) -> tv1 = tv) s
            in
                t1
        with KeyNotFoundException -> t

    | TyTuple ts -> TyTuple (List.map (apply_subst s) ts)

// Free variables
let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyVar tv -> Set.singleton tv
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    // | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts
    | TyTuple ts -> List.fold (fun r t -> Set.union r (freevars_ty t)) Set.empty ts

    // ForAll: ftv(ForAll a_bar,gamma) -> ftv(gamma)\{a_bar}
    | Forall (tvs, t) -> Set.difference (freevars_ty t) tvs
    
    | None -> Set.empty

    // ftv(Gamma,(x:tau)) -> Set.union ftv(tau) ftv(Gamma)
    | env -> None

// no need to match, only one option
// type scheme = Forall of tyvar Set * ty // list is alpha_bar
// tvs is a list
// let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs
let freevars_scheme (Forall (tvs, t)) = Set.difference (freevars_ty t) tvs

// let freevars_scheme_env env =
//    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env
let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> Set.union r (freevars_scheme sch)) Set.empty env

(*
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - (Set.ofList tvs)

let rec freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)
*)

// type inference
//



// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    // | Lit (Lint _) -> TyInt, subst Empty _ integer
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    //9 Jan, top down style coding, start from big block to small block
    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        // we haven't defined those functions below yet, define above in a minute
        // _ty operates on ty, etc.
        // No overloading in F#
        // Assume 2 functions exist and they return the same type which - can be used
        // freevars should return sets (so - can be used and easy to be implementated)
        // set doesn't allow duplicates like maths
        let tvs = freevars_ty t1 - freevars_scheme_env env // alpha_bar
        let sch = Forall (tvs, t1) // sigma
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst s2 s1
        // Add unification

    | _ -> failwithf "not implemented"

    // Let uses generalisation
    // Application uses unification


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
