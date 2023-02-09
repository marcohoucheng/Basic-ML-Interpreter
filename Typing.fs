(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list // tyvar = int

// need to make a version of this in schemes
let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt))) 
]

// type scheme = Forall of tyvar Set * ty

let gamma0_sch = [
    ("+", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
]


// Substitution
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
        // For all tyvar in tvs (Set), if in s then remove them
        // Loop through tvs, if element in s (first element) then remove
        // Loop through tvs, exclude them in s.
        // s, s1 are subst (list of tyvar * ty)
        // tvs is alpha_bar in notes, type tyvar Set
        // let s1 = List.filter (fun (x, _) -> not (List.contains x s)) (Set.toList tvs)
        let s1 = List.filter (fun (x, _) -> not (Set.contains x tvs)) s
        Forall (tvs, apply_subst s1 t)

// Returns a scheme env = (string * scheme) list
let apply_subst_scheme_env (s : subst) (env : scheme env) : scheme env =
    List.map (fun (s1, sch) -> s1, apply_subst_scheme s sch) env
    
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

// ftv (Sets)
let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyVar tv -> Set.singleton tv
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    // | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts

// let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs
let freevars_scheme (Forall (tvs, t)) = Set.difference (freevars_ty t) tvs

let freevars_scheme_env (env : scheme env) =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env
// let freevars_scheme_env (env : scheme env) =
//    Set.fold (fun set (_, sch) -> Set.union set (freevars_scheme sch)) Set.empty env

// Composition
let rec compose_subst (s2 : subst) (s1 : subst) : subst =  // s2 @ s1
    // type subst = (tyvar * ty) list
    // we have 2 list, aim to make a new one
    // lists look like [1 int, 2 int, ...]
    // if first element of 2 list are the same, then merge them in the new list
    // otherwise
    
    // loop through list 2, see if 1st element exists in list 1 then...
    // check the second element is the same
    // if it doesn't exist in list 1, then we have...
    // list 2 [0], apply_sub(list2[1], subst1)
    let map_temp (tvs2, t2) =
        let res = List.tryFind (fun (tvs, _) -> tvs = tvs2) s1 // map this to s2
        match res with
        | None -> tvs2, t2
        | Some (tvs_r, t_r) -> if t2 = t_r
                                then tvs2, apply_subst s1 t2
                                else type_error "cannot unify as %O is mapped to both %O and %O" tvs_r t_r t2
        // | Some (_, t_r) when t2 = t_r -> tvs2, apply_subst s1 t2
        // | Some (tvs_r, t_r) when t2 <> t_r -> type_error "cannot unify as %O is mapped to both %O and %O" tvs_r t_r t2
    // end result s3 @ s1
    let s3 = List.map map_temp s2
    compose_subst s3 s1

// Unification
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

let mutable counter = -1;

let fresh() : ty =
    printf "fresh triggered \n"
    counter <- counter + 1
    TyVar counter

// Instantation
(*
let rec inst_org (Forall (tvs, t)) : ty =
    let freeVars = freevars_ty t
    let toBeRefresh = Set.intersect freeVars tvs
    let toBeRefresh_l = Set.toList toBeRefresh
    // build up a substitution mapping each of the type variable that needs to
    // be refresh, in a new fresh type type variable
    let s = List.map (fun v -> (v, fresh)) toBeRefresh_l
    apply_subst s t
*)

let rec inst (Forall (tvs, t)) =
    match t with
    | TyName _ -> t
    | TyVar tv -> if (Set.contains(tv) tvs) then fresh() else TyVar tv
    // | TyVar tv when not(Set.contains(tv) tvs) -> TyVar tv
    // | TyVar tv when (Set.contains(tv) tvs) -> fresh()
    | TyArrow (t1, t2) -> TyArrow (inst (Forall (tvs, t1)), inst (Forall (tvs, t2)))
    | TyTuple ts -> let temp = List.map (fun t -> inst (Forall (tvs, t))) ts
                    TyTuple temp
    // | _ -> type_error "Instantiation failed"

// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    printf "typeinfer_expr called \n"
    // scheme env = (string * scheme) list
    match e with
    // | Lit (Lint _) -> TyInt, subst Empty _ integer
    | Lit (LInt _) -> TyInt, []
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | Var x ->
        printf "typeinfer_expr called Var x \n"
        let res = List.tryFind (fun (y, _) -> x = y) env // (name, ty) and we only care about the name
        let t, s = match res with
                   | None -> type_error "No scheme available for the variable %O\n" x
                   | Some (_, sch) -> inst(sch), [] // inst (Forall (tvs, t)) : ty
        t, s

    // | Lambda (x, None , e)
    | Lambda (x, tyo, e) ->
        printf "typeinfer_expr called Lambda\n"
        let tyo1 = match tyo with
                   | Some tyo1 -> tyo1
                   | None -> fresh()
        let sch = Forall (Set.empty, tyo1)
        let new_env = (x, sch) :: env
        let t1, s1 = typeinfer_expr new_env e
        let t2 = apply_subst s1 tyo1
        TyArrow(t2, t1), s1
        
    | App (e1, e2) ->
        printf "typeinfer_expr called App\n"
        let t1, s1 = typeinfer_expr env e1
        let env1 = apply_subst_scheme_env s1 env
        let t2, s2 = typeinfer_expr env1 e2
        // unify (t1 : ty) (t2 : ty) : subst
        let alpha = fresh()
        let s3 = unify t1 (TyArrow(t2, alpha))
        // apply_subst (s : subst) (t : ty) : ty
        let t = apply_subst s3 alpha
        t, compose_subst s3 s2

    | Let (x, None, e1, e2) ->
        printf "typeinfer_expr called Let None\n"
        let t1, s1 = typeinfer_expr env e1
        // alpha_bar (Set)
        // this env is theta, we need to
        let tvs = Set.difference (freevars_ty t1) (freevars_scheme_env env)
        // sch = sigma (type scheme of tyvar Set * ty)
        // tvs (alpha_bar) is a set
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst s2 s1
    
    | Let (x, Some tyo, e1, e2) ->
        printf "typeinfer_expr called Let Some\n"
        let t1, s0 = typeinfer_expr env e1
        // Unify tyo and t1
        let s1 = compose_subst s0 (unify t1 tyo)
        // alpha_bar (Set)
        // this env is theta, we need to
        let tvs = Set.difference (freevars_ty t1) (freevars_scheme_env env)
        // sch = sigma (type scheme of tyvar Set * ty)
        // tvs (alpha_bar) is a set
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst s2 s1
    
    | IfThenElse (e1, e2, e3o) ->
        printf "typeinfer_expr called ITE\n"
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

    | Tuple es -> // makes no sense
        printf "typeinfer_expr called Tuple\n"
        // loop through es list
        // start with s0 = [] and env
        // env_0 = apply_subst_scheme_env s0 env
        // t1, s1 = typeinfer_expr env0 e1
        let f (t, s) e =
            let env = apply_subst_scheme_env s env
            let t1, s1 = typeinfer_expr env e
            // cannot use :: because LHS may not be a single element
            t @ List.singleton(apply_subst s1 t1), compose_subst s1 s
        let x = []
        let y = []
        let t, s = List.fold f (x, y) es
        TyTuple t, s

    | LetRec (f, Some tfo, e1, e2) ->
        printf "typeinfer_expr called Let Rec\n"
        let alpha = fresh()
        let sch = Forall (Set.empty, alpha)
        let t1, s0 = typeinfer_expr ((f, sch) :: env) e1
        let s1 = compose_subst s0 (unify t1 tfo)
        let env1 = apply_subst_scheme_env s1 env
        let tvs = Set.difference (freevars_ty t1) (freevars_scheme_env env1)
        let sch1 = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((f, sch1) :: env1) e2
        t2, compose_subst s2 s1
    
    ///////////////////////////////////////////////////////////
    
    (*
    // Int
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify TyInt t1
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        let s5 = unify TyInt t2
        let s6 = compose_subst s5 s4
        TyInt, s6 // t2, s6
    *)

    // Int & Float
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = match t1, op with
                 | TyInt, _ -> unify TyInt t1
                 | TyFloat, _ -> unify TyFloat t1
                 | _, op -> type_error "type %O not supported by the operation %O" t1 op
        // let s2 = unify TyInt t1
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        // let s5 = unify TyInt t2
        let s5 = match t1, t2 with
                 | TyInt, TyInt -> unify TyInt t2
                 | TyFloat, TyInt
                 | TyFloat, TyFloat -> unify TyFloat t2
                 | TyInt, TyFloat ->
                        let s2 = unify TyFloat t1
                        let s3 = compose_subst s2 s1
                        let env1 = apply_subst_scheme_env s3 env
                        let t2, s4 = typeinfer_expr env1 e2
                        unify TyFloat t2
                 | _ -> type_error "cannot unify %O and %O" t1 t2
        let s6 = compose_subst s5 s4
        let ty_out = match t1, t2 with
                     | TyInt, TyInt -> TyInt
                     | TyFloat, TyInt
                     | TyFloat, TyFloat
                     | TyInt, TyFloat -> TyFloat
                     | _, _ -> type_error "Types %O and %O incompatible with the %O operator" t1 t2 op
     
        ty_out, s6

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify TyFloat t1
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        let s5 = unify TyFloat t2
        let s6 = compose_subst s5 s4
        apply_subst s6 t2, s6

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify TyBool t1
        let s3 = compose_subst s2 s1
        let env1 = apply_subst_scheme_env s3 env
        let t2, s4 = typeinfer_expr env1 e2
        let s5 = unify TyBool t2
        let s6 = compose_subst s5 s4
        (apply_subst s6 t2), s6

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


    | _ -> failwithf "not implemented"


(*
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
*)