﻿(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    | LetRec (f, _, e1, e2) -> 
        let v1 = eval_expr env e1
        let env1 = match v1 with
                     | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
                     | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        eval_expr ((f, env1) :: env) e2

    | BinOp (e1, "+", e2) -> binop_plus (+) (+) (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop (-) (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop (*) (*) env e1 e2
    | BinOp (e1, "/", e2) -> binop (/) (/) env e1 e2
    | BinOp (e1, "%", e2) -> binop (%) (%) env e1 e2
    
    | BinOp (e1, "<", e2)  -> binop_bool (<)  (<)  env e1 e2
    | BinOp (e1, "<=", e2) -> binop_bool (<=) (<=) env e1 e2
    | BinOp (e1, ">", e2)  -> binop_bool (>)  (>)  env e1 e2
    | BinOp (e1, ">=", e2) -> binop_bool (>=) (>=) env e1 e2
    | BinOp (e1, "=", e2)  -> binop_bool (=)  (=)  env e1 e2
    | BinOp (e1, "<>", e2) -> binop_bool (<>) (<>) env e1 e2

    | BinOp (e1, "and", e2) -> binop_bools (&&) env e1 e2
    | BinOp (e1, "or", e2)  -> binop_bools (||) env e1 e2

    | UnOp ("not", e) -> unop_b (not) env e
    | UnOp ("+", e) -> unop_p (+) env e
    | UnOp ("-", e) -> unop_n (-) env e
//
    | BinOp (e1, "+.", e2) -> binop_plus (+) (+) (+) env e1 e2
    | BinOp (e1, "-.", e2) -> binop (-) (-) env e1 e2
    | BinOp (e1, "*.", e2) -> binop (*) (*) env e1 e2
    | BinOp (e1, "/.", e2) -> binop (/) (/) env e1 e2
    | BinOp (e1, "%.", e2) -> binop (%) (%) env e1 e2
    
    | BinOp (e1, "<.", e2)  -> binop_bool (<)  (<)  env e1 e2
    | BinOp (e1, "<=.", e2) -> binop_bool (<=) (<=) env e1 e2
    | BinOp (e1, ">.", e2)  -> binop_bool (>)  (>)  env e1 e2
    | BinOp (e1, ">=.", e2) -> binop_bool (>=) (>=) env e1 e2
    | BinOp (e1, "=.", e2)  -> binop_bool (=)  (=)  env e1 e2
    | BinOp (e1, "<>.", e2) -> binop_bool (<>) (<>) env e1 e2

    | UnOp ("+.", e) -> unop_p (+) env e
    | UnOp ("-.", e) -> unop_n (-) env e

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and binop_plus op_int op_float op_string env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LString x), VLit (LString y) -> VLit (LString (op_string x y))
    | VLit (LInt x), VLit (LInt y)       -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y)   -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y)     -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y)     -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s + %s" (pretty_value v1) (pretty_value v2)

and binop op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y)     -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y)   -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y)   -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s + %s" (pretty_value v1) (pretty_value v2)
    
and binop_bool op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y)     -> VLit (LBool (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LBool (op_float x y))
    | VLit (LInt x), VLit (LFloat y)   -> VLit (LBool (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y)   -> VLit (LBool (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s + %s" (pretty_value v1) (pretty_value v2)

and binop_bools op_bool env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LBool x), VLit (LBool y) -> VLit (LBool (op_bool x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s + %s" (pretty_value v1) (pretty_value v2)

and unop_p op env e =
    let v = eval_expr env e
    match v with
    | VLit (LInt x)   -> VLit (LInt (+x))
    | VLit (LFloat x) -> VLit (LFloat (+x))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s " (pretty_value v)

and unop_n op env e =
    let v = eval_expr env e
    match v with
    | VLit (LInt x)   -> VLit (LInt (-x))
    | VLit (LFloat x) -> VLit (LFloat (-x))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s " (pretty_value v)

and unop_b op env e =
    let v = eval_expr env e
    match v with
    | VLit (LBool x) -> VLit (LBool (op x))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (+): %s " (pretty_value v)
