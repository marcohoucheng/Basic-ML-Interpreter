// Synthetic Sugar: let f x = x + 1 or let f = fun x -> x + 1
// Curry: a function with multiple parameters is rewritten as a series of new functions, each with only one parameter. And this is done automatically by the compiler for you.
// Lists are not polymorphic

// multThree : a -> a -> a -> a
let multThree x y z = x * y * z
// Also de-sugaring
let multThree_uncurried = fun x -> fun y -> fun z -> x * y * z

// add1 : int * int -> int
let add_uncurried = fun (x, y) -> x + y

// add2 : int -> int -> int
let add_curried = fun x -> (fun y -> x + y)

// uncurried form, i.e. with tuples
let call_uncurried = add_uncurried (3, 4)
// CURRIED form
let call_curried = add_curried 3 4

// (b -> a -> c) -> a -> b -> c
let flip f x y = f y x

// g : (Int x Int) -> Int
let g (x,y) = x + y + 1

// g : a -> b -> c -> a * b * c
let g x y z = (x, y, z)
let g = fun x -> fun y -> fun z -> (x, y, z)

// Int * (Int -> Int) -> Int
let g (x, y) = y (x + 1) + 1

// (Bool * Int * Int) -> Int
let h (x, y, z) = if x && y > 2 then y else z

// Bool -> "b" (a -> Bool) -> "c" (a) -> Bool
// Bool -> a -> Bool -> a -> Bool
let f a b c = if a then b c else a

// a -> (a -> b) -> b
let f x y = y x

// a -> b -> ((b -> a) -> c) -> c
let h x y z = z y x

// (Bool -> Bool * Int -> Bool * Int) -> Int
let u (a, b, c) = if a (b c) then c else 3

// a -> a
let id x = x

// (a * b) -> (b * a)
let swap (x, y) = (y, x)

// (a * a * (a -> b)) -> b * b
let swap2 (x, y, f) = (f x, f y)

// (Int -> a) * Int -> a
let app (f, x) = f (x + 1)

// map : (a -> b) -> List a -> List b
let rec map f l =
    match l with
    | [] -> []
    | x :: xs -> f x :: map f xs

// filter : (a -> bool) -> a list -> a list
let rec filter f l =
    match l with
    | [] -> []
    | x :: xs -> if f x then x :: filter f xs else filter f xs

// iter : (a -> unit) -> a list -> unit
let rec iter f l =
   match l with 
   | [] -> ()
   | x :: xs -> f x; iter f xs

// foldL : (b -> a -> b) -> b -> a list -> b
let rec foldL f z l =
    match l with
    | [] -> z
    | x :: xs -> foldL f (f z x) xs

(*
// foldL workings:

type x = a
f input: type z, type x
f output: type z
foldL output: type z

type f -> type z -> type l -> type output
type f -> b -> a list -> type output
(b -> a -> b) -> b -> a list -> type output
(b -> a -> b) -> b -> a list -> b
*)