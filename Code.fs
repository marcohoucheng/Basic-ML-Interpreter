// fib n = nth fib seq number

let rec fib n =
    match n with
    | 0 -> 0
    | 1 -> 1
    | _ -> fib (n-1) + fib (n-2)

List.map fib [0 .. 10]

// Define a function to check if a number is prime
let isPrime n =
    let rec loop i =
        i > n/2 || (n % i <> 0 && loop (i + 1)) // stop as soon as a factor is found
    loop 2

let isPrime_2 n =
    let sqrt_int n = int(sqrt(float n) - sqrt(float n) % 1.0)
    let rec loop i =
        i > sqrt_int n || (n % i <> 0 && loop (i + 1)) // stop as soon as a factor is found
    loop 2


// Define a function that checks if a number is prime
let is_prime n =
    let rec loop i =
        if i * i > n then true
        elif n % i = 0 then false
        else loop (i + 1)
    in loop 2

// Define a function that returns the first n prime numbers
let first_n_primes n =
    let rec loop i acc =
        if List.length acc = n then acc
        elif is_prime i then loop (i + 1) (i :: acc)
        else loop (i + 1) acc
    in loop 2 [] |> List.rev

// Without pipe
let first_n_primes n =
    let rec loop i acc =
        if List.length acc = n then acc
        elif is_prime i then loop (i + 1) (i :: acc)
        else loop (i + 1) acc
    in List.rev (loop 2 []) // reverse the order


////////////////////////////////////////////////////////////////////////////////////////

let isPrime_log n =
    let rec loop i =
        printf "i = %o\n" i
        let a = i > n/2
        printf "i > n/2 = %b\n" a
        let b = n % i <> 0
        printf "n mod i <> 0 = %b\n" b
        a || (b && loop (i + 1)) // stop as soon as a factor is found
    loop 2

let isPrime_log2 n =
    let sqrt_int n = int(sqrt(float n) - sqrt(float n) % 1.0)
    let rec loop i =
        printf "i = %o\n" i
        let a = i > sqrt_int n
        printf "i > sqrt_int n = %b\n" a
        let b = n % i <> 0
        printf "n mod i <> 0 = %b\n" b
        a || (b && loop (i + 1)) // stop as soon as a factor is found
    loop 2

////////////////////////////////////////////////////////////////////////////////////////

// z |> g |> f x is the same as f x (g z)

[1 .. 10] |> List.map (fun x -> x * x) |> List.filter (fun x -> x % 2 = 0)

// is equivalent to:

List.filter (fun x -> x % 2 = 0) (List.map (fun x -> x * x) [1 .. 10])

// f x <| g z is equivalent to f x (g z)

List.head <| List.filter (fun x -> x % 2 = 0) [1 .. 10]

// is equivalent to

List.head (List.filter (fun x -> x % 2 = 0) [1 .. 10])

////////////////////////////////////////////////////////////////////////////////////////

module Fold =
    
    let rec foldR f z l =
        match l with
        | [] -> z
        | x :: xs -> f (foldR f z xs) x


    // foldL : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
    let rec foldL f z l =
        match l with
        | [] -> z
        | x :: xs -> foldL f (f z x) xs

    // map : ('a -> 'b) -> 'a list -> 'b list
    let map f l = foldR (fun l2 x -> l2 @ [f x]) [] l

    // filter : ('a -> bool) -> 'a list -> 'a list
    let filter p l = foldL (fun z x -> if p x then x :: z else z) [] l


    let rec max_by cmp l =
        match l with
        | [] -> raise (Failure "message")
        | [x] -> x
        | x :: xs -> let m = max_by cmp xs in if cmp x m then m else x


    type 'a option = None | Some of 'a

    let max_by_opt cmp l =
        let f m x =
            match m with
            | None -> Some x
            | Some y -> if cmp x y then Some y else Some x
        foldL f None l




    let r1 = foldL (fun z x -> x + z) 0 [1 .. 20] 

    let l2 = [1; 2; 3] @ [4; 5; 6]

    let s1 = foldL (+) "" ["a"; "b"; "c"]   // "abc"
    let s2 = foldR (+) "" ["a"; "b"; "c"]   // "cba"

    let factorial n = foldL ( * ) 1 [1 .. n]


    (*
    public static <A, B> List<B> map(Iterable<A> c, Function<A, B> f) {
        List<B> out = new ArrayList<>();
        for (A a : c)
            out.add(f.apply(a));
        return out;
    }

    template <class A, class B, class F>
    vector<B> map(const vector<A>& v, const F& f) {
        vector<B> r;
        for (auto x : v)
            r.push_back(f(x));
        return r;
    }
    *)



//// Trees

module Tree =

    type 'a tree = 
        | Leaf of 'a option
        | Node of 'a tree * 'a tree
    
    let t1 = Node (Node (Leaf Some 1, Leaf Some 2), Node (Leaf Some 3, Leaf None))

    let rec pretty_tree t =
        match t with
        | Leaf None -> "."
        | Leaf (Some x) -> sprintf "%O" x
        | Node (t1, t2) -> sprintf "(%s %s)" (pretty_tree t1) (pretty_tree t2)

    // map_tree : ('a -> 'b) -> 'a tree -> 'b tree
    let rec map_tree f =
        let R = map_tree f   // m : 'a tree -> 'b tree
        in fun t ->
            match t with
            | Leaf None ->
                Leaf None

            | Leaf (Some x) ->
                let z = Leaf (f x) in z

            | Node (l, r) -> 
                Node (R l, R r)

    // sum_int_tree : int tree -> int
    let rec sum_int_tree t =
        match t with
        | Leaf (Some x) -> x
        | Leaf None -> 0
        | Node (l, r) -> sum_int_tree l + sum_int_tree r 

    // sum_tree : ('a -> 'a -> 'a) -> 'a tree -> 'a
    let rec sum_tree (+) zero t =
        match t with
        | Leaf (Some x) -> x
        | Leaf None -> zero
        | Node (l, r) -> (sum_tree (+) zero l) + (sum_tree (+) zero r) 

    // filter : ('a -> bool) -> 'a list -> 'a list
    // filter_tree : ('a -> bool) -> 'a tree -> 'a tree
    let rec filter_tree p t =
        match t with
        | Leaf (Some x) -> if p x then Leaf (Some x) else Leaf None
        | Leaf None -> Leaf None
        | Node (l, r) -> Node (filter_tree p l, filter_tree p r)

    // foldL_tree : ('b -> 'a -> 'b) -> 'b -> 'a tree -> 'b
    let rec fold_tree f z t =
        match t with
        | Leaf (Some x) -> f z x
        | Leaf None     -> z
        | Node (l, r)   -> let z' = fold_tree f z l in fold_tree f z' r

    let sum_tree_by_folding f zero t = 
        fold_tree f zero t


    let tests () =
        let N = Node
        let L x = Leaf (Some x)
        let t1 = N (N (L 1., L 2.), N (L 3., Leaf None))
        printfn "t1 = %s" (pretty_tree t1)
        let z1 = sum_tree ( ** ) 2. t1
        let z2 = sum_tree_by_folding ( ** ) 2. t1

//        let mt1 = map_tree (fun x -> x >= 2) t1 
        ()



module OtherTree =

    type 'a tree = Node of 'a option * 'a tree option * 'a tree option

    let t1 = Node (Some 5, Some Node (Some 1, None, None), Some Node (Some 1, None, None))
        
    let Leaf x = Some (Node (Some x, None, None))

    let t2 = Node (Some 5, Leaf 1, Leaf 1) // Same as t1

    let SNode (x, t1, t2) = Some (Node (x, t1, t2))

    let t1 = Node (Some 5, 
                   SNode (Some 6, Leaf 1, Leaf 2), 
                   SNode (Some 7, Leaf 3, Leaf 4)
                   )

    let pretty_opt f o =
        match o with
        | None -> "."
        | Some x -> f x

    let rec pretty_tree t =
        match t with
        | Node (xo, lo, ro) -> 
            let x = pretty_opt (sprintf "%O") xo
            let l = pretty_opt pretty_tree lo
            let r = pretty_opt pretty_tree ro
            sprintf "(%s %s %s)" l x r

