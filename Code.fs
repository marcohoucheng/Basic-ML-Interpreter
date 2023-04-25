// fib n = nth fib seq number

let rec fib n =
    match n with
    | 0 -> 0
    | 1 -> 1
    | _ -> fib (n-1) + fib (n-2)

List.map fib [0 .. 10]

// prime n = first n prime numbers

// prime = only divisible by 1 and itself

let isPrime n =
    let sqrt_int n = int(sqrt(float n) - sqrt(float n) % 1.0)
    let ub = sqrt_int n
    //let listtocheck = [2 .. ub]
    // divide through 2 to ub, if reminder is 0 then false
    let c = 2


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