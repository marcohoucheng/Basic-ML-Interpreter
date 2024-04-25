# Introduction

This project is an exam for the Functional Languages module in MSc Computer Science at University of Padova.

It is an implementation of a basic ML language interpreter written in F\#. This interpreter supports type inference where the interpreter completes the type inference step before executing any comments to ensure safety of the code.

## Usage

The interpreter can be ran on Visual Studios on Windows. ML language commands can be entered via the `test.tml` file or through the cmd window. Some example codes are as follows:

`
let f x y = (x, y) in
let g x = f x x
in ()


let f = fun x -> (x + 1, if x then 1 else 2)

let x = 5 in
let y = 8. in
let f = x * 2 + y in
let z = f > 0
in (z)
`