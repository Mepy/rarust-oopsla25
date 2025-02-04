## RARust
This repo provides a prototype implementation of the **R**esource **a**ware type system for **Rust** (**RaRust**) presented in the paper *Automatic Linear Resource Bound Analysis for Rust via Prophecy Potentials*.

**RaRust** takes raw Rust programs (with `tick` annotation) as inputs and prints functions' signatures with resource annotation as outputs. This repo also includes an evaluation of a benchmark to demonstrate its usage.


### Quick Start 
Our experiment result is in `./benchmark.result`. Use `reproduce.sh` to reproduce the result, if dependency has been already installed; guides from scratch are in the following section.

### Repo Structure
```
.
├── README.md # this file
├── benchmark.result # analysis result of benchmark
├── clean.sh         # the script to clean result
├── reproduce.sh     # the script to reproduce result

├── charon # fork with modification from [Aeneas](https://doi.org/10.1145/3547647)
├── evaluation
│   ├── benchmark
│   │   ├── benchmark.llbc # llbc format of benchmark
│   │   └── src
│   │       ├── types.rs # benchmark types
│   │       ├── eval.rs  # benchmark programs
│   │       └── main.rs  # benchmark entry
│   ├── rrlib # the tick function rrlib::tick(i64)
│   └── RaRustInFlux # encoding in [Flux](https://github.com/flux-rs/flux)
└── rarust
    └── src
        # whole program
        ├── main.rs      # ENTRY, read benchmark.llbc and call llbc::handle
        ├── llbc.rs      # traverse llbc, linear programming, and output result
        ├── printer.rs   # pretty printing for output
                
        # functions
        ├── functions.rs # function signatures and call graph
        ├── scc.rs       # strongly connected component analysis 

        # implementation of typing rules
        ├── rich_type.rs # rich_type with potential
        ├── enrich.rs    # enrich types with potential annotations
        ├── lp.rs        # linear programming context
        ├── typ_ctx.rs   # typing context, read and write
        ├── subtyping.rs # resource aware subtyping with lp
        └── typing.rs    # type checking expressions and statements
```

### Steps to reproduce from scratch
We packed into the artifact the JSON format IR of `benchmark.llbc` and analysis result `benchmark.result`. The following are steps to reproduce the evaluation.

0. make sure `cargo`, `cc` and `make` already installed.
1. install CbcSolver (https://github.com/coin-or/Cbc)
    ```sh
    $ # coincbc.sh
    $ apt-get update
    $ apt-get install coinor-cbc coinor-libcbc-dev 
    ```
    CbcSolver version `2.10.3+repack1-1build1` is tested.
2. compile `charon` ([fork](https://github.com/Mepy/charon/tree/Mepy) with modification from [Aeneas](https://doi.org/10.1145/3547647))
    ```sh
    $ cd charon 
    make
    ```
3. and use `charon` to generate low-level borrow calculus (llbc) in JSON format
    ```sh
    $ cd evaluation/benchmark 
    $ ../../charon/bin/charon # generate benchmark.llbc at WorkDir
    ```
4. run evaluation with `rarust`
    ```sh
    $ cd rarust 
    $ cargo build # with dependencies, including charon
    $ cargo run >/dev/null -- "../evaluation/benchmark/benchmark.llbc" "../benchmark.result"
    ```
    Where `"../evaluation/benchmark/benchmark.llbc"` is the path of llbc IR and `"../benchmark.result"` is the path of the result.

### Explanation of Analysis Result

We only explain 4 functions for demonstration, and others are similar in `./benchmark.result`:
```
sum_loop // |constraints| = 54
    : 0 + l : & List[Nil=1(), Cons=6(Lit, Box(List))] -> Lit

sum_rec // |constraints| = 19
    : 1 + l : & List[Nil=-0(), Cons=6(Lit, Box(List))] -> Lit

find // |constraints| = 31
    : 1 + t : & Tree[Leaf=0(), Node=8(Lit, Box(Tree), Box(Tree))] + x : Lit -> Lit

rev // |constraints| = 71
    : 4 + l : &mut (List[Nil=-0(), Cons=9(Lit, Box(List))], List[Nil=0(), Cons=0(Lit, Box(List))]) -> 0, ()
```

`|constraints|` is the number of linear constraints during analysis of this function. 

`sum_loop` is the sum function written with loop, and the resource consumption is $0+1\cdot|\text{Nil}| + 6\cdot|\text{Cons}|$, or $1+6 |l|$ where $|l|$ denotes the length of a list.

`sum_rec` is the sum function written in a recursive style, and the resource consumption is $1+0\cdot|\text{Nil}| + 6\cdot|\text{Cons}|$, or $1+6|l|$ again.

`find` is the function that finds `x` in the tree `t`, and the resource consumption is $1+0\cdot|\text{Leaf}| + 8\cdot|\text{Node}|$, or $1+8 |t|$ where $|t|$ denotes the number of internal nodes of the tree $t$.

`rev` is the reverse function of mutable lists. The mutable borrow types should be interpreted as that from $\text{List}(\text{Nil}=0, \text{Cons}=9)$ to $\text{List}(\text{Nil}=0, \text{Cons}=0)$. The resource consumption is $4+(0-0)\cdot|\text{Nil}| + (9-0)\cdot|\text{Cons}|$, or $4+9|l|$.

We assembled our benchmark suite to cover all the considered features. We list as follows:

| case(s) | feature(s) | comment |
| :---: | :---: | :---: |
| sum_**rec** | shared borrows and **rec**ursive function | NA |
| rev_**rec** | mutable borrows and **rec**ursive function | NA |
| sum_**loop**, rev_**loop** | **loop** statement `while true { ... }` | having the same result as the **rec**ursive version |
| rev2, dup2 | function call | **exactly** the twice resource consumption |
| reborrow_s, reborrow_m | reborrow | NA |
| nested_s_s, nested_m_s, nested_m_m | nested borrows $ \& \& t $ | NA |
| min, max, find, add, tuple, record | user-defined data types like trees, tuples and records | NA |