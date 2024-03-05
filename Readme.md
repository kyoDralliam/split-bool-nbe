Splitting Bools with Nbe
==========================

A toy implementation of a small dependent type theory with extensional booleans.

The type theory features a single universe, extensional dependent products Π, and booleans 𝔹 with large elimination.


# Requirements

Tested with 

- ocaml >= 4.14.1
- dune >= 3.8.2
- utop >= 2.13.1 (for running the examples)

# Building

From the top directory, issue

```
$ dune build
```


# Running

Assuming utop is installed, from the top directory, issue
```
$ dune utop
```

This should drop into an utop REPL with the module [lib/example.ml](https://github.com/kyoDralliam/split-bool-nbe/blob/main/lib/example.ml) opened
```
utop # check_all_examples () ;;
- : bool = true
```