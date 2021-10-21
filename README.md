# Implementing Cartesian Closed Categories

This repo is an elementary implementation of Simply Typed Lambda Calculus (STLC)
and its semantics in terms of Cartesian Closed Categories.  It is not particularly well documented (yet!).

# Installation


## Dependencies

This project uses [Interaction
Trees](https://github.com/DeepSpec/InteractionTrees/) (currently as a git submodule) as the basis for its category theory
definitions.

The OCaml code depends on `menhir` and `utop`, which can be installed via:

```
opam install menhir utop
```

## Cloning the repository

To check out the repository, be sure to include the `--recurse-submodules` flag:

```
git clone --recurse-submodules https://github.com/Zdancewic/ccc
```

## Coq Development

To build the Coq development, you should be able to just use `make` at the top
level of the repo.

## OCaml Implementation

To build the OCaml development, run `make` from the `ml` subdirectory.  You can
also run `make utop` to get 

