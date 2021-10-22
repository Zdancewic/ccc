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

To build the OCaml development, run `make` from the `ml` subdirectory. This
generates `Main.native`, a simple front-end that accepts files with STLC terms
and prints out their denotations.  Run it by calling `Main.native <foo>.stlc`
where `<foo>` is a filename and `stlc` is the file extension.  The
(undocumented) syntax for STLC programs is almost OCaml, except that all types
are capitalized, and all `let` expressions and `fun` binders must have type
annotations.  See the files in `test/test*.stlc` for some examples.

Here is a sample output (which takes a long time to compute for such a small program!):
```
~/Research/ccc/ml> ./Main.native test/test_pair0.stlc
---------------------------------------------------------------- test_pair0.stlc
type Bool = One + One


let true : Bool = inl () in
let false : Bool = inr () in
let f : Bool * Bool -> Bool = fun (x : Bool * Bool) -> fst x in
f (false, true)

---------------------------------------------------
DENOTATION: 
0 -> Inr 0
```


You can also run `make utop` to get a `utop` environment to play around with things interactively.

