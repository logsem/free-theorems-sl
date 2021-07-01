# Free Theorems from Separation Logic Specifications

This repository contains the Coq mechanization associated with the paper "Free
Theorems from Separation Logic Specifications".

## Navigating the development

The html rendering of the Coq scripts provides an easy way of navigating the
development, without having to build anything. It is [available
online](https://logsem.github.io/free-theorems-sl/html/toc.html).

### Examples

- `stack`: a simple stack specification (§2)
- `file`: simple specification for a file API with open/read/close operations (§5.1)
- `iterator`: specification for an iterator over a mutable collection (§5.2)
- `well_bracketed`: specification enforcing a well-bracketing protocol (§5.3)
- `traversable_stack`: a stack specification with a `foreach` operation (§5.4)
- `linearizability`: a concurrent specification using logically atomic triples (§6)

Bonus:
- `stack_impl`: an example implementation of the stack library, satisfying the
  specifications in `stack` and `traversable_stack`

### Language and logic

The `heap_lang` directory contains the definition of the language. It is based
on the standard cbv language of the same name shipped with Iris, extended with
the additional trace primitives and corresponding reasoning principles.

- `lang` defines the syntax and operational semantics of the language (Fig. 1)
- `lifting` defines the trace-related resources (see `trace_is`, `hist`,
  `trace_inv` and related lemmas) and proves the Separation Logic specifications
  for the trace operations (`wp_emit` and `wp_fresh`) (Fig. 3)
- `adequacy` establishes the Adequacy theorem: lemma `modular_invariance`
  corresponds to Theorem 4.1.

The remaining unlisted files typically contain helper lemmas or tactics.

### Notations

Some notations differ between the Coq formalization and the paper. Here is a
short cheatsheet of the common Coq notations that we use:

- Hoare triples are written as `{{{ P }}} e {{{ RET r; Q }}}`, where `P` is the
  pre-condition, `Q` the post-condition, and `r` is a binder naming the return
  value in `Q`.
- `# x` denotes a (deep embedded) value of the programming language, for the
  literal `x`. For instance, `#()` is the "unit" value, `# 3` is the integer
  value 3, and `# "abc"` is the value for the event tag `"abc"`.
- `(a, b)%V` denotes a deep embedded value of the programming language, which is
  the pair of values `a` and `b`. This is to distinguish with `(a, b)` which is
  a pair in Coq.
- `_ !! _` corresponds to the "lookup" operation. In particular, if `t` is a
  trace (a list of events), `t !! i` looks up the `i`-th value of the trace (and
  returns an option as trace might be of length less than `i`).
- `_ ++ _` is the list concatenation operation. We use `t ++ [e]` for the trace
  adding event `e` at the end of trace `t`
- the `trace_is` predicate corresponds to "trace" in the paper

## Building the proofs

### Installing the dependencies

The development is known to build with Coq 8.9.1 to 8.12 and Iris 3.3. 

The easiest way to install those is by creating a fresh *local*
[opam](https://opam.ocaml.org/) switch with everything needed (check that opam
`>= 2.0` is installed):

```
  opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.09.1
  eval $(opam env)
```

#### Troubleshooting

If the invocation fails at some point, either remove the `_opam` directory and
re-run the command (this will redo everything), or do `eval $(opam env)` and
then `opam install -y .` (this will continue from where it failed).

### Building

Simply run:
```
make
make html  # rebuild the html rendering of the proofs
```

