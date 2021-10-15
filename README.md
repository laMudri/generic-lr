# generic-lr

A framework for typed syntaxes with variable binding and usage restrictions.

## Interesting modules

The core part of the framework can be loaded through `Generic.Linear.Everything`.
This includes the definition of `map-s` for layers of syntax in
`Generic.Linear.Syntax.Interpretation.Map`, various properties of environments
and renaming under `Generic.Linear.Environment` and `Generic.Linear.Renaming`,
the semantic traversal in `Generic.Linear.Semantics`, and the implementations of
generic renaming and substitution in `Generic.Linear.Semantics.Syntactic`.
We also have the other two examples from the paper: world-indexed relations in
`Generic.Linear.Example.WRel`, with the instantiation to monotonicity in
`Generic.Linear.Example.WRel.Monotonicity`; and the usage elaborator in
`Generic.Linear.Example.UsageCheck`.

## Compiles with

- Agda version 2.6.2
- agda-stdlib version 0.17
