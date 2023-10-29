# generic-lr

A framework for typed syntaxes with variable binding and usage restrictions.

## Interesting modules

The core part of the framework can be loaded through `Generic.Linear.Everything`.
This includes the definition of `map-s` for layers of syntax in
`Generic.Linear.Syntax.Interpretation.Map`, various properties of environments
and renaming under `Generic.Linear.Environment` and `Generic.Linear.Renaming`,
the semantic traversal in `Generic.Linear.Semantics`, and the implementations of
generic renaming and substitution in `Generic.Linear.Semantics.Syntactic`.

The examples from chapter 8 of the thesis can be found in
`Generic.Linear.Example.UsageCheck`,
`Generic.Linear.Example.NbESimple`,
`Generic.Linear.Example.WRel` (with the instantiation to monotonicity in
`Generic.Linear.Example.WRel.Monotonicity`), and
the `Generic.Linear.Example.Translation` directory.
All of the examples can be checked by running
`agda src/Generic/Linear/Example/AllExamples.agda`.

## Compiles with

- Agda version 2.6.3
- agda-stdlib version 1.7.2
