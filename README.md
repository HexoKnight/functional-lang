# Language Overview

A small functional language built up from System F<:. Mostly standard syntax. See the [examples](examples) and [stdlib](stdlib).

## Language features

- subtyping
- bounded (impredicative) polymorphism
- local argument type and type argument inference
- a structural type system
- enum types
- tuple types
- (positive) recursive types
- algebraic effects

# Design

The program consists of 4 stages: parsing, validation, typing and evaluation.
The intermediate formats used and produced by each stage can be found in [src/reprs](src/reprs).

## [Parsing](src/parsing)

Parses the source text into an AST.
Currently uses a rust parser generator library called LALRPOP.

## [Validation](src/validation)

Performs pre-type-checking things like name resolution to produce an 'untyped IR'.
But it is intended to also be the place for syntax desugaring.

## [Typing](src/typing)

Type checks the 'untyped IR' to produce a 'typed IR' (typed in the sense that it is well typed, not that it actually has any type information, which is in fact erased here).

## [Evaluation](src/evaluation)

Evaluates the 'typed IR' in small-step evaluation style to produce a final value.
It handles function application by treating all functions as closures, which avoids any kind of substitution that would otherwise complicate things.

# Building

The binary requires a feature of the same name (to allow separation of dependencies without needing to create a separate crate).

```sh
cargo build --features binary
```

The binary can then be found at `target/debug/funclang[.exe]`. Check it works with

```sh
funclang --help
```

# Running Programs

```sh
funclang evaluate path/to/source_file
```

A best attempt at error handling is implemented, with mostly full span information.
However, deep subtyping and type inference errors can be incredibly cryptic.
