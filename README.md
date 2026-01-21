# Language Overview

Simply typed lambda calculus with some small extensions. Mostly standard syntax. See the [examples](examples).

## Language features

- subtyping
- (impredicative) polymorphism
- a structural type system
- enum types
- tuple types

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

Evaluates the 'typed IR' in big-step evaluation style to produce a final value.
It handles function application by treating all functions as closures, which avoids any kind of substitution that would otherwise complicate things.

# Implementation Details

Lots of temporary values (eg. types during type-checking, values during evaluation) are arena allocated to better work around rust's ownership rules but may be reference counted in the future to allow for memory to be freed immediately.

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
funclang path/to/source_file evaluate
```

Error handling is hardly implemented so there is no location information attached to errors unfortunately.
