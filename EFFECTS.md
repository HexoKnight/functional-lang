effects:
- structural
- `effect <label> <TyIn> <TyOut>` -> effect

types:
- arrow types now have the type of effects that they require
  - `A -> B %{<effects>} -> C`

values:
- effect trigger
  - `trigger <effect>` -> func: `TyIn %{effect} -> TyOut`
- effect handler
  - `handle <effect>` -> func: `[%H] (enum {trigger: (TyOut, TyIn -> T), none: T} %{H} -> R) -> (() %{effect, H} -> T) -> R`
- abstractions now have the type of effects that they require
  - `\a:A \b:B %{<effects>} body`
  - automatically pulled in from scope
- effect abstraction
  - `?%<name> ...` -> `[%<name>]`
- effect application
  - `... %[<effects>]` -> `... %[<effects>]`
  - can be inferred
- applications can manually specify the effects to be used
  - `func %{<effects>} arg`
  - automatically pulled in from scope

# Examples

```
(\foo %{Get[T]} trigger Get[T]) .\func: foo %{Get[T]} -> T

(?%E \f: () %{E} -> () %{E} f ()) .\run: [%E] (() %{E} -> ()) %{E} -> ()

handle <mut T> \() %{get_t: Get[T], set_t: Set[T]}

get_t() // T

set_t foo // ()

func () // ()
func %{get_t} () // ()

(\() get_t()) // () %{get_t: Get[T]} -> T
  .\f

run %[Get[T]] f // ()
run %{Get[T]} f // ()
run f // ()
```

# Effect passing combos
- no effects on function: `func arg`
- most recent effect: `func arg`
- explicit effect (eg. for less recent):
  - `func %{label1} arg`
  - `func %{label2} arg`
- multiple effects of same name (forced to be explicit):
  - `func %{break1: label1, break2: label2} arg`
  - `func %{break1: label1, break2: label1} arg`

# effect resolution
- `type_check(uir) -> (tir, ty, effs)`
- 'effects used' propagates out from applications until they are captureed by
- `app { func, arg } => (_, _, func.effs + arg.effs + func.ty.effs)`
- `abs { arg_ty, body } => (_, arg_ty -> %{body.effs} body, 0)`
- `?%E (in -> %{e, E} out) -> %{E} out2`
- `?%E (in -> %{e1, E} out) -> (in -> %{e2, E} out) -> %{E} out2`
