# Writing Specifications

Specifications are represented as pre- and post-conditions. They can be written using notation that makes them reminiscent of doxygen comments.

+ `\with (x : T) ... (y : U)` represents universally quantified variables that scope
  over *both* the pre- and the post-condition.
+ `\let x := e` represents a standard `let` expression assigning the value of
  of the *Gallina* expression `e` to the logical variable `x`.
+ `\prepost P` adds the separation logic assertion `P` to the pre- *and* the
  post-condition
+ `\arg nm e` adds to the pre-condition that the value of the "current" argument
  should unify with `e`. Currently, `nm` (a string) is used for documentation
  purposes only.
  - This syntax also supports with binders, e.g. `\arg{x} "x" (Vint x)`. Jus
    like `\with`, variables are quantified over both thr pre- and thr post-condition. 
    If you want to specify the type of the quantified variable,
    `\arg{(x:Z) (y:nat)} "x" (Vint x)`
+ `\args es` adds `es` arguments to the current list of arguments (note that `es`
  is a list).
+ `\pre P \post{x .. y}[r] Q` represents a pre-condition of `P` and a
  post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. The expression `r` will unify with the
  return value.
+ `\pre P \post[r] Q` represents a pre-condition of `P` and a
  post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. In this syntax, `r` is a binder of type
  `val`.
+ `\pre P \post Q` represents a pre-condition of `P` and a
  post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. In this syntax, the return type must
  be `void`.

## Simple Examples

A function to return 0.

```coq
\pre empSP
\post{}[Vint 0] empSP
```

A function to return its parameter plus 1 (note the pre-condition is necessary
to ensure that the addition does not overflow).

```coq
\with (n : Z)
\arg "n" n
\pre [| has_type (n+1) (Tint W32 Signed) |]
\post{}[Vint (n + 1)] empSP
```

A function to read the (integer) value stored at a pointer (note that this
function only requires fractional ownership of the underlying pointer).

```coq
\with (p : val) (v : Z) (q : Qp)
\arg "p" p
\prepost _at (_eq p) (tint W32 q v)
\pre empSP
\post{}[Vint v] empSP
```
