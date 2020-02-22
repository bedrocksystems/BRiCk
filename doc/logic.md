# Logics: Sem/Logic.v, Sem/PLogic.v
- `mpred`
  + The C++ program logic
- `Rep :~ val -> mpred`
  + Used for representation predicates over **locations**
  + Argument is the location
- `Loc :~ genv -> option val`
  + Computes a location (e.g. a pointer) using the current program
- `Offset :~ genv -> option (val -> val)`
  + Computes on offset using the current program


# Connectives: Sem/PLogic.v
- `_eqv : val -> Loc`
  + A location predicate that asserts equivalence over the argument and the value given to the predicate
- `_eq : ptr -> Loc`
  + A location predicate that asserts equivalence over the argument and the poiter given to the predicate
- `_at : Loc -> Rep -> mpred`
  + The `Loc` is valid and the `Rep` holds on it.
  + Note the the "validness" of a `Loc` means that it is a pointer, not
    that it is not null.

# Ownerships: Sem/PLogic.v
- `tint : size -> Qp -> Z -> Rep`
  + Ownership of a signed integer
  + size: The bit size of the integer
  + Qp: The fractional permission
  + The value of the integer
- `tuint : size -> Qp -> Z -> Rep`
  + same as above but unsigned integers
- ...


# Sizes: Syntax/Types.v

*(in the future these might be replaced by looking up in the environment)*

- `char_bits`
  + 8 bits
- `short_bits`
  + 16 bits
- `int_bits`
  + 32 bits
- `long_bits`
  + 64 bits

# Locations

There are several ways to construct `Loc`s.

- `_eq : val -> Loc`
  + exactly this location.
- `_offsetL : Offset -> Loc -> Loc`
  + add an offset to a location.
- `_field : field -> Offset`
  + the offset of a field
- `_super : forall (base parent : gname), Offset`
  + the offset of a parent class


# Common Use Cases
The canonical approach to describe ownership of a variable is:
```
_at (_eq x) R
```

This reads that "At the location `x`, the predicate `R` holds".

A common instantiation of `R` is that of 32 bit signed integers:
```
tint W32 1 42
```

This is a representation predicate that asserts full ownership (`1`) of the given location,
while describing that it is 32 bits (`int_bits`), that it has the value `42`.

The full ownership is then:
```
_at (_eq x) (tint W32 1 42)
```
