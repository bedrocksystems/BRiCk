# Changelog

### How to use

This document is a best-effort that tracks breaking changes to the code base.

When adding a new entry, add it to the **top** of the list with the date.
When a release occurs, change the `Since Last Release` heading to the name
of the release, and introduce a new heading.

## Since Last Release

## 2026.10.16

The supported subset, known soundness caveats and trusted base are summarized
in `rocq-skylabs-brick/doc/sphinx/features.rst`.

2026.10.15: `align_of_void` is now proved from `size_of_void` instead of being
assumed (#389).

2026.10.13: Soundness fixes that remove or strengthen rules. Proofs that relied
on the old rules need the new side conditions.
- Removed the axiom that identified pointers from persistent type information
  and allocation liveness. It allowed proving `False` after reusing storage with
  placement `new` (#385).
- `void` result cells have a defined one-byte size. Previously `type_ptr_size`
  could derive `False` from an ordinary `void` return (#374).
- Inverse pinned offsets require validity of the source pointer, not only the
  destination (#375).
- Strict pointer interpolation requires a positive element size (#376).

2026.10.13: `Egnu_null t` (GNU `__null`, i.e. `NULL` in GNU C++) is now
`Eint 0 t` instead of `Ecast (Cptr2int t) Enull`, which had no semantics, so
every use of `NULL` was unprovable.

2026.10.07: `cpp2v` emits `Dunsupported` for records with under-aligned fields
or base classes, since typed pointers imply natural alignment. Byte-only packed
records and packed records with explicitly aligned fields are still supported
(#362).

2026.10.07: Layout fixes.
- Typed block decomposition of arrays requires array typing and preserves
  alignment (#359).
- The alignment of a named type is only constrained when its alignment metadata
  is known (#350).

2026.10.06: Raw integer-byte conversions require `has_type_prop (Vn n) Tbyte`,
and list conversions require typed-byte evidence. Float object encodings
require a supported format, so x87 `long double` bytes stay abstract (#346).

2026.10.05: New `genv` field `member_pointer_bitsize : bitsize`, separate from
ordinary pointer width, which defines the size of member pointer cells. Code
that builds a `genv` must supply it (#349).

2026.10.05: `wp_initialize_decomp_ok` was not exhaustive and allowed proving
`False`. It is now proved (#347).

2026.10.02: `size_of` of `Tref` and `Trv_ref` is pointer-sized instead of
`None`. The old definition contradicted `type_ptr_size` (#341).

2026.09.24: Fixed false admitted lemmas in the inductive pointer models (#333,
#334).

2026.09.23: Empty-base optimization fixes (#311).
- Disabled `implicit_destruct_struct`, `implicit_destruct_union`,
  `struct_to_raw` and `raw_bytes_of_struct_wf_base`, which are unsound with
  empty-base optimization.
- `cpp2v` emits base-class offsets in bits, like field offsets. Regenerate
  `cpp2v` output.

2026.09.21: The `cpp.prog` plugin moved to its own package,
`rocq-skylabs-brick-cpp-prog`. Add it to the dependencies of projects that use
`cpp.prog` (#326).

2026.07.29: Add support for clang's `CXXStdInitializerListExpr`, i.e. the
implicit construction of a `std::initializer_list<E>` from a braced-init-list
(<http://eel.is/c++draft/dcl.init.list#5>).
- New `Expr` constructor `Einitlist_std (backing : Expr) (t : type)`. Downstream
  exhaustive matches over `Expr` need a new case.
- `wp_init_initlist_std` reduces it to the `std::initializer_list` constructor
  named by `std_initlist_ctor` (`lang/cpp/syntax/types.v`), following
  `wp_init_binop_spaceship`. The representation of the resulting object belongs
  to whoever specifies that constructor; see `brick-libcpp`.
- The lifetime-extended case, e.g. `std::initializer_list<int> il = {1,2,3};`,
  is still unsupported because it requires scope-extruded temporaries.

2025.03.20: Change global prefix `bedrock.xxx` to `bluerock.xxx`
- See `scripts/fm-refactorings/bedrock-bluerock.sh`

2025.03.17: Split the C++ program logic BRiCk from the BlueRock prelude (`rocq-skylabs-prelude`) and Iris extensions (`rocq-skylabs-iris`).
- See `scripts/fm-refactorings/split-brick.sh`


