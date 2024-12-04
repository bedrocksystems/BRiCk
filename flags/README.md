Common Flags
============

The files in this folder configure the flags used for `coqc` and `coqdoc`.

## Remarks on the warning configuration for `coqc`

- We temporarily disable the verbose incompatible prefix warnings via
  `-w -notation-incompatible-prefix`.
- As in Iris, we use `-w -notation-overridden`, see
  [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/_CoqProject).
- We also disable similar warnings related to notations via:
  `-w -custom-entry-overridden`, `-w -redundant-canonical-projection`, and
  `-w -ambiguous-paths`.
