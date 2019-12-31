C++ Semantics
==

This directory contains an (axiomatic) semantics for the parse trees described in `Cpp.Syntax`.
To avoid introducing closed world assumptions, the semantics is defined using a combination of `Parameter`s and `Axiom`s.

## Layout

- `Semantics.v` contains axioms pertaining to values and primitive operations.
- `Logic.v` *defines* our ambient logic using Iris.
- `Operator.v` contains the semantics of primitive operators.
- `Wp.v` contains parameters asserting the existance of `wp`'s for various syntactic classes, e.g. expressions, statements.
- `Expr.v` contains the semantics of expressions.
- `Stmt.v` contains the semantics of statements.
- `Call.v` consolidates rules about the evaluation of function arguments.
- `Init.v` contains the semantics of initialization lists.
- `Atomic.v` contains the semantics of atomic expressions.
- `Layout.v` contains the semantics of class layout.
- `PLogic.v` contains an abstract "path" logic for conviently writing paths within the logic, e.g. `a.b[3].c`.
- `CompilationUnit.v` contains the semantics of compilation units, in particular facts about types.
- `CCLogic.v` contains some definitions on top of Iris definitions of invariants and view shifts.
- `Linking.v` contains definitions pertaining to using facts established in one program in a larger program.
