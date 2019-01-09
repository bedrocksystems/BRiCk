From Coq Require Export
     Strings.String
     Lists.List.

From Cpp Require Export Ast.

Notation "a !:: b" := (@cons ident a b) (at level 30, right associativity).
