Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Parser.
Require Import Cpp.HoareSemantics.

From Demo Require Import A_hpp_spec.


Definition A_cpp_spec (resolve : _) :=
      (|> cglob' (resolve:=resolve) A__bar A__bar_spec) -* cglob' (resolve:=resolve) A__foo A__foo_spec.
