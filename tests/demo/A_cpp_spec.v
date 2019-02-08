Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import Auto.

From Demo Require Import A_hpp_spec.


Definition A_cpp_spec (resolve : _) :=
      (|> Forall ti, cglob' (resolve:=resolve) A__bar ti A__bar_spec) -*
          Forall ti, cglob' (resolve:=resolve) A__foo ti A__foo_spec.
