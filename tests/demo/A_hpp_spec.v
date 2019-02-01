Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Auto. 
Require Demo.A_hpp.

Definition A__foo := "_ZN1A3fooEi".
Definition A__foo_spec : function_spec' :=
  SFunction (Qmut T_int) (Qmut T_int :: nil)
      (fun x =>
         {| wpp_with := Z
          ; wpp_pre := fun y => [| x = Vint y |] ** [| 0- 2^31 < (y + 6)%Z < 2^31 -1 |]
          ; wpp_post := fun y (r : val) => [| r = Vint (y + 6)%Z |]
          |}).

Definition A__bar := "_ZN1A3barEi".
Definition A__bar_spec : function_spec' :=
  SFunction (Qmut T_int) (Qmut T_int :: nil)
      (fun x =>
         {| wpp_with := Z
          ; wpp_pre := fun y => [| x = Vint y |] ** [| 0- 2^31 < (y + 7)%Z < 2^31 -1 |]
          ; wpp_post := fun y (r : val) => [| r = Vint (y + 7)%Z |]
          |}).

Definition A_hpp_spec (resolve : _) :=
      (|> cglob' (resolve:=resolve) A__foo A__foo_spec) -* cglob' (resolve:=resolve) A__bar A__bar_spec.
