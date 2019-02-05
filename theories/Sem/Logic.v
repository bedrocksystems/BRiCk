From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Ast Parser.
Import Cpp.Parser.
From Cpp.Sem Require Import
     Semantics.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

From auto.Tactics Require Import Discharge.

Module Type logic.

  Parameter mpred : Type.

  Parameter ILogicOps_mpred : ILogicOps mpred.
  Global Existing Instance ILogicOps_mpred.
  Parameter ILogic_mpred : ILogic mpred.
  Global Existing Instance ILogic_mpred.

  Parameter BILogicOps_mpred : BILogicOps mpred.
  Global Existing Instance BILogicOps_mpred.
  Parameter BILogic_mpred : BILogic mpred.
  Global Existing Instance BILogic_mpred.

  Parameter EmbedOp_Prop_mpred : EmbedOp Prop mpred.
  Global Existing Instance EmbedOp_Prop_mpred.
  Parameter Embed_Prop_mpred : Embed Prop mpred.
  Global Existing Instance Embed_Prop_mpred.

  Parameter ILLOperators_mpred : ILLOperators mpred.
  Global Existing Instance ILLOperators_mpred.
  Parameter ILLater_mpred : ILLater mpred.
  Global Existing Instance ILLater_mpred.

  Notation "'[|'  P  '|]'" := (only_provable P).

  (** core assertions
   * note that the resource algebra contains the code memory as well as
   * the heap.
   *)

  (* heap points to *)
  Parameter ptsto : val -> val -> mpred.

  (* todo(gmm): this is thread local *)
  (* address of a local variable *)
  Parameter addr_of : region -> ident -> val -> mpred.

  (* the pointer contains the code *)
  Parameter code_at : ptr -> Func -> mpred.
  (* code_at is freely duplicable *)
  Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
  Axiom code_at_drop : forall p f, code_at p f |-- empSP.

  Parameter ctor_at : ptr -> Ctor -> mpred.
  Parameter dtor_at : ptr -> Dtor -> mpred.

  (* it might be more uniform to have this be an `mpred` *)
  Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

  Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.

  Parameter size_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter align_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter with_genv : (genv -> mpred) -> mpred.
  Axiom with_genv_single : forall f g,
      with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).

End logic.

Declare Module L : logic.

Export L.

Export ILogic BILogic ILEmbed Later.
