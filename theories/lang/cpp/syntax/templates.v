Require Import bedrock.prelude.base.
Require Import bedrock.prelude.error.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.mcore.
Require Export bedrock.lang.cpp.syntax.namemap.

(** ** Template pre-instances *)
(**
A template file maps the symbol or type name of a template
instantiation (bound in a translation unit) to a _template
pre-instance_ comprising the instance's template name (bound in a
template file) and arguments.
*)
Definition temp_name : Set := name' lang.temp.

Section tpreinst.
  Context {lang : lang.t}.

  (* TODO: this type probably does not need to be parametric in [lang.t]
     The only meaningful instantation is [lang.cpp]
   *)
  Record tpreinst' : Set := TPreInst {
    tpreinst_name : temp_name;
    tpreinst_args : list (temp_arg' lang);
  }.

  #[global] Instance tpreinst'_inhabited : Inhabited tpreinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tpreinst'_eq_dec : EqDecision tpreinst'.
  Proof. solve_decision. Defined.
End tpreinst.
Add Printing Constructor tpreinst'.
#[global] Arguments tpreinst' : clear implicits.
#[global] Arguments TPreInst {_} _ & _ : assert.

(** ** Template instances *)
Section tinst.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {lang : lang.t} {V : Type@{uV}}.

  Record tinst' : Type@{uV} := TInst {
    tinst_params : list (temp_param' lang.temp);
    tinst_args : list (temp_arg' lang);
    tinst_value : V;
  }.

  #[global] Instance tinst'_inhabited `{!Inhabited V} : Inhabited tinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tinst'_eq_dec
      `{!EqDecision V} :
    EqDecision tinst'.
  Proof. solve_decision. Defined.
End tinst.
Add Printing Constructor tinst'.
#[global] Arguments tinst' : clear implicits.
#[global] Arguments TInst {_ _} _ _ & _ : assert.

Notation temp_param := (temp_param' lang.cpp).
Notation temp_arg := (temp_arg' lang.cpp).

Require Import bedrock.lang.cpp.syntax.translation_unit.

(** ** Templated values *)
Section template.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {V : Type@{uV}}.

  Record template : Type@{uV} := Template {
    template_params : list Mtemp_param;
    template_value : V;
  }.

  #[global] Instance template_inhabited `{!Inhabited V} : Inhabited template.
  Proof. solve_inhabited. Qed.

  #[global] Instance template_eq_dec `{!EqDecision V} :
    EqDecision template.
  Proof. solve_decision. Defined.
End template.
Add Printing Constructor template.
#[global] Arguments template : clear implicits.
#[global] Arguments Template {_} _ & _ : assert.

#[universes(polymorphic)]
Section template.
  Import UPoly.

  #[global] Instance template_fmap : FMap template := fun A B f t =>
    Template t.(template_params) (f t.(template_value)).

  #[global] Instance template_traverse : Traverse template := fun F _ _ _ A B f t =>
    Template t.(template_params) <$> f t.(template_value).
End template.

Import lang.
Notation Mtpreinst := (tpreinst' temp).
Notation Mtinst := (tinst' temp).
Notation MUnion := (Union' temp).
Notation MStruct := (Struct' temp).
Notation MFunctionBody := (FunctionBody' temp).
Notation MFunc := (Func' temp).
Notation MMethod := (Method' temp).
Notation MCtor := (Ctor' temp).
Notation MDtor := (Dtor' temp).
Notation MObjValue := (ObjValue' temp).
Notation MGlobDecl := (GlobDecl' temp).
Notation MGlobalInit := (GlobalInit' temp).
Notation MGlobalInitializer := (GlobalInitializer' temp).
Notation MInitializer := (Initializer' temp).
Notation MMember := (Member' temp).
Notation MInitializerBlock := (InitializerBlock' temp).
Notation Mfield_name := (field_name.t lang.temp).
Notation MInitPath := (InitPath' lang.temp).

(** ** Template TUs *)
(**
Template TUs house all templated code in a translation unit and relate
non-templated code induced by template application to the applied
template and its arguments.
*)
Definition Msymbol_table : Type := TM.t (template MObjValue).
Definition Mtype_table : Type := TM.t (template MGlobDecl).
Definition Malias_table : Type := TM.t (template Mtype).
Definition Minstance_table : Type := NM.t Mtpreinst.
Record Mtranslation_unit : Type := {
  msymbols : Msymbol_table;
  mtypes : Mtype_table;
  maliases : Malias_table;	(* we eschew <<Gtypedef>> for now *)
  minstances : Minstance_table
}.
