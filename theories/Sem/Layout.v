Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic PLogic CompilationUnit.

Axiom uninit_class_fwd
  : forall cls base st,
    denoteGlobal cls (Gstruct st) **
    _at (_eq base) (uninit (Tref cls))
    |-- _at (_eq base)
            (sepSPs (List.map (fun gn =>
                                 _offsetR (_super cls gn) (uninit (Tref gn))) st.(s_bases) ++
                     List.map (fun '(n,t,_) =>
                            (* todo(gmm): there is a problem with references in this code.
                             *)
                                 _offsetR
                                   (_field {| f_name := n ; f_type := cls |})
                                   (uninit (drop_qualifiers t))) st.(s_fields))).

Axiom tany_class_bwd
: forall cls base st,
    denoteGlobal cls (Gstruct st) **
    _at (_eq base)
              (sepSPs (List.map (fun gn =>
                                   _offsetR (_super cls gn) (tany (Tref gn))) st.(s_bases) ++
                       List.map (fun '(n,t,_) =>
                                   _offsetR (_field {| f_name := n ; f_type := cls |})
                                            (tany (drop_qualifiers t))) st.(s_fields)))
    |-- _at (_eq base) (tany (Tref cls)).

Axiom uninit_array : forall t n,
    uninit (Tarray t n)
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (uninit t)) (seq 0 (BinNatDef.N.to_nat n))).

Axiom tany_array : forall t n,
    tany (Tarray t n)
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (tany t)) (seq 0 (BinNatDef.N.to_nat n))).
