(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.dispatch.
Require Import bedrock.lang.cpp.semantics.subtyping.
Require Import bedrock.lang.cpp.logic.dispatch.

Require Import bedrocktest.virt_cpp.
#[global] Instance resolve : genv.genv :=
  genv.Build_genv module W32.

#[global] Instance AA : @class_derives _ "_Z1A" "_Z1A".
Proof. econstructor; reflexivity. Defined.

#[global] Instance AB : @class_derives _ "_Z1B" "_Z1A".
Proof. econstructor; [ reflexivity | simpl; tauto | refine _ ]. Defined.

#[global] Instance AC : @class_derives _ "_Z1C" "_Z1A".
Proof. econstructor; [ reflexivity | simpl; tauto | refine _ ]. Defined.

#[global] Instance AD : @class_derives _ "_Z1D" "_Z1A".
Proof. econstructor; [ reflexivity | simpl; tauto | refine _ ]. Defined.

Goal (dispatch _ AC "_ZN1A3fooEv").(derivation) = AC.
Proof. reflexivity. Qed.

Goal let deriv := dispatch _ AC "_ZN1A3fooEv" in
     match deriv.(vimpl) with
     | None => False
     | Some _ => deriv.(derivation) = AC
     end.
Proof. reflexivity. Qed.

Goal let deriv := dispatch _ AD "_ZN1A3fooEv" in
     match deriv.(vimpl) with
     | None => False
     | Some _ => deriv.(derivation) = AD
     end.
Proof. reflexivity. Qed.
