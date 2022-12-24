(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.bi.prelude.
Require Import bedrock.lang.cpp.bi.cfractional.
Require Import iris.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.

(**
Some representative examples. For the full story see
./split_cv_tests.v.
*)

Section EXAMPLES.
  Context {PROP : bi}.
  Context (R : cQp.t -> PROP) `{!cfractional.CFractional R}.

  Let R_as_fractional q : AsCFractional (R q) R q.
  Proof. exact: Build_AsCFractional. Qed.
  #[local] Existing Instance R_as_fractional.

  (**
  Splitting on [+] is always trivial.
  *)

  Let split_cv_cv cv1 cv2 :
    R (cv1 + cv2) |-- R cv1 ** R cv2.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_cv_mk cv c q :
    R (cv + cQp.mk c q) |-- R cv ** R (cQp.mk c q).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk_cv cv c q :
    R (cQp.mk c q + cv) |-- R (cQp.mk c q) ** R cv.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk_mk c1 c2 q1 q2 :
    R (cQp.mk c1 q1 + cQp.mk c2 q2) |-- R (cQp.mk c1 q1) ** R (cQp.mk c2 q2).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (**
  Splitting on [cQp.scale q] preserves the factor [q].
  *)
  Let split_scale p q1 q2 :
    R (cQp.scale p (q1 + q2)) |--
    R (cQp.scale p q1) **
    R (cQp.scale p q2).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_scale p q q1 q2 :
    R (cQp.scale p (cQp.scale q (q1 + q2))) |--
    R (cQp.scale p (cQp.scale q q1)) **
    R (cQp.scale p (cQp.scale q q2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (**
  Splitting [cQp.is_const] knows about [&&].
  *)

  Let split_andb c1 c2 q :
    R (cQp.mk (c1 && c2) q) |-- R (cQp.mk c1 (q/2)) ** R (cQp.mk c2 (q/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (** Otherwise, both sides get the same [cQp.is_const] after the split. *)

  Let split_mut :
    R (cQp.mut 1) |-- R (cQp.mut (1/2)) ** R (cQp.mut (1/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_const :
    R (cQp.const 1) |-- R (cQp.const (1/2)) ** R (cQp.const (1/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk c :
    R (cQp.mk c 1) |-- let Rhalf := R (cQp.mk c (1/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_cv cv :
    R cv |-- let Rhalf := R (cQp.mk (cQp.is_const cv) (cQp.frac cv/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (*
  Splitting fractions knows about a few constants and (some factors
  of) [q1 + q2].
  *)

  Let split_½ : R (cQp.mut (1/2)) |-- let Rhalf := R (cQp.mut (1/4)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_1 : R (cQp.mut 1) |-- let Rhalf := R (cQp.mut (1/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_q q : R (cQp.mut q) |-- let Rhalf := R (cQp.mut (q/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_sum q1 q2 : R (cQp.mut (q1 + q2)) |-- R (cQp.mut q1) ** R (cQp.mut q2).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_mul_l p q1 q2 :
    R (cQp.mut (p * (q1 + q2))) |-- R (cQp.mut (p * q1)) ** R (cQp.mut (p * q2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mul_r p q1 q2 :
    R (cQp.mut ((q1 + q2) * p)) |-- R (cQp.mut (q1 * p)) ** R (cQp.mut (q2 * p)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_div p q1 q2 :
    R (cQp.mut ((q1 + q2) / p)) |-- R (cQp.mut (q1 / p)) ** R (cQp.mut (q2 / p)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (**
  Combining two variables produces [+].
  *)
  Let combine_cv cv :
    R cv ** R cv |-- R (cv + cv).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_cv_cv cv1 cv2 :
    R cv1 ** R cv2 |-- R (cv1 + cv2).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (**
  Combining under [cQp.scale q] preserves the factor [q].
  *)
  Let combine_scale q q1 q2 :
    R (cQp.scale q q1) ** R (cQp.scale q q2) |-- R (cQp.scale q (q1 + q2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_scale p q q1 q2 :
    R (cQp.scale p (cQp.scale q q1)) **
    R (cQp.scale p (cQp.scale q q2)) |--
    R (cQp.scale p (cQp.scale q (q1 + q2))).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (**
  Combining anything else combines [cQp.is_const], [cQp.is_frac]
  componentwise and then folds [cQp.add] and eta reduces [cQp.mk].
  *)

  Let combine_cv_mk cv c :
    R cv ** R (cQp.mk c (1/2)) |-- R (cQp.mk (cQp.is_const cv && c) (cQp.frac cv + 1/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_cv cv c :
    R (cQp.mk c (1/2)) ** R cv|-- R (cQp.mk (c && cQp.is_const cv) (1/2 + cQp.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifing [cQp.is_const] given two concrete values *)

  Let combine_mut_mut :
    R (cQp.mut (1/2)) ** R (cQp.mut (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mut_const :
    R (cQp.mut (1/2)) ** R (cQp.const (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_const_mut :
    R (cQp.const (1/2)) ** R (cQp.mut (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_const :
    R (cQp.const (1/2)) ** R (cQp.const (1/2)) |-- R (cQp.const 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifing [cQp.is_const] given one concrete value *)

  Let combine_mut_var q cv :
    R (cQp.mut q) ** R cv |-- R (cQp.mut (q + cQp.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_var_mut q cv :
    R cv ** R (cQp.mut q) |-- R (cQp.mut (cQp.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_var q cv :
    R (cQp.const q) ** R cv |-- R (cQp.mk (cQp.is_const cv) (q + cQp.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_var_const q cv :
    R cv ** R (cQp.const q) |-- R (cQp.mk (cQp.is_const cv) (cQp.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mut_mk c :
    R (cQp.mut (1/2)) ** R (cQp.mk c (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_mut c :
    R (cQp.mk c (1/2)) ** R (cQp.mut (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_mk c :
    R (cQp.const (1/2)) ** R (cQp.mk c (1/2)) |-- R (cQp.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_const c :
    R (cQp.mk c (1/2)) ** R (cQp.const (1/2)) |-- R (cQp.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifying [cQp.is_const] given no concrete values *)

  Let combine_cv cv :
    let Rhalf := R (cQp.mk (cQp.is_const cv) (cQp.frac cv/2)) in Rhalf ** Rhalf |-- R cv.
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mk c :
    let Rhalf := R (cQp.mk c (1/2)) in Rhalf ** Rhalf |-- R (cQp.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_cv_mk cv c q :
    R cv ** R (cQp.mk c q) |-- R (cQp.mk (cQp.is_const cv && c) (cQp.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_cv cv c q :
    R (cQp.mk c q) ** R cv |-- R (cQp.mk (c && cQp.is_const cv) (q + cQp.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mk_mk c1 c2 q1 q2 :
    R (cQp.mk c1 q1) ** R (cQp.mk c2 q2) |-- R (cQp.mk (c1 && c2) (q1 + q2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (**
  Simpifying [cQp.frac] is pretty aggressive. We give a few examples.
  *)

  Let combine_quarter q : R (cQp.mut (q/4)) ** R (cQp.mut (q/4)) |-- R (cQp.mut (q/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_¼ : R (cQp.mut (1/4)) ** R (cQp.mut (1/4)) |-- R (cQp.mut (1/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_half q : R (cQp.mut (q/2)) ** R (cQp.mut (q/2)) |-- R (cQp.mut q).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_½ : R (cQp.mut (1/2)) ** R (cQp.mut (1/2)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine : R (cQp.mut (1/4)) ** R (cQp.mut (3/4)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine : R (cQp.mut (3/4)) ** R (cQp.mut (1/4)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine : R (cQp.mut (1/3)) ** R (cQp.mut (2/3)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine : R (cQp.mut (2/3)) ** R (cQp.mut (1/3)) |-- R (cQp.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mul_l p q1 q2 :
    R (cQp.mut (p * q1)) ** R (cQp.mut (p * q2)) |-- R (cQp.mut (p * (q1 + q2))).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mul_r p q1 q2 :
    R (cQp.mut (q1 * p)) ** R (cQp.mut (q2 * p)) |-- R (cQp.mut ((q1 + q2) * p)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_div p q1 q2 :
    R (cQp.mut (q1 / p)) ** R (cQp.mut (q2 / p)) |-- R (cQp.mut ((q1 + q2) / p)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

End EXAMPLES.
