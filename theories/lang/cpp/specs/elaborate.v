(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.
 *)
Require Import bedrock.lang.cpp.
Require Import bedrock.lang.cpp.specs.wp_spec_compat.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** determine if an argument is already materialized in the operand style.
   *)
  Definition mtype (t : type) : globname + type :=
    match erase_qualifiers t with
    | Tnamed cls => inl cls
    | ty => inr ty
    end.

  (** [elaborate' ret ts wpp args] builds a function specification around [wpp]
      assuming that [wpp] takes the arguments in [args] (in reverse order) and the
      remaining arguments in [ts].
   *)
  Fixpoint elaborate' (ret : type) (ts : list type) (wpp : WpSpec_cpp) (args : list val) : WpSpec mpredI ptr ptr :=
    match ts with
    | nil =>
        match mtype ret with
        | inl cls =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr [| Vptr pr = rv |]))
        | inr t =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr (_at pr (primR t 1 rv))))
        end
    | t :: ts =>
        match mtype t with
        | inl cls =>
            add_with (fun pv : ptr => add_arg pv (elaborate' ret ts wpp (args ++ [Vptr pv])))
        | inr t =>
            add_with (fun pv : ptr => add_with (fun v : val => add_arg pv (
                                           add_pre (_at pv (primR t 1 v)) (add_post (Exists v, _at pv (primR t 1 v))
                                                                                    (elaborate' ret ts wpp (args ++ [v]))))))
        end
    end.

  (** [elaborate ret ts wpp] is the elaborated version of the [wpp]
      (operand-based) spec that is based on materialized values.
   *)
  Definition elaborate (ret : type) (ts : list type) (wpp : WpSpec_cpp)
    : WpSpec mpredI ptr ptr :=
    elaborate' ret ts wpp nil.
End with_cpp.

