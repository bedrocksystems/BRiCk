Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Auto.

Require C.main_c.
Require Import C.main_c_spec.


Lemma can_get_element {T} :
  forall (x3 : list T) (x4 : Z),
    0 <= x4 <= Z.of_nat (Datatypes.length x3) ->
    x4 < Z.of_nat (Datatypes.length x3) ->
    exists (v : T) (i : nat), Z.of_nat i = x4 /\ nth_error x3 i = Some v.
Proof. Admitted.

(* soundness of the specification *)
Theorem main_cpp_sound : forall (resolve : genv),
    denoteModule main_c.module |-- spec resolve.
Proof.
  intros.
  simpl.
  unfold spec.
  start_module.

  verifyF_forget "_Z4main".
  { (* ::main(int argc, char* argv[]) *)
    start_proof.
    rewrite denoteModule_weaken.
    simplifying.
    work.
    (* this is the loop invariant
     * todo(gmm): i need to clean this up a lot!
     *)
    transitivity (
        (ti_cglob' (resolve:=resolve) "_Z6putstr" putstr_spec **
         tlocal x1 (Tint None true) "argc" x **
         tlocal x1 (Tpointer (Qmut (Tpointer (Qmut T_char)))) "argv" x0) **
         (Forall res : val, [| res = 0 |] ** args_array x0 x3 -* x2 res) **
         args_array x0 x3 **
         Exists i,
           [| 0 <= i <= Z.of_nat (Datatypes.length x3) |] **
           tlocal x1 T_int "i" i).
    { work. }
    eapply wp_for.
    simplifying.
    work.
    simplifying.
    work.
    { simpl.
      eapply embedPropR.
      eapply eval_lt; try reflexivity. subst. reflexivity. }
    rewrite is_true_int.
    destruct (ZArith_dec.Z_lt_ge_dec x4 (Z.of_nat (Datatypes.length x3))).
    { simpl.
      simplifying.
      unfold args_array.
      assert (exists v, exists i, Z.of_nat i = x4 /\ nth_error x3 i = Some v).
      { eapply can_get_element; eauto. }
      destruct H1 as [ ? [ ? [ ? ? ] ] ].
      rewrite tarray_cell; eauto with size_of.
      rewrite <- wp_lhs_subscript.
      simplifying.
      simpl.
      work.
      simplifying.
      work.
      { subst. work. }
      simplifying. simpl.
      unfold tlocal.
      lift_ex_l.
      perm_left ltac:(idtac; eapply (Lemmas.learn_bounds x4); simpl; intros).
      work.
      instantiate (1:=Vint (x4 + 1)).
      eapply provable_star.
      { eapply eval_add. reflexivity.
        eapply has_type_int_any. }
      work.
      rewrite tarray_cell with (ms:=x3); eauto with size_of.
      work. }
    { simpl.
      unfold Sskip.
      simplifying.
      work.
      done_proof. } }

  finish_module.
  Unshelve.
  all: eassumption.
Qed.
