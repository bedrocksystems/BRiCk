Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
      Semantics Logic Operator PLogic Wp Call.
From Cpp Require Import ChargeCompat.

From iris.base_logic.lib Require Import
     fancy_updates invariants cancelable_invariants wsat.
Import invG.

Section with_Σ.
  Context `{!invG Σ}.
  
  Local Notation mpred := (mpred Σ) (only parsing).
  Local Notation mpredI := (mpredI Σ) (only parsing).
  Local Notation mpredSI := (mpredSI Σ) (only parsing).
  Local Notation FreeTemps := (FreeTemps Σ) (only parsing).

  Definition wrap_shift (F : (val -> mpred) -> mpred) (Q : val -> mpred) : mpred :=
    Exists mid, (|={⊤,mid}=> F (fun result => |={mid,⊤}=> Q result))%I.

  (* semantics of atomic builtins
   * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
   *)
  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom : forall {resolve:genv}, AtomicOp -> list val -> type -> (val -> mpred) -> mpred.

  (* note that this rule captures all of the interesting reasoning about atomics
   * through the use of [wp_shift]
   *)
  Monomorphic Axiom wp_prval_atomic: forall rslv ti r ao es ty Q,
      wp_args (resolve:=rslv) ti r es (fun (vs : list val) (free : FreeTemps) =>
           wrap_shift (wp_atom (resolve:=rslv) ao vs (erase_qualifiers ty)) (fun v => Q v free))
      |-- wp_prval (resolve:=rslv) ti r (Eatomic ao es ty) Q.

  (* Ideas adopted from the paper:
   * Relaxed Separation Logic: A program logic for C11 Concurrency -- Vefeiadis et al.
   *)

  (*Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

  (* note(gmm): these are used for reading and writing values shared between
   * threads.
   * note(gmm): these look exactly like the standard read and write assertions
   * because all of the invariant reasoning is encapsulated in [wp_shift].
   *)
  Axiom wp_atom_load_cst
  : forall rslv memorder (acc_type:type) (l : val) (Q : val -> mpred),
      [| memorder = _SEQ_CST |] **
      (Exists v, (|> _at (_eq l) (tprim acc_type v) ** ltrue //\\ Q v))
      |-- wp_atom (resolve:=rslv) AO__atomic_load_n (l :: memorder :: nil) acc_type Q.

  Axiom wp_atom_store_cst
  : forall rslv memorder (acc_type:type) l Q val,
      [| memorder = _SEQ_CST |] **
      (Exists val, |> _at (_eq l) (tprim acc_type val)) **
      (|>_at (_eq l) (tprim acc_type val) -* Exists void, Q void)
      |-- wp_atom (resolve:=rslv) AO__atomic_store_n (l :: memorder :: val :: nil) Tvoid Q.

  (* atomic compare and exchange n *)
  Axiom wp_atom_compare_exchange_n:
    forall rslv val_p expected_p desired wk succmemord failmemord Q'
           (ty : type)
           expected,
      ([|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      Exists v,
         |> (_at (_eq expected_p) (tprim ty expected) **
             _at (_eq val_p) (tprim ty v)) **
         (([| v = expected |] -*
          |> (_at (_eq expected_p) (tprim ty expected) **
              _at (_eq val_p) (tprim ty desired)) -* Q' (Vbool true)) //\\
         ([| v <> expected |] -*
          |> (_at (_eq expected_p) (tprim ty v) **
              _at (_eq val_p) (tprim ty v)) -* Q' (Vbool false))))
       |-- wp_atom (resolve:=rslv) AO__atomic_compare_exchange_n
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) Tbool Q'.
  (* ^ note(gmm): this states that *both pointers are read atomically*.
   *)

  (* atomic compare and exchange rule
   *)
  Axiom wp_atom_compare_exchange:
    forall rslv val_p expected_p desired_p wk succmemord failmemord Q
      (ty : type)
      expected desired,
         (|> (_at (_eq expected_p) (tprim ty expected) **
              _at (_eq desired_p) (tprim ty desired)) **
         Exists val,|> _at (_eq val_p) (tprim ty val) **
         [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
         ((((* success *)
            [| val = expected |] **
            |> (_at (_eq expected_p) (tprim ty expected) **
                _at (_eq desired_p) (tprim ty desired) **
                _at (_eq val_p) (tprim ty desired)) -* Q (Vbool true))) //\\
          (((* failure *)
            [| val <> expected |] **
              |> (_at (_eq expected_p) (tprim ty val) **
                  _at (_eq desired_p) (tprim ty desired) **
                  _at (_eq val_p) (tprim ty val))) -* Q (Vbool false))))
       |-- wp_atom (resolve:=rslv) AO__atomic_compare_exchange
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q.

  (* atomic fetch and xxx rule *)
  Definition wp_fetch_xxx ao op : Prop :=
    forall rslv E pls memorder Q (acc_type : type),
      [| memorder = _SEQ_CST |] **
         (Exists v,
          |> _at (_eq E) (tprim acc_type v) **
          Exists v', [| eval_binop (resolve:=rslv) op acc_type acc_type acc_type v pls v' |] **
                     |> (_at (_eq E) (tprim acc_type v') -* Q v))
      |-- wp_atom (resolve:=rslv) ao (E::memorder::pls::nil) acc_type Q.

  Ltac fetch_xxx ao op :=
    let G := eval unfold wp_fetch_xxx in (wp_fetch_xxx ao op) in exact G.

  Axiom wp_atom_fetch_add : ltac:(fetch_xxx AO__atomic_fetch_add Badd).
  Axiom wp_atom_fetch_sub : ltac:(fetch_xxx AO__atomic_fetch_sub Bsub).
  Axiom wp_atom_fetch_and : ltac:(fetch_xxx AO__atomic_fetch_and Band).
  Axiom wp_atom_fetch_xor : ltac:(fetch_xxx AO__atomic_fetch_xor Bxor).
  Axiom wp_atom_fetch_or  : ltac:(fetch_xxx AO__atomic_fetch_or  Bor).

  (* atomic xxx and fetch rule *)
  Definition wp_xxx_fetch ao op : Prop :=
    forall rslv E pls memorder Q (acc_type : type),
      [| memorder = _SEQ_CST |] **
         (Exists v,
          |> _at (_eq E) (tprim acc_type v) **
          Exists v', [| eval_binop (resolve:=rslv) op acc_type acc_type acc_type v pls v' |] **
                     |> (_at (_eq E) (tprim acc_type v') -* Q v'))
      |-- wp_atom (resolve:=rslv) ao (E::memorder::pls::nil) acc_type Q.

(*
  Definition wp_xxx_fetch ao op : Prop :=
    forall q P E Qp pls memorder Q Q'
         (acc_type : type)
         (split: forall v,  P ** Qp v |--
                         Exists v', [| eval_binop op acc_type acc_type acc_type v pls v' |] **
                                    Qp v' ** Q v'),
      Fp_readable q ->
         P ** _at (_eq E) (AtomInv q acc_type Qp) **
         [| memorder = _SEQ_CST |] **
         (Forall x, (_at (_eq E) (AtomInv q acc_type Qp) ** Q x) -* Q' x)
       |-- wp_atom ao (E::pls::memorder::nil) acc_type Q'.
*)

  Ltac xxx_fetch ao op :=
    let G := eval unfold wp_xxx_fetch in (wp_xxx_fetch ao op) in exact G.

  Axiom wp_atom_add_fetch : ltac:(xxx_fetch AO__atomic_add_fetch Badd).
  Axiom wp_atom_sub_fetch : ltac:(xxx_fetch AO__atomic_sub_fetch Bsub).
  Axiom wp_atom_and_fetch : ltac:(xxx_fetch AO__atomic_and_fetch Band).
  Axiom wp_atom_xor_fetch : ltac:(xxx_fetch AO__atomic_xor_fetch Bxor).
  Axiom wp_atom_or_fetch  : ltac:(xxx_fetch AO__atomic_or_fetch  Bor).
  
End with_Σ.
