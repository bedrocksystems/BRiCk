Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.

Require C.main_c.

Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).



(* representation of c-style strings, i.e. null-terminated *)
Fixpoint c_string (p : val) (ls : string) : mpred :=
  match ls with
  | EmptyString => tptsto T_schar p (Vchar "000"%char)
  | String c cs =>
    tptsto T_schar p (Vchar c) **
    c_string (offset_ptr p 1) cs
  end.

Section array.
  Context {T : Type}.
  Variable sz : Z.
  Variable (P : val -> T -> mpred).
  Fixpoint array' (p : val) (ls : list T) : mpred :=
    match ls with
    | nil => empSP
    | l :: ls =>
      P p l ** array' (offset_ptr p sz) ls
    end.
End array.

(* typed arrays *)
Definition tarray (t : type) {T : Type} (P : val -> T -> mpred)
           (base : val) (ls : list T) : mpred :=
  Exists sz, with_genv (fun g => [| @size_of g t sz |]) **
             array' sz P base ls.

Definition main_spec : function_spec' :=
  SFunction (Qmut T_int)
            (Qmut T_int :: Qmut
                  (Qconst (Tpointer
                             (Qmut
                                (Tpointer
                                   (Qmut (Tchar (Some 8%nat) true)))))) :: nil)
      (fun argc argv =>
         {| wpp_with := list string
          ; wpp_pre m :=
              [| Vint (Z.of_nat (length m)) = argc |] **
              tarray (Tpointer (Qmut (Tchar (Some 8%nat) true)))
                     (fun p v =>
                        Exists s, tptsto (Tpointer (Qmut (Tchar (Some 8%nat) true))) p s ** c_string p v)
                     argv m
          ; wpp_post m (r : val) := [| r = Vint 3 |] **
              tarray (Tpointer (Qmut (Tchar (Some 8%nat) true)))
                     (fun p v =>
                        Exists s, tptsto (Tpointer (Qmut (Tchar (Some 8%nat) true))) p s ** c_string p v)
                     argv m
         |}).

Definition main_cpp_spec (resolve : _) :=
  ti_cglob' (resolve:=resolve) "_Z4main" main_spec.
