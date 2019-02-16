Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.

Require C.main_c.
Require Import C.array.

Definition args_array (p : val) (ls : list string) : mpred :=
  tarray (Tpointer (Qmut T_char))
    (fun (p : val) (v : string) =>
       Exists s : val,
         tptsto (Tpointer (Qmut T_char)) p s ** c_string s v) p
    ls.


Definition putstr_spec : function_spec' :=
  SFunction (Qmut Tvoid) (Qmut (Tpointer (Qmut T_char)) :: nil)
            (fun p =>
               {| wpp_with := string
                ; wpp_pre s := c_string p s
                ; wpp_post s _ := c_string p s
                |}).

Definition main_spec : function_spec' :=
  SFunction (Qmut T_int)
            (Qmut T_int :: Qmut
                  (Qconst (Tpointer
                             (Qmut
                                (Tpointer
                                   (Qmut T_char))))) :: nil)
      (fun argc argv =>
         {| wpp_with := list string
          ; wpp_pre m :=
              [| Vint (Z.of_nat (length m)) = argc |] **
              args_array argv m
          ; wpp_post m (r : val) := [| r = Vint 0 |] **
              args_array argv m
         |}).

Definition spec (resolve : _) :=
  ti_cglob' (resolve:=resolve) "_Z6putstr" putstr_spec -*
  ti_cglob' (resolve:=resolve) "_Z4main" main_spec.

Export C.array.