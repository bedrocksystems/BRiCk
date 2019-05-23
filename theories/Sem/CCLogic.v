Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith_base.

From Coq.Classes Require Import
     RelationClasses Morphisms.


From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics Logic Expr.
From Cpp.Auto Require Import
     Discharge.

Module Type cclogic.


  (* fractional points to relation val_{Q} -> val
     I comment out this fractional points to relation
     as we can encode this through RA. So there is no
     need for a hard-coded default one.
 *)
  (*Parameter fptsto : val -> Q -> val -> mpred.*)
  
  (****** Logical State ********)
  
  (*carrier is the data type through which we would like to 
    represent bookkeeping in resource algebra. Simply, the 
    type to be passed to the resource algebra -- carrier.
    ex: Inductive FracPerm_Carrier :=
                | QPermission (f:Q)
                | QPermissionUndef.
    Note: Deciding what the carrier is going to be depends on
    the verification problem.
  *)
  Parameter carrier : Type.

  (*
    Resource Algebra Record: TODO: Ask Gregory the type for the ChargeCore. 
    For now let's call it carrier_monoid but normally it has to have 
    
    Here is an example to a carrier_monoid
    
    Program Definition FracPerm_{
      RA :> Type // Ex: we pass our FracPerm_Carrier type
                 // Ex: we create one instance of FracPerm via 
                 // a constructor of the carrier QPermission(1/2)

      RA_emp     // Ex: Define what is Emp for FracPerm_Carrier and pass it here
      RA_plus/join // Ex: Composition of the two FracPerm_Carriers has to be defined and passed here
      ...
      RA_refl
      RA_trans
      //structural rules    
    }

   *)
  Parameter carrier_monoid : Type. (*This will change once I know Chargecore RA*)

  (* carrier_monoid has to be guarded against duplicability *)
  Parameter carrier_guard : carrier_monoid -> list carrier_monoid -> mpred.
  Variable guard_container : list carrier_monoid.

  (*A generic fractional points to relation encoded using monoids x points to v with permission p.  
   Ex: logical_fptsto FracPerm (bookeeping_already_existing_resources) (QPermission frac) x v 
  *)
  Axiom logical_fptsto: forall  (perm : carrier_monoid) (guard : In perm guard_container)  (p : Set) (x : val) (v : val), mpred.

  (*A generic ghost location gl and a value kept gv.  ghost *)
  Axiom logical_ghost: forall (ghost : carrier_monoid) (guard : In ghost guard_container)  (gl : Set) (gv : val), mpred.

  (*Introducing ghost*)
  Parameter mwand : mpred -> mpred -> Prop. (*todo(ISK): I dont want to have one more pred for Prop->mpred. I need -* in mpred *)
  Parameter wp_ghst : Expr -> (val -> mpred) -> mpred.

  (*
       {P} E {Q}
    ------------
    {P} E {Q * exists l. l:g} //ghost locatoin l carries the ghost resource g
   *)

  (*todo(isk): Ask Gregory the magic wand.*)
  Axiom rule_ghost_intro:
  forall  g P E Q CMI (guard: In CMI guard_container) (ptriple: mwand P (wp_ghst E Q)),
     mwand P ( wp_ghst E (fun v =>  (Q v) ** (Exists l, logical_ghost CMI  guard l g))).
 
    (********ATOMIC EXPRESSIONS*****)
    (*clang atomic expressions 
    Expression : Eatomic (_ : AtomicOp) (_ : list (ValCat * Expr)) (_ : type) where AtomicOP can be
    | AO__atomic_load
    | AO__atomic_load_n
    | AO__atomic_store
    | AO__atomic_store_n
    | AO__atomic_compare_exchange
    | AO__atomic_compare_exchange_n
    | AO__atomic_exchange
    | AO__atomic_exchange_n
    | AO__atomic_fetch_add
    | AO__atomic_fetch_sub
    | AO__atomic_fetch_and
    | AO__atomic_fetch_or
    | AO__atomic_fetch_xor
    | AO__atomic_fetch_nand
    | AO__atomic_add_fetch
    | AO__atomic_sub_fetch
    | AO__atomic_and_fetch
    | AO__atomic_or_fetch
    | AO__atomic_xor_fetch
    | AO__atomic_nand_fetch
   *)

  Parameter wp_atom : AtomicOp -> list (ValCat * Expr) -> type -> (val -> mpred) -> mpred.
   (* AtomPerm(E, Linv(E)) *)
  Parameter AtomPerm :  Expr -> (Expr -> mpred ) -> mpred .

  Parameter PureFact : val -> mpred.
 
  (*TODO(isk) ask Gregory the exact values for vcat and acc_type has to be passed *)
  Axiom rule_atomic_load: forall (acc_type:type) (vcat:ValCat) P E Q, mwand (P ** AtomPerm E Q)
                                                              (wp_atom AO__atomic_load ((vcat,E)::nil) acc_type (fun  x =>  PureFact x)).
                                                                                                                            
End cclogic.

Declare Module CCL : cclogic.

Export CCL.

Export ILogic BILogic ILEmbed Later.
