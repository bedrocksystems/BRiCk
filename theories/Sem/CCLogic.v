Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ClassicalDescription.

From Coq.Classes Require Import
     RelationClasses Morphisms.

From ChargeCore.SepAlg Require Import SepAlg.

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
  Definition carrier := Type.

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

  Parameter carrier_monoid : Type.

  (* carrier_monoid has to be guarded against duplicability *)
  Parameter carrier_guard : carrier_monoid -> list carrier_monoid -> mpred.
  Variable guard_container : list carrier_monoid.

  (*A generic fractional points to relation encoded using monoids x points to v with permission p.  
   Ex: logical_fptsto FracPerm (bookeeping_already_existing_resources) (QPermission frac) x v 
  *)
  Axiom logical_fptsto: forall  (perm : carrier_monoid) (guard : In perm guard_container)  (p : Set (*has to be perm*)) (x : val) (v : val), mpred.

  (*A generic ghost location gl and a value kept gv.  ghost *)
  Axiom logical_ghost: forall (ghost : carrier_monoid) (guard : In ghost guard_container)  (gl : Set (*has to be ghost*)) (gv : val), mpred.

  (*Introducing ghost*)
  (*
    Gregory suggests emp |- Exists g. g:m
  *)
  Parameter wp_ghst : Expr -> (val -> mpred) -> mpred.

   (*
     {P} E {Q}
    ------------
    {P} E {Q * exists l. l:g} //ghost location l carries the ghost resource g
   *)

  (**************************************
    A General Note to Gregory : If we want to refer to resources encoded via monoids -- let's say Pg -- then we have to bookkeep/pass
    guard and containers (guard: In monoid_instance guard_container). Specs below assume that we do not refer to any resource encoded 
    via monoids so there exists no guard and monoid container that we defined above. In case we want you can introduce them to the specs below.
  **************************************)

  (*******Atomic Instruction Specification*******)

  (*todo(isk): Ask Gregory the magic wand.*)
  Axiom rule_ghost_intro:
  forall  g P E Qp CMI (guard: In CMI guard_container) (ptriple: P |-- (wp_ghst E Qp)),
     P |-- ( wp_ghst E (fun v =>  (Qp v) ** (Exists l, logical_ghost CMI  guard l g))).
 
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
 (* list ValCat * Expr*)
  Parameter wp_atom : AtomicOp -> list val -> type -> (val -> mpred) -> mpred.

  Axiom wp_rhs_atomic: forall rslv ti r ao es ty Q,
    wps (wpAnys (resolve:=rslv) ti r) es  (fun (vs : list val) (free : FreeTemps) => wp_atom ao vs ty (fun v=> Q v free)) empSP
        |-- wp_rhs (resolve:=rslv) ti r (Eatomic ao es ty) Q.
  
  Definition atomdec (P: Prop) :=
   if (excluded_middle_informative P) then true else false.

  (*Ideas adopted from the paper: Relaxed Separation Logic: A program logic for C11 Concurrency -- Vefeiadis et al. *)

  (*Facts that needs to hold when a location is initialized*)
  Parameter Init: val -> mpred.
  
  (*Atomic CAS access permission*)
  Parameter AtomCASPerm :  val -> (val -> mpred) -> mpred .
  
  (*Atomic READ access permission*)
  Parameter AtomRDPerm: val -> (val -> mpred) -> mpred.
  
    (*Atomic WRITE access permission*)
  Parameter AtomWRTPerm: val -> (val -> mpred) -> mpred.
  
  (*Init is freely duplicable*)
  Axiom Persistent_Initialization : forall l , Init  l -|- Init  l ** Init  l.
  
  (*Atomic CAS access permission is duplicable*)
  Axiom Persistent_CASPerm : forall l LocInv,  AtomCASPerm l LocInv -|- AtomCASPerm l LocInv  ** AtomCASPerm l LocInv.

  (*Atomic load access permission is splittable and joinable.
    We want multiple readers should have accesses 
    LocInv' l ** LocInv -|- Exists LocInv''. LocInv
   *)
(* Correct  Parameter Composable_LocInv: val -> (val -> mpred) -> (val->mpred) -> (val->mpred) -> mpred.*)
  
  (*Any two reads in the multiple reader env. is allowed
   Thus, read permissions should be splittable and joinable
  
   *)
(*  Axiom Splittable_RDPerm : forall LocInv LocInv' l vcat ,  AtomRDPerm l LocInv  ** AtomRDPerm l LocInv'  -|-
                                                                       Exists LocInv'', LocInv'' (get_val_of_expr vcat l) **
                                                                              (Composable_LocInv (get_val_of_expr vcat l) LocInv' LocInv LocInv'').
*)

  (*  Axiom Splittable_WRTPerm : forall LocInv LocInv' l vcat, AtomWRTPerm l LocInv ** AtomWRTPerm l LocInv' -|-
                                                                       Exists LocInv''.*)
  (* r := l.load -- we can think of this as r := l.load(acc_type) *)
  (*todo(isk): give up the permission to read the same value again with same permission *)
  Axiom rule_atomic_load: forall (acc_type:type)  l (LocInv: val -> mpred),
      (Init  l ** AtomRDPerm l LocInv) |--
            (wp_atom AO__atomic_load (l::nil) acc_type
            (fun r => LocInv r)).

 
  (* l.store(v) -- we can think of it as l.store(v,acc_type)
     
  *)
   Axiom rule_atomic_store : forall (acc_type:type) v l (LocInv: val -> mpred),
      (AtomWRTPerm l LocInv ** LocInv l)
        |-- (wp_atom AO__atomic_store (l::v::nil) acc_type
            (fun r => Init l ** AtomWRTPerm l LocInv)).
  
  
  (*atomic compare and exchange rule*)
  Axiom rule_atomic_compare_exchange :
    forall P E E' E'' Qp  Q
           (acc_type : type) 
           (preserve:  P ** Qp E'  |-- Qp E'' ** Q),
      (P  ** AtomCASPerm E Qp)
        |-- (wp_atom AO__atomic_compare_exchange (E::E'::E''::nil) acc_type
            (fun x => if excluded_middle_informative (x = E') then
                                  Q else
                                  (P  ** AtomCASPerm E Qp))).
      
  (*Note: one more pass needed on this rule*)
  Axiom rule_atomic_fetch_add : 
    forall P released keptforinv E Qp pls
         (acc_type : type)
         (split: forall v,  P |-- (released v) ** (keptforinv v))
         (atom_xchng: forall v, ((released v) ** (AtomCASPerm E Qp)) |--
                        (wp_atom AO__atomic_compare_exchange  (E::v::pls::nil) acc_type
                                 (fun x:val => if (excluded_middle_informative(x = v)) then
                                                 (keptforinv v) else
                                                 ((released v) ** (AtomCASPerm E Qp))))),
      (P ** (AtomCASPerm E Qp)) |--
              (wp_atom AO__atomic_fetch_add (E::pls::nil) acc_type
                       (fun x:val => keptforinv x)).

End cclogic.

Declare Module CCL : cclogic.

Export CCL.

Export ILogic BILogic ILEmbed Later.
