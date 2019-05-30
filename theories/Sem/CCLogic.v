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
  Axiom logical_fptsto: forall  (perm : carrier_monoid) (guard : In perm guard_container)  (p : Set (*todo(isk): has to be perm*)) (x : val) (v : val), mpred.

  (*A generic ghost location gl and a value kept gv.  ghost *)
  Axiom logical_ghost: forall (ghost : carrier_monoid) (guard : In ghost guard_container)  (gl : Set (*todo(isk): has to be ghost*)) (gv : val), mpred.

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
    | AO__atomic_load -- DONE
    | AO__atomic_load_n
    | AO__atomic_store -- DONE
    | AO__atomic_store_n
    | AO__atomic_compare_exchange -- DONE
    | AO__atomic_compare_exchange_n
    | AO__atomic_exchange
    | AO__atomic_exchange_n
    | AO__atomic_fetch_add -- DONE
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
  Parameter AtomCASPerm :  val -> (val ->mpred) -> mpred .
  
  (*Atomic READ access permission*)
  Parameter AtomRDPerm: val -> (val -> mpred) -> mpred.
  
  (*Atomic WRITE access permission*)
  Parameter AtomWRTPerm: val -> (val -> mpred) -> mpred.

  (* Perm LocInv l * Perm LocInv' l -|- Perm LocInv*LocInv' l 
    Composability of two location invariant maps: val -> mpred on location l
    todo(isk): Existentials are weak?
   *)
  Axiom Splittable_RDPerm: forall (LocInv: val->mpred) (LocInv':val->mpred) l ,  AtomRDPerm l LocInv **  AtomRDPerm l LocInv' 
                          -|- Exists v, (Exists LocInv'', (LocInv'' v -* (LocInv' v ** LocInv v)) //\\ (AtomRDPerm v LocInv'')). 
  
  (*Init is freely duplicable*)
  Axiom Persistent_Initialization : forall l , Init  l -|- Init  l ** Init  l.
  
  (*Atomic CAS access permission is duplicable*)
  Axiom Persistent_CASPerm : forall l LocInv,  AtomCASPerm l LocInv -|- AtomCASPerm l LocInv  ** AtomCASPerm l LocInv.

  (* *)
  Axiom Splittable_WRTPerm: forall (LocInv: val->mpred) (LocInv':val->mpred) l ,  AtomRDPerm l LocInv **  AtomRDPerm l LocInv' 
                           -|- Exists v, (Exists LocInv'', (LocInv'' v -* (LocInv' v \\// LocInv v)) //\\ (AtomRDPerm v LocInv'')).
  
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
                                  P  ** AtomCASPerm E Qp)).
      
  (*atomic fetch and add rule*)
  Axiom rule_atomic_fetch_add : 
    forall P released keptforinv E Qp pls
         (acc_type : type)
         (split: forall v,  P |-- (released v) ** (keptforinv v))
         (atom_xchng: forall v, ((released v) ** (AtomCASPerm E Qp)) |--
                        (wp_atom AO__atomic_compare_exchange  (E::v::pls::nil) acc_type
                                 (fun x => if (excluded_middle_informative(x = v)) then
                                                 (keptforinv v) else
                                                 ((released v) ** (AtomCASPerm E Qp))))),
      (P ** (AtomCASPerm E Qp)) |--
              (wp_atom AO__atomic_fetch_add (E::pls::nil) acc_type
                       (fun x:val => keptforinv x)).

  (****************A Lock Example***************)
  
  (*
  ------------------------------
   Definition new_lock := 
      {I}
      x := alloc();
     {I*AtomCASPerm*AtomWRTPerm}
      x:= 0;
     {LockPerm x I}

   {I} new_lock() {x. LockPerm x I}
  ------------------------------
  Definition lock (x) := 
    {LockPerm x I}
    do{
      {LockPerm x I}
      r := CAS(x,0,1); 
      { (r. (r=0 /\ I) \/ (r=1 /\ LockPerm x I ) )}     

    }while(!r)
    {I ** LockPerm x I}


   SPEC: {LockPerm x I} lock(x) {I ** LockPerm x I}
  ----------------------------------------
   Definition unlock(x) := 
     x := 0;

   SPEC: {I ** LockPerm x I} unlock(x) {LockPerm x I}
   *** We use AtomWRTPerm of LockPerm
   -----------------------------------------

   We also have to give spec to alloc for init.
   {emp} alloc  {I*AtomCASPerm*AtomWRTPerm}
   *)
 
  (* LocInv asserts the invariant associated with the location implementing lock.
     When the lock is held it asserts empty ownership otherwise it asserts the 
     ownership of invariant I ( which is picked by verification engineer)
   *)
  Parameter s:val. (*succ*)
  Parameter f:val. (*fail*)

  (*LocInv asserts the invariant I associated with the location x implementing lock
   When lock is held 
  *)
  Definition LockInv  I ( x: val) :=
    if   excluded_middle_informative (  x = f) then
      empSP   else
      if excluded_middle_informative (  x = s) then
         I     else
        lfalse.
  (*
   LockPerm asserts permission to access to a lock.
   It contains AtomPerm to access the lock via CAS
   *)
  Definition LockPerm x I  :=  AtomWRTPerm  x (LockInv I) **  AtomCASPerm x (LockInv I) ** Init x .
  (**********The lock example ends***********)
  
End cclogic.

Declare Module CCL : cclogic.

Export CCL.

Export ILogic BILogic ILEmbed Later.
