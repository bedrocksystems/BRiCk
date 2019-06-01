Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.QArith.QArith.

Require Import Coq.ssr.ssrbool.

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

  Structure SA := 
  { s_type :> Type;
    s_bot: s_type;
    s_top: s_type; 
    s_undef: s_type;
    s_compose: s_type -> s_type -> s_type;
    s_compose_com: forall s1 s2, s_compose s1 s2 = s_compose s2 s1;
    s_compose_assoc: forall s1 s2 s3, s_compose (s_compose s1 s2) s3 = s_compose s1 (s_compose s2 s3);
    s_compose_cancel: forall s1 s1' s2, s_compose s1 s2 <> s_undef ->
                                        s_compose s1 s2 = s_compose s1' s2 -> s1 = s1';
    s_compose_bot: forall s1 s2, s_compose s1 s2 = s_bot -> s1 = s_bot /\ s2 = s_bot;
    s_compose_w_bot: forall s, s_compose s s_bot = s;
    s_compose_w_undef: forall s, s_compose s s_undef = s_undef;
    s_compose_complete_top: forall s, s_compose s_top s <> s_undef -> s = s_bot;
    s_top_not_bot: s_top <> s_bot;
    s_top_not_undef: s_top <> s_undef;
    s_ord : rel s_type; 
    s_ord_refl : reflexive s_ord;
    s_ord_antis : antisymmetric s_ord;
    s_ord_trans : transitive s_ord;
    s_ord_total : total s_ord
  }.
  
  (*Example carrier*)
  Inductive FracPerm_Carrier :=
  | FPerm (f:Q) (UNIT: 0 <= f <= 1)
  | FPermUndef.

 Axiom FPerm_Equal: forall f g UNITf UNITg ,
      f = g -> FPerm f UNITf  = FPerm g UNITg .
 
 (*Composition over fractional permissions*)
 Definition FPerm_Compose f g :=
   match f, g return FracPerm_Carrier with
   | FPermUndef, _ => FPermUndef
   | _, FPermUndef => FPermUndef
   | FPerm f' _ , FPerm g' _ => match excluded_middle_informative (0 <= f' + g' <= 1) with
                                |left Pred => FPerm (f' + g') Pred
                                | right _ => FPermUndef
                                               
                                end
   end.
 
 (*Order*)
 Definition FPerm_Order f g : bool := 
  match f, g with
    | FPermUndef, _ => true
    | FPerm _ _, FPermUndef => false
    | FPerm f' _, FPerm g' _ => if (excluded_middle_informative  (f' <= g')) then true else false
  end.
      
  (*
    Here is an example to a carrier_monoid
   *)

  (*We keep this just for terminology*)
  Parameter carrier_monoid : Type.

  (*Example carrier monoid*)
  Program Definition FracPerm_Carrier_Monoid := 
  {| s_type := FracPerm_Carrier; 
     s_bot := FPerm 0 _; 
     s_top := FPerm 1 _; 
     s_undef := FPermUndef;
     s_compose := FPerm_Compose; 
     s_ord := FPerm_Order 
  |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
             
 (*A note to Gregory, If I were to paramterize mpred (p:FracPerm_Carrier_Monoid) ... 
  I wouldn't need this inductive type.
  THIS WOUDL BE A NEAT SOLUTION.

  I dont like them to be separate axioms. It is a ad-hoc solution, but lets keep it as it for now. 
 *)

  Axiom logical_fptsto: forall (Prm: SA) (p: Prm)  (l: val) (v : val), mpred.
  
  Program Definition Frac_PointsTo l q v :=
    match excluded_middle_informative (0 <= q  <= 1)  with
     | right _ => lfalse
     | left _ => match excluded_middle_informative (q == 0) with
                    | left _ => empSP 
                    | right _ =>  logical_fptsto FracPerm_Carrier_Monoid  (FPerm  q _)  l v
                  end  
   end.
      
  (*Similaryl one can encode ghost state using SA*) 
  (*
   This type extends as we introduce new logical assertions such as logical_ghost etc. 
   A generic ghost location gl and a value kept gv. 
   
  A NOTE to Gregory: I did not do bookeeping of Monoids -- guard: In MONID LIST MONOID -- for fractional permis  sions and pointsto but in general we have to have the following structure for all logical predicates.  
   *)
  Variable guard_container : list SA.
  Axiom logical_ghost: forall (ghost : SA) (guard : In ghost guard_container)  (gl : ghost) (gv : val), mpred.

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
  Axiom rule_ghost_intro:
  forall  g P E Qp CMI (guard: In CMI guard_container) (ptriple: P |-- (wp_ghst E Qp)),
     P |-- ( wp_ghst E (fun v =>  (Qp v) ** (Exists l, logical_ghost CMI  guard l g))). 

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

  (*Generate atomic access token via consuming the initially holding invariant*)
  Axiom Generate_CASPerm : forall x (t:type) (Inv:val->mpred) , Exists v, tptsto t x v **  Inv v  |-- AtomCASPerm x Inv.

  (*Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.
  Definition Vbool (b : bool) :=
    Vint (if b then 1 else 0).
  
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
  
  
  (*atomic compare and exchange rule
   todo(isk): check the number of args -- 6 -- and order of them.
  *)
  Axiom rule_atomic_compare_exchange :
    forall P E E' E'' Qp  Q
           (acc_type : type) 
           (preserve:  P ** Qp E'  |-- Qp E'' ** Q),
      (P  ** AtomCASPerm E Qp)
        |-- (wp_atom AO__atomic_compare_exchange (E::E'::E''::nil) acc_type
            (fun x => if excluded_middle_informative (x = E') then
                                  Q else
                        P  ** AtomCASPerm E Qp)).
  (*Atomic compare and exchange n -- we use this in spinlock module*)
  Axiom rule_atomic_compare_exchange_n:
    forall P E E' E'' wk succmemord failmemord Qp Q'  (Q:mpred)
           (acc_type : type) 
           (preserve:  P ** Qp E'  |-- Qp E'' ** Q),
      (P  ** AtomCASPerm E Qp ** [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |]) **
       (Forall x, (if excluded_middle_informative (x = E') then
                                  Q else
                    P  ** AtomCASPerm E Qp) -* Q' x) |-- 
       wp_atom AO__atomic_compare_exchange_n (E::succmemord::E'::failmemord::E''::wk::nil) acc_type Q'.
         
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
  
End cclogic.

Declare Module CCL : cclogic.

Export CCL.

Export ILogic BILogic ILEmbed Later.
