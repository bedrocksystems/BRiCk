Require Import iris.base_logic.lib.viewshifts.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.specs.
Require Import bedrock.lib.frac.

Section withSigma.
  Context {Sigma : gFunctors} {wsg: wsat.invG.invG Sigma} {cl: cancelable_invariants.cinvG Sigma}.

  (**
Suppose we have have a concurrent class `C` with operation `oa` that is *logically atomic*.
Suppose `oa` takes an integer as an argument.
For example, `C` could be a counter and `oa` could increment it by a given number.
The goal is to prove *atomicity refinement*: concurrent observers
can not observe a difference between the code and the model (which executes atomically).

First, we define a state transition system in Coq to model the class.
We pick a Coq type [T] that captures the state of a `C` object and
a step function [oa_step] that models the how `oa` changes the
state of the object. The following is one choice for the counter example:
 [T := Z], [oaStep i a := (i + a, tt)].
   *)

  Parameter T: Type.

  Parameter oa_step: forall (a:Z (* models the argument to `oa` *)) (pre: T), T (* post state *) * Z (* return value *).


  (**
Then we define the class representation predicate that describes the relationship
between the C memory representation of objects of class `C` with the Gallina
type [T].
This layout is completely implementation dependent.
For examples, see the tests directory.
   *)
  Parameter CR : T -> Rep.

  (** `C` is a concurrent class. Many callers are expected to
      concurrently invoke `oa` on the object.
      Thus, callers would typically not exclusively
      own the object memory while calling update functions. So, [CR]
      cannot be directly used a the class representation predicate because no
      thread will have [this |-> CR l] for any [l] since that would
      give that thread **exclusive** access to the object.

      To share the representation between multiple owners, we use a concurrent
      invariant that will hold the ownership of the object memory by asserting
      [CR l] for **some** [l : T].
      To represent this, we need two ghost locations which we bundle together:
   *)
  Record Cghost : Set :=
    {
      model_loc: gname; (** name of a ghost location to store/track  the model ([l:T]) of the class. *)
      inv_loc: gname; (** name of a ghost location to track the permissions to the named invariant.*)
    }.

  (** Invariants are identified by namespaces. We should pick one based on the
     fully qualified name of the file where we are declaring the invariant *)
  Definition this_name_space : namespaces.namespace :=
    nroot .@ "example".@"lib".@"C".

  (** this asserts that we have the necessary typeclass instances to store values of type [T]
   at ghost locations*)
  Context {frac_ghost: fracG T Sigma}.

  (**
   Next we define two handles on the state of a `C` object, the first [StC_] will
   be the "authoritative" piece that the implementation will hold onto.
   *)
  Definition StC_ (c: Cghost) (t: T) : mpred :=
    fgptsto (model_loc c) (1/2) t.

  (** The second one is the "fragmented" piece (or the "view") that clients will
   use to talk about the state *)
  Definition StC (c: Cghost) (t: T) : mpred :=
    fgptsto (model_loc c) (1/2) t.

   (**
    The definitions of [StC_] and [StC] are such that they are disjoint, but coupled.
    Formally, this means that it is always the case that the implementation's view [StC_]
    is the same as (compatible with) the client's view [StC].
    *)
  Lemma StC_compat : forall g  t t',
      StC_ g t ** StC g t' |--  (StC_ g t ** StC g t') ** [| t = t' |].
  Proof using.
    intros.
    apply fgptsto_ag2.
  Qed.

   (**
    Additionally, if you have both [StC_] and [StC], then you can change both
    values logically atomically.
    *)
   Lemma StC_update : forall g t t',
      StC_ g t ** StC g t |-- (|==> StC_ g t' ** StC g t')%I.
   Proof using.
     unfold StC, StC_. intros.
     use_protect half_half_update; work.
   Qed.

  (** Now we define the actual class representation using a named (concurrent) invariant.
   For this, we use [TInv] which correspond to "destroyable invariants".
   The last argument to [TInv] is the invariant assertion, i.e. the predicate
   that is true throughout the execution of the system.
   In this case, it says that the invariant owns the object memory as specified in [CR]
   and also assert that the object memory corresponds to some [l:T].
   Also, this [l] is stored at the ghost location
   [modelLoc g] and always kept in sync with the object memory. Also, the class
   representation only has half permission to the ghost location [modelLoc g].
   (the other half is given to the client in the constructor).
   The first argument is the name space and the second argument is
   [invLoc g] is the ghost location that tracks the ownership of the invariant.

   The [TInv_own] clause asserts that the [TInv] invariant is still live, i.e.
   it has not been destroyed yet. [TInv_own g q] for any [g] is sufficient to
   guarantee that the invariant [g] is live. When we destroy [g], we give up
   [TInv_own g 1] to get the invariant. *)
  Definition CRInv (g: Cghost) (q:Qp) : Rep :=
    as_Rep (fun this =>
        TInv_own (inv_loc g) q **
        TInv this_name_space
             (inv_loc g)
             (Exists (l:T), this |-> CR l ** StC_ g l)).

  (** additional resources necessary to establish the invariant
   *)
  Parameter FILL_IN : mpred.

  (** the model of the initial object constructed by the constructor *)
  Parameter init_val : T.

  (** the constructor simply establishes the class representation predicate.
   It creates the required ghost locations in the logic. The caller gets two
   resources back:
   1. full ownership of the *concurrent* invariant which can then be split among
      the parties that share the resource.
   2. ownership of [StC] representing his handle on the state.
   *)
  Definition constructorSpec (this : ptr) : WithPrePost Sigma :=
    \pre FILL_IN
    \post Exists (g: Cghost),
       this |-> (CRInv g 1) ** StC g init_val.

  (**
   Note that with this setup, it is easy to share the [CRInv], but we will need
   to use [TInv] to share [StC].
   *)

  (**
   When we write a specification, we express atomicity through a "view shift"
   (or fancy update) which allows us to **atomically** check out a snapshot of
   the model (of type [T]), inspect it, and update it appropriately.

   There are several pieces to the specification
  *)

  (** the resources that the caller must submit while calling `oa` in the state [pre_t] *)
  Parameter oa_call_resources : forall (pre_t :T) (oaarg: Z), mpred.

  (** the resources that are returned from `oa` when the call was made
      in the state [pre_t] *)
  Parameter oa_return_resources : forall (pre_t:T) (oaarg: Z), mpred.

  (** predicates describing non-concurent resources that are accessible throughout
      the function, e.g. the buffer of an output parameter
   *)
  Parameter FILL_IN_pre : mpred.
  Parameter FILL_IN_post : Z -> mpred.

  (**
   The [svs] definition describes the logical (model level) code that runs at
   the commit/linearization point. It has to be able to operate in *any* state
   (note the universal quantifier over [pre_t]) and perform the update from [pre_t]
   to [post_t]. It is important to note that in order to do this, it uses [StC_update]
   which means that the caller *must* have access to [StC] (the client's portion of the model)

   Two things are counter-intuitive about this specification:
   1. [oa_return_resources] is given in the starting-state of the view shift.
      This corresponds to the fact that the implementation, which is "running"
      the view shift is giving up these resources. Because they do not occur in
      the conclusion, the view shift is capable of stashing them in [Q] which it
      will get when the function returns.
   2. [oa_call_resources] is part of the ending state of the view shirt.
      This corresponds to the fact that the client's view shift must be able to
      obtain them and give them up (since they can not be put into [Q] since the
      two are separable: [oa_call_resources post_t a ** Q r])
  *)
  Definition oa_spec (this:ptr) : WithPrePost Sigma :=
    \with (q: Qp) (Q : Z -> mpred) (g: Cghost)
    \arg{a} "a" (Vint a)
    \prepost this |-> (CRInv g q)
    \pre FILL_IN_pre ** (** other resources, e.g. ownership for output buffer, if needed *)
         (Forall (pre_t :T),
            let (post_t, r) := oa_step a pre_t in
            svs (⊤∖  ↑ this_name_space) (⊤∖  ↑ this_name_space)
                (StC_ g pre_t ** oa_return_resources pre_t a)
                (StC_ g post_t ** oa_call_resources pre_t a ** Q r))
    \post{r}[Vint r] Q r ** FILL_IN_post r.

End withSigma.
