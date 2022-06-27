(*
 * Copyright (C) BedRock Systems Inc. 2020-2022
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import stdpp.decidable.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.genv.
Require Import bedrock.lang.cpp.semantics.subtyping.

(** Dispatching to a virtual function contains two pieces:
    1. Finding the correct function to invoke
    2. Fixing up the dispatch object.
    Consider the following example
    ```c++
    struct A { virtual void foo() = 0; };
    struct B : public A { virtual void foo() { } };

    A* a = new B();
    a->foo(); // same as [static_cast<B*>(a)->B::foo()]
    ```
    note that in order to dispatch to the overridden function
    the dispatch also introduces a cast to get a pointer
    of the correct type.
 *)
Record vhandle : Set :=
  { (* the name of the method that implements the function
       [None] means that there is no body.
     *)
    vimpl      : option obj_name
  ; vpath      : list globname
(*   ; voverrider : globname
  ; vfrom      : globname
  ; (* the cast for the [this] parameter *)
    derivation : class_derives σ voverrider vfrom  *) }.

Section dispatch.
  Context (σ : genv).

  Definition list_get {T} (t : obj_name) (l : list (obj_name * T)) : option T :=
    snd <$> List.find (fun '(t',_) => bool_decide (t = t')) l.

  (** [dispatch base path fn = Some (impl_path, impl_fn)]
      dispatches [fn] (the name of a member function on [Tnamed base])
      given the path [path] (which is [mdc..base].
      NOTE: [base] and [path] are the arguments to [identity]
      - [impl_fn] is the name of the function to call
      - [impl_path] is the path from (base..impl].
      Some examples assuming:
      ```c++
      struct A { virtual void f(); };
      struct B : public A { virtual void f(); };
      struct C : public B { };
      ```
      - [dispatch "::A" ["::C","::B","::A"] "A::f()" = Some (["::B"], "B::f()")]
      - [dispatch "::B" ["::C","::A"] "B::f()" = Some ([], "B::f()")]
   *)
  #[local] Fixpoint dispatch (base : globname) (path : list globname) (fn : obj_name)
    : option (list globname * obj_name) :=
    match path with
    | nil => Some (path, fn)
    | next :: rest =>
        dispatch base rest fn ≫= fun '(hndl, override) =>
          match σ.(genv_tu) !! next with
          | Some (Gstruct st) =>
              match list_get override st.(s_overrides) with
              | Some cand' => Some (path, cand')
              | None => Some (hndl, override)
              end
          | _ => None
          end
    end.

End dispatch.
