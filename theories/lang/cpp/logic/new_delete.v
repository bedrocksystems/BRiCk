(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * Semantics of [new] and [delete] expressions
 * (expressed in weakest pre-condition style)
 *)
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     destroy initializers
     wp call.

Require Import bedrock.lang.cpp.heap_notations.

Module Type Expr__newdelete.

  #[local] Open Scope free_scope.

  (**
   * Weakest pre-condition for [new] and [delete] expressions
   *
   * NOTE It is important that these rules are sound, but less important that
   * they are complete. When in doubt, we err on the side of caution and under-specify
   * the behavior of various constructs.
   *
   * If you run into code that requires addditional semantic specification, please file
   * an issue.
   *)

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset) (ρ : region).

    #[local] Notation wp_prval := (wp_prval M ρ).
    #[local] Notation wp_init := (wp_init M ρ).
    #[local] Notation wp_args := (wp_args M ρ).
    #[local] Notation fspec := (fspec resolve.(genv_tu).(globals)).

    #[local] Notation size_of := (@size_of resolve) (only parsing).

    Section new.
     (** [new (...) C(...)] <https://eel.is/c++draft/expr.new>
         - invokes a C++ new operator [new_fn], which returns a storage pointer [storage_ptr];
           [new_fn] _might_ allocate memory
           (https://eel.is/c++draft/expr.new#10), or return an argument
           address for some forms of placement new;
         - constructs an object pointer [obj_ptr], which shares the address of [storage_ptr];
         - invokes the constructor C over [obj_ptr].

          Furthermore <https://eel.is/c++draft/expr.new#22>:
          | (22) A new-expression that creates an object of type T initializes that
          |      object as follows:
          | (22.1) If the new-initializer is omitted, the object is default-initialized
          |        ([dcl.init]).
          |        [Note 12: If no initialization is performed, the object has an
          |         indeterminate value. — end note]
          | (22.2) Otherwise, the new-initializer is interpreted according to the
          |        initialization rules of [dcl.init] for direct-initialization.
          We use [default_initialize] for default ininitialization as it is defined in the
          C++ Standard and we use [wp_init] for direct-initialization as defined
          by the C++ Standard.

          ~~~ Implementation Details ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

          - This axiom assumes that [storage_ptr] points to a character array that will
            _provide storage_ for a new _complete object_ [o]
            (http://eel.is/c++draft/intro.object#def:provides_storage).

            In that case, the C++ abstract machine can choose to make [obj_ptr
            <> storage_ptr] (while keeping the same address), so that the old
            pointer [storage_ptr] cannot be used to access the new object.
            Inspired by Cerberus, we model this by _allowing_ [obj_ptr] to have
            a different allocation ID.

          - The created object might be a subobject of an existing object
            (pointed to by some pointer [p])
            (https://eel.is/c++draft/basic.memobj#intro.object-2).
            It is unclear whether that requires [storage_ptr = p] or just
            [provides_storage storage_ptr p].
            In that case, we plan to allow proving that [obj_ptr] = [p ., o]; we
            offer no such support at present; we account for this case by not specifying that
            [ptr_alloc_id obj_ptr <> ptr_alloc_id storage_ptr].
          - Currently, we do not model coalescing of multiple allocations
            (https://eel.is/c++draft/expr.new#14).
       *)
      Axiom wp_prval_new :
        forall (oinit : option Expr)
          new_fn new_args aty ty Q targs sz
          (nfty := normalize_type new_fn.2)
          (_ : arg_types nfty = Some (Tint sz Unsigned :: targs)),
          (** TODO this needs a side-condition requiring that [new] with no
              arguments does not return [nullptr] because the C++ standard
              permits the assumption. *)
          wp_args targs new_args (fun vs free =>
            Exists sz al, [| size_of aty = Some sz |] ** [| align_of aty = Some al |] **
              |> fspec nfty (Vptr $ _global new_fn.1) (Vn sz :: vs) (fun res =>
                    Exists storage_ptr : ptr,
                      [| res = Vptr storage_ptr |] **
                      if bool_decide (storage_ptr = nullptr) then
                        Q res free
                      else
                        (* [blockR sz -|- tblockR aty] *)
                        (storage_ptr |-> (blockR sz 1 ** alignedR al) **
                         (* TODO: ^ This misses an condition that [storage_ptr]
                            is suitably aligned, accounting for
                            __STDCPP_DEFAULT_NEW_ALIGNMENT__ (issue #149) *)
                             (Forall obj_ptr : ptr,
                                (* This also ensures these pointers share their
                                   address (see [provides_storage_same_address]) *)
                                provides_storage storage_ptr obj_ptr aty -*
                                match oinit with
                                | None => (* default_initialize the memory *)
                                  default_initialize aty obj_ptr
                                                     (fun free' =>
                                                        Q (Vptr obj_ptr) (free' >*> free))
                                | Some init => (* Use [init] to initialize the memory *)
                                  wp_init aty obj_ptr init
                                          (fun free' => Q (Vptr obj_ptr) (free' >*> free))
                                end))))
      |-- wp_prval (Enew (Some new_fn) new_args aty None oinit ty) Q.
    End new.

    Section delete.
      (* delete

         https://eel.is/c++draft/expr.delete

         NOTE: https://eel.is/c++draft/expr.delete#7.1 says:
         > The value returned from the allocation call of the new-expression
         > shall be passed as the first argument to the deallocation function.

         Hence, the destructor is passed a pointer to the object, and the
         deallocation function [delete] is passed a pointer to the
         underlying storage.

         On deleting null:
         From the C++ standard (https://en.cppreference.com/w/cpp/language/delete)

         > If expression evaluates to a null pointer value, no destructors are
         > called, and the deallocation function may or may not be called (it's
         > unspecified), but the default deallocation functions are guaranteed
         > to do nothing when passed a null pointer.

         TODO this does not support array delete yet. (FM-1012)
       *)
      Axiom wp_prval_delete : forall delete_fn e ty destroyed_type Q,
          (* call the destructor on the object, and then call delete_fn *)
          wp_prval e (fun v free =>
             Exists obj_ptr, [| v = Vptr obj_ptr |] **
             if bool_decide (obj_ptr = nullptr)
             then
               (* this conjunction justifies the compiler calling the delete function
                  or not calling it. *)
                  (fspec delete_fn.2 (Vptr $ _global delete_fn.1)
                         (v :: nil) (fun _ => Q Vvoid free))
               ∧ Q Vvoid free
             else (type_ptr destroyed_type obj_ptr **
              (* v---- Calling destructor with object pointer *)
              delete_val true destroyed_type obj_ptr
                (fun this' ty =>
                   Exists storage_ptr sz, [| size_of ty = Some sz |] **
                 (* v---- Token for converting obj memory to storage memory *)
                 provides_storage storage_ptr this' ty **
                 (* Transfer memory to underlying storage pointer; unlike in
                    [end_provides_storage], this memory was pre-destructed by
                    [delete_val]. *)
                  (storage_ptr |-> blockR sz 1 -*
                    (* v---- Calling deallocator with storage pointer *)
                    fspec delete_fn.2 (Vptr $ _global delete_fn.1)
                      (Vptr storage_ptr :: nil) (fun v => Q v free)))))
          |-- wp_prval (Edelete false (Some delete_fn) e destroyed_type ty) Q.
    End delete.
  End with_resolve.
End Expr__newdelete.

Declare Module E__newdelete : Expr__newdelete.

Export E__newdelete.
