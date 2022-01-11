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

  (** Dynamic Typing at [delete]-Time

      The C++ Standard ascribes undefined behavior to any [delete]-calls which
      have a Static Type which differs from the Dynamic Type that was associated
      with the pointer when it was initially created via [new]
      <https://eel.is/c++draft/expr.delete#3>:
      | (3) In a single-object delete expression, if the static type of the object to be
      |     deleted is not similar ([conv.qual]) to its dynamic type and the selected
      |     deallocation function (see below) is not a destroying operator delete, the
      |     static type shall be a base class of the dynamic type of the object to be
      |     deleted and the static type shall have a virtual destructor or the behavior is
      |     undefined. In an array delete expression, if the dynamic type of the object to
      |     be deleted is not similar to its static type, the behavior is undefined.
      [new_tokenR allocation_type] tracks this Dynamic Type information.
   *)
  Parameter new_tokenR : forall `{Σ : cpp_logic ti}, type -> Rep.
  Axiom new_tokenR_timeless : forall `{Σ : cpp_logic ti} ty, Timeless (new_tokenR ty).
  #[global] Existing Instances new_tokenR_timeless.

  Section with_cpp_logic.
    Context `{Σ : cpp_logic thread_info}.

    Section with_resolve.
      Context {resolve:genv}.
      Variables (ρ : region).

      #[local] Notation wp_prval := (wp_prval ρ).
      #[local] Notation wp_init := (wp_init ρ).
      #[local] Notation wp_initialize := (wp_initialize ρ).
      #[local] Notation wp_operand := (wp_operand ρ).
      #[local] Notation wp_args := (wp_args ρ).
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
        Axiom wp_operand_new :
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
                                                          (* Track the type we are allocating
                                                             so it can be checked at [delete]
                                                           *)
                                                          obj_ptr |-> new_tokenR aty -*
                                                          Q (Vptr obj_ptr) (free' >*> free))
                                  | Some init => (* Use [init] to initialize the memory *)
                                    wp_initialize aty obj_ptr init
                                            (fun free' =>
                                               (* Track the type we are allocating
                                                  so it can be checked at [delete]
                                                *)
                                               obj_ptr |-> new_tokenR aty -*
                                               Q (Vptr obj_ptr) (free' >*> free))
                                  end))))
        |-- wp_operand (Enew (Some new_fn) new_args aty None oinit ty) Q.

        Axiom wp_operand_array_new :
          forall (array_size : Expr) (oinit : option Expr)
            new_fn new_args aty ty Q targs sz
            (nfty := normalize_type new_fn.2)
            (_ : arg_types nfty = Some (Tint sz Unsigned :: targs)),
            (** TODO this needs a side-condition requiring that [new] with no
                arguments does not return [nullptr] because the C++ standard
                permits the assumption. *)
            (* <https://eel.is/c++draft/expr.new#7>
               | (7) Every constant-expression in a noptr-new-declarator shall be a
               |     converted constant expression ([expr.const]) of type std​::​size_t
               |     and its value shall be greater than zero.
               |     [Example 4: Given the definition int n = 42, new float[n][5] is
               |      well-formed (because n is the expression of a noptr-new-declarator),
               |      but new float[5][n] is ill-formed (because n is not a constant
               |      expression). — end example]
               If we're allocating a new array, we know that the expression must reduce
               to a constant value of type [size_t] /and/ that it must be sequenced
               before we call the [new_fn].
             *)
            wp_operand array_size (fun v free =>
              (* Valid C++ programs require this value to be a [Vint] (see the quote from
                 [expr.new#7] above). *)
              Exists array_sizeN, [| v = Vn array_sizeN |] **
                (* The size must be greater than zero (see the quote from [expr.new#7] above). *)
                [| 0 < array_sizeN |]%N **
                wp_args targs new_args (fun vs free' =>
                  Exists sz al,
                    let array_ty := Tarray aty array_sizeN in
                    [| size_of array_ty = Some sz |] **
                    [| align_of aty = Some al |] **
                    (* NOTE: This is [Forall sz'] because the C++ Abstract Machine can choose
                             however many bytes it wants to use for metadata when handling
                             dynamically allocated arrays.
                     *)
                    Forall sz',
                      |> fspec nfty (Vptr $ _global new_fn.1) (Vn (sz' + sz) :: vs) (fun res =>
                        Exists storage_ptr : ptr,
                          [| res = Vptr storage_ptr |] **
                          if bool_decide (storage_ptr = nullptr) then
                            Q res free
                          else
                            (* [blockR sz -|- tblockR (Tarray aty array_size)] *)
                            (storage_ptr |-> blockR (sz' + sz) 1 **
                             storage_ptr .[Tint W8 Unsigned ! sz'] |-> alignedR al) **
                             (* todo: ^ This misses an condition that [storage_ptr]
                              is suitably aligned, accounting for
                              __STDCPP_DEFAULT_NEW_ALIGNMENT__ (issue #149) *)
                                (Forall obj_ptr : ptr,
                                   (* This also ensures these pointers share their
                                   address (see [provides_storage_same_address]) *)
                                   provides_storage
                                     (storage_ptr .[Tint W8 Unsigned ! sz'])
                                     obj_ptr array_ty -*
                                   match oinit with
                                   | None => (* default_initialize the memory *)
                                     default_initialize array_ty obj_ptr
                                                        (fun free'' =>
                                                           (* Track the type we are allocating
                                                              so it can be checked at [delete]
                                                            *)
                                                           obj_ptr |-> new_tokenR array_ty -*
                                                           Q (Vptr obj_ptr)
                                                             (free'' >*> free' >*> free))
                                   | Some init => (* Use [init] to initialize the memory *)
                                     wp_initialize array_ty obj_ptr init
                                                   (fun free'' =>
                                                      (* Track the type we are allocating
                                                         so it can be checked at [delete]
                                                       *)
                                                      obj_ptr |-> new_tokenR array_ty -*
                                                      Q (Vptr obj_ptr)
                                                        (free'' >*> free' >*> free))
                                   end))))
        |-- wp_operand (Enew (Some new_fn) new_args aty (Some array_size) oinit ty) Q.
      End new.

      Section delete.
        (* delete

           https://eel.is/c++draft/expr.delete

           NOTE: https://eel.is/c++draft/expr.delete#7.1 says:
           > The value returned from the allocation call of the new-expression
           > shall be passed as the first argument to the deallocation function.

           Hence, the destructor is passed a pointer to the object, and the
           deallocation function [delete] is passed a pointer to the
           underlying storage (of type [void *]).

           On deleting null:
           From the C++ standard (https://en.cppreference.com/w/cpp/language/delete)

           > If expression evaluates to a null pointer value, no destructors are
           > called, and the deallocation function may or may not be called (it's
           > unspecified), but the default deallocation functions are guaranteed
           > to do nothing when passed a null pointer.

           NOTE: [Edelete]'s first argument is [true] iff the expression corresponds to
           an array-delete ([delete[]]).
         *)
        Axiom wp_operand_delete :
          forall delete_fn e ty destroyed_type Q
            (dfty := normalize_type delete_fn.2)
            (_ : arg_types dfty = Some [Tptr Tvoid]),
          (* call the destructor on the object, and then call delete_fn *)
          wp_operand e (fun v free =>
             Exists obj_ptr, [| v = Vptr obj_ptr |] **
             if bool_decide (obj_ptr = nullptr)
             then
               (* this conjunction justifies the compiler calling the delete function
                  or not calling it. *)
                 (fspec dfty (Vptr $ _global delete_fn.1)
                        (v :: nil) (fun _ => Q Vvoid free))
               ∧ Q Vvoid free
             else (
               (* /---- Token for distinguishing between array and
                  v     non-array allocations *)
               obj_ptr |-> new_tokenR destroyed_type **
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
                       fspec dfty (Vptr $ _global delete_fn.1)
                             (Vptr storage_ptr :: nil) (fun _ => Q Vvoid free)))))
        |-- wp_operand (Edelete false (Some delete_fn) e destroyed_type ty) Q.

        (* NOTE: [destroyed_type] will refer to the /element/ of the array *)
        Axiom wp_operand_array_delete :
          forall delete_fn e ty destroyed_type array_size Q
            (dfty := normalize_type delete_fn.2)
            (_ : arg_types dfty = Some [Tptr Tvoid]),
          (* call the destructor on the object, and then call delete_fn *)
          wp_operand e (fun v free =>
             Exists obj_ptr, [| v = Vptr obj_ptr |] **
             if bool_decide (obj_ptr = nullptr)
             then
               (* this conjunction justifies the compiler calling the delete function
                  or not calling it. *)
                 (fspec dfty (Vptr $ _global delete_fn.1)
                        (v :: nil) (fun _ => Q Vvoid free))
               ∧ Q Vvoid free
             else (
               let array_ty := Tarray destroyed_type array_size in
               (* /---- Token for distinguishing between array and
                  v     non-array allocations *)
               obj_ptr |-> new_tokenR array_ty **
               (* /---- Calling destructor with object pointer
                  v     Note: virtual dispatch is not allowed for [delete[]] *)
               delete_val false array_ty obj_ptr
                 (fun this' _ (* [= array_ty], thanks to [delete_val] because arrays do not support virtual destruction. *) =>
                    Exists storage_ptr (sz sz' : N),
                      [| size_of array_ty = Some sz |] **
                      (* v---- Token for converting obj memory to storage memory *)
                      provides_storage
                        (storage_ptr .[Tint W8 Unsigned ! sz'])
                        this' array_ty **
                      (* Transfer memory to underlying storage pointer; unlike in
                         [end_provides_storage], this memory was pre-destructed by
                         [delete_val]. *)
                      (storage_ptr |-> blockR (sz' + sz) 1 -*
                       (* v---- Calling deallocator with storage pointer *)
                       fspec dfty (Vptr $ _global delete_fn.1)
                             (Vptr storage_ptr :: nil) (fun v => Q Vvoid free)))))
        (* TODO: drop [ty] from the AST, it's always void. *)
        |-- wp_operand (Edelete true (Some delete_fn) e destroyed_type ty) Q.

        Section NOTE_potentially_relaxing_array_delete.
          (* While (we currently think) it is UB to delete [auto p = new int[5][6]]
             using [delete[] &(p[0][0])], it seems like clang still does something
             sensible for this. If we want to relax our axioms in the future to
             allow for this sort of behavior, we could relate the "carrier type"
             and the "dynamic type" of the array which was allocated (which is stored
             in the [new_token]).

             In particular, so long as the [obj_ptr] [p'] we delete is syntactically
             identical to the [obj_ptr] [p] returned by our array-new call /and/
             the "carrier type" of the delete is _similar_
             <https://eel.is/c++draft/conv.qual> to the "carrier type" of
             the array, we can use [p'] to delete the object rooted at [p].

             NOTE: we might need to insert [erase_qualifiers]/[normalize_type] calls to
             reflect that the standard only calls for "similarity"
             (which has a more nuanced consideration of cv-qualifiers).
           *)

          (* If we have [Tarray ty sz], [array_carrier_type ty] strips all of the outermost
             [Tarray]s off and returns the "carrier type" of the array.
           *)
          Fixpoint array_carrier_type (ty : type) : type :=
            match ty with
            | Tarray ty' _ => array_carrier_type ty'
            | _ => ty
            end.
        End NOTE_potentially_relaxing_array_delete.
      End delete.
    End with_resolve.
  End with_cpp_logic.
End Expr__newdelete.

Declare Module E__newdelete : Expr__newdelete.

Export E__newdelete.
