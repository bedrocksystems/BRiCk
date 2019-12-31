(* This file contains intensional functions necessary to
 * describe the semantics of our AST.
 *
 * It would be great if we could eliminate this, but it
 * requires some more thought.
 *
 * Another option would be to completely pre-process the
 * AST and remove these nodes.
 *)
Require Import bedrock.lang.cpp.ast.

(* The AST includes [Ebind_temp] nodes that contain destructor information
 * however, these nodes are embedded in the sub-expression rather than in the
 * creating node.
 *
 * This function extracts the destructor information from [Ebind_temp] and
 * returns it along with the child node if it exists.
 *)
Fixpoint destructor_for (e : Expr) : Expr * option obj_name :=
  match e with
  | Ebind_temp e dtor _ => (e, Some dtor)
  | Eandclean e _ => destructor_for e
  | _ => (e, None)
  end.

(* if an expression is being constructed into an object not owned by
 * the lexical scope of this object, then we won't be in charge of
 * running the destructor
 *)
Definition not_mine (e : Expr) : Expr :=
  match destructor_for e with
  | (a,_) => a
  end.

(* this function determines whether the type is an aggregate type, i.e.
 * arrays and objects.
 *)
Fixpoint is_aggregate (t : type) : bool :=
  match t with
  | Tref _
  | Tarray _ _ => true
  | Tqualified _ t => is_aggregate t
  | _ => false
  end.

Fixpoint is_void (t : type) : bool :=
  match t with
  | Tqualified _ t => is_void t
  | Tvoid => true
  | _ => false
  end.
