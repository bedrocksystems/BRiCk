(**
This tutorial assumes basic understanding of functional programming and logic.
A good way to revise these concepts is to read the first 5 chapters 
(Preface,..., Polymorphism and Higher order functions) of the
#<a href=https://softwarefoundations.cis.upenn.edu/lf-current/deps.html>Software Foundations</a># book

Just like that book, this tutorial is produced from Coq .v files, which can be found in _cpp2v/doc_.
If you want to play with the Coq code in this tutorial, you may want to open the .v source file 
in a Coq editor, instead of opening the html output in a web brower.
In the html, identifiers are hyperlinked to their definition. 
Your Coq editor may also provide a facility to jump to definition (M-. in emacs (company-coq mode))
*)
Require Import bedrock.auto.cpp.specs.

Section with_Σ.
Context {Σ: gFunctors} {σ:genv}.
Import primitives.
Open Scope bi_scope.

Variable x:ptr.
Variable y:ptr.
Variable r:Rep.
Variable q:Qp.

(** * |->
*)

(**
Separation logic assertions are of type [mpred].
The main assertion is of the form:
 *)
Example ex: mpred := x |-> r.

(**
As declared above, [x] is a pointer (memory location)
and [r] is a memory representation. [ex] asserts that x is a valid location and that location contains
the memory representation r.

As an example, [ex2] below asserts that the memory location [x] contains
the long value 2. [ex2] also asserts ownership fraction q
 ownership over the memory location [x].
*)
Example ex2 : mpred := x |-> (longR q 2).

(** the right hand side of [_ |-> _] has type [Rep] which stands for
memory representations. *)
Definition ex3 : Rep :=  longR 1 2.

(**
[q] of type [Qp] is a positive rational number.
In our context, it must be in range (0,1].
[1] implies full ownership, which can be used to update or delete
the memory location. lesser ownership can be used to read the location. *)

Example eFrac1 : Qp := 1.
Example eFrac2 : Qp := 2/4.

Variable z:Z.
(**
There are similar primitives for other primitive types as well: *)
Example e4 : Rep := intR q z. (** similarly, [sintR] and [uingR] *)
Example e6 : Rep := charR q z. (** similarly, [scharR] for signed and [ucharR] for unsigned *)
Example e5 : Rep := shortR q z. (** similarly, [ushortR] and [sshortR] *)
Example e7 : Rep := longR q z. (** similarly, [ulongR] and [slongR] *)
Example e8 : Rep := longlongR q z. (** similarly, [ulonglongR] and [slonglongR] *)
Example e9 : Rep  := int8R q z. (** similarly, [int16], [int32], [uni64]. Prefix 'u' for the unsigned variants *)
Variable b: bool.
Example e11: bool:=true.
Example e10 : Rep := boolR (1/2) b.

(** * Separation
*)
Variable pl: mpred.
Variable pr: mpred.

(** Any two [mpred]s can be combined together using the infix operator [**]
to get an [mpred]:
*)
Example e12: mpred := pl ** pr.
(** [e12] asserts that [pl] and [pr] hold *separately*, meaning that their ownership
of resources is disjoint. For example, the following assertion is invalid because
both the left side and the right side talk about the same (1) ownership of [x].
*)
Example e13 : mpred := x |-> (intR 1 4) ** x |-> (intR 1 4).

(** We can prove that [e13] implies [False] ([_ |-- _] should be read as "entails" ("implies")):*)
Lemma l1: e13 |-- [| False |].
Abort.

(** However, the following is fine: *)
Example e14 : mpred := x |-> intR (1/2) 4 ** x |-> intR (1/2) 4.

(** if [x] and [y] are different locations, the following is also fine *)
Example e15 : mpred := x |-> intR 1 4 ** y |-> intR (1/2) 4.

(** This separateness part of the [**] (instead of vanila conjuction) gives the main modularity properties of separation logic.
For example, if a thread [t1] has precondition [P1] and postcondition [Q2],
and a thread [t2] has precondition [P2] and postcondition [Q2],
the thread [t1 || t2] ([t1] and [t2] running in parallel) has precondition
[P1**P2] and postcondition [Q1**Q2].
Also, separation logic has the frame property: if we can prove a precondition [P] and postcondition [Q] for a function [f],
then for any assertion [H] separate from [P] and [Q], the [P**H] and [Q**H]
are also valid pre- and post- conditions respectively.
*)

(** * Structured Reps
*)

(**
In the examples above (e.g. [ex]), in the [x |-> r] notation, the LHS ([x]) must be an *absolute* location,
RHS is a [Rep] and the whole term ([x |-> r]) has type [mpred].
We have also overloaded the same notation to the case where [x] is *relative* location, e.g. an offset
defined by a field or an array index and type (size of elements) of array.
*)

Variable struct_field struct_field2 : field.

Example structRep1 : Rep := struct_field |-> r.

(**
Note that in In this case, the whole term [structRep] has type [Rep] (memory representation) instead of [mpred]. Such [Rep]s typically describe the memory representation of an *absolute* location holding structured data, e.g. structs, arrays, classes:

  note that a [Rep] is like "Even", it isn't meaningful to say "Even is true",
  it is only meaningful to say "Even n" is true. Similarly, it isn't meaningful
  to say that a [Rep] holds, until you say what location it holds on.
 *)


Variable this:ptr.

Example e17 : mpred := this |-> structRep1.

(** we can also unfold [structRep1] above and write *)

Example e18 : mpred := this |-> (struct_field |-> r).

(**
Because the notation [_ |-> _] is declared right associative, we can drop the parens: *)

Example e19 : mpred := this |-> struct_field |-> r.

(**
Note that the [**] notation is overloaded to work on [Rep]s as well as [mpred]s;
however, the meaning is intuitively the same. That is, the following [Rep]
states that the relative locations are disjoint (i.e. for any *single* absolute
location [l], [l ., struct_field |-> r ** l ., struct_field2 |-> r]).
*)

Example e20 : Rep := struct_field |-> r ** struct_field2 |-> r.



(** * Magic Wand *)

(**
The following assertion asserts that
you have the resources
of [pr] "minus" the resources in [pl].
*)

Example wand1 : mpred := pl -* pr.

(**
The main reasoning rule for this construct is the following, which says that once you separately get the missing piece, you get the whole thing back.:
*)

Lemma wandElim: pl ** (pl -* pr) |-- pr.
Proof using. work. Qed.


(**  * Pure Assertions
*)

(**
Some assertions are pure in the sense that they
are not asserting anything about the current state
of memory or devices. Examples:
*)

Example pure1 : Prop := 1=1.

(** the following is a false assertion, but a valid assertion nevertheless *)
Example pure2 : Prop := 1=2.

(** In Coq, pure assertions have type [Prop]. However, in function specs, pre and post conditions have type [mpred]. To convert an [Prop] to an [mpred], we put them inside [| _ |] *)

Definition pureMpred : mpred := [| 1=1 |].
(*
ptrR

as_rep

Exists

Forall

Best practices:
think about finiteness of words
pattern match on return value

borrow_from
*)
End with_Σ.
