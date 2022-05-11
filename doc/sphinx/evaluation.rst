.. _evaluation:

###############################
Evaluation
###############################

The semantics of C++ programs in |project| are written in `weakest (liberal) pre-condition style <https://en.wikipedia.org/wiki/Predicate_transformer_semantics>`_.
The general form of these rules is the following:

.. coq:

   Parameter wp : input_1 -> .. -> input_n -> (output_1 -> ... -> output_n -> PROP) -> PROP

Note that `wp` is a predicate in our separation logic (the fact that it returns a `PROP`).
Informally you can think of it as capturing the pre-condition to the inputs (one of which is normally an expression) that are sufficient such that the code is safe and if the expression terminates, it terminates in a state in which its outputs statisfy the "continuation" (i.e. the final function argument to `wp`).

Due to the structure of C++, |project| contains a separate weakest pre-condition modality for each syntactic category. These are defined in |link:bedrock.lang.cpp.logic.wp|.

Expressions
==============

In |project| we break expression evaluation down into four weakest pre-condition assertions representing the different `value categories <http://eel.is/c++draft/expr.prop#basic.lval-1>`_ of a C++ expression.

Modeling Temporaries
---------------------

In the course of evaluating C++ programs, the language can construct objects that are later destroyed, this occurs for `automatic storage duration <https://eel.is/c++draft/basic.stc.auto#1>`_ variables (i.e. stack allocated variables and temporaries).
C++ semantics guarantees that the lifetime of temporaries is well-bracketed, meaning that objects will be destroyed in the reverse order that they were constructed.
In |project| we capture the stack of objects to be destroyed using the type |link:bedrock.lang.cpp.logic.wp#FreeTemps.t|.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN FreeTemps.t *)
   :end-before: (* END FreeTemps.t *)
   :dedent:

Here |link:bedrock.lang.cpp.logic.wp#FreeTemps.id| represents the identity, characterizing that nothing needs to be destroyed.
`delete ty p` represents that the value at pointer `p` (which should have type `ty`) needs to be destroyed.
Note that to delete the value, the C++ abstract machine runs the destructor and reclaims the underlying memory.
Note that virtual dispatch is *not* used when invoking the destructor.
`seq a b` means that the temporaries in `a` must be destroyed *before* the temporaries in `b`.
`par a b` means that the temporaries in `a` and the temporaries in `b` are destroyed in an interleaved manner [#parallel-destruction]_.

The meaning of these constructs is made precise by interpreting the syntax using |link:bedrock.lang.cpp.logic.destroy#interp|.

.. literalinclude:: ../../theories/lang/cpp/logic/destroy.v
   :start-after: (* BEGIN interp *)
   :end-before: (* END interp *)
   :dedent:

l-values & x-values
----------------------

l-values and x-values follow the same general structure.
Their weakest precondition rules are captured by |link:bedrock.lang.cpp.logic.wp#WPE.wp_lval| and |link:bedrock.lang.cpp.logic.wp#WPE.wp_xval| respectively (we show `wp_lval` as our example).

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_lval *)
   :end-before: (* END wp_lval *)
   :dedent:

pr-values
----------------------

The final value category of C++ (pr-values) is slightly more complex than l-values and x-values.
The `C++ standard <http://eel.is/c++draft/expr.prop#basic.lval-1.2>`_ describes them as follows:

.. quote:

   A prvalue is an expression whose evaluation initializes an object or
   computes the value of an operand of an operator, as specified by the
   context in which it appears, or an expression that has type cv void."

|link:bedrock.lang.cpp.logic.wp#WPE.wp_init| handles the second of these two.
The parameter is the following:

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_init *)
   :end-before: (* END wp_init *)
   :dedent:

This definition has two interesting differences from `wp_lval` and `wp_xval`.
The first is that it takes a |link:bedrock.lang.cpp.semantics.values#PTRS.ptr| that represents the location that the object is being constructed into.
Because of this, the post-condition does not consume a value but instead a `FreeTemp` and a `FreeTemps`.
Both of these are simply `FreeTemps` under the hood but in this context they mean slightly different things.
The first argument is the `FreeTemp` that is used to destroy the object that is initialized by this expression.
The second is used to destroy the temporaries that are created while initializing the object.
For example, suppose you are calling a constructor `C(1+1)`.
In this case, the constructed value (of type `C`) would be destroyed by `FreeTemp`, while the temporary that `1+1` evaluates to would be destroyed by `FreeTemps`.

On top of `wp_init`, we can *define* `wp_prval` by universally quantifying the pointer that is being initialized and passing it to the continuation.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_prval *)
   :end-before: (* END wp_prval *)
   :dedent:

Note that the pointer `p` is completely unconstrained in this definition.
In practice the C++ abstract machine will pick this pointer to be fresh and reserve it before proceeding to initialize it when evaluating `e`.


Operands
~~~~~~~~~~~
|link:bedrock.lang.cpp.logic.wp#WPE.wp_operand| is used to evaluate a operand of a primitive operator.
These operands are *always* primitives, since operators that accept aggregates are desugared to functions or methods.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_operand *)
   :end-before: (* END wp_operand *)
   :dedent:

Unlike `wp_init` and `wp_prval`, operands return |link:bedrock.lang.cpp.semantics.value#val|\ s.
Because the value returned does not have an identity, there is nothing to destroy, so, unlike `wp_prval` and `wp_init`, the continuation takes a single `FreeTemps`, which will destroy the temporaries created when evaluating the operand.

The relationship between |link:wp_operand| and |link:wp_init| can be precisely characterized by the following two axioms.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_init <-> wp_operand *)
   :end-before: (* END wp_init <-> wp_operand *)
   :dedent:

The first of these axioms states that initializing *a primitive* using an expression `e` can be viewed as evaluating `e` using operand semantics and then materializing a value (using |link:bedrock.lang.cpp.logic.heap_pred#primR|) with the value and the type of the expression.
The second of these axioms, which is not technically justified by the standard and is therefore only provided for documentation purposes, states that evaluating an operand can be viewed as initializing a fresh primitive object, reading the value out of it, destroying it, and then returning the result to the continuation `Q`.
The reason that this rule is not technically justified by the standard is because the C++ standard states explicitly that there is no identity associated with this sort of value.
However, since the existence of a pointer does not imply that the object has a location in the |project| model, we can create a fresh `ptr` and then immediately destroy it.


Function Call Semantics
------------------------

The semantics for function calls is concerned with the way that we pass arguments to functions and (potentially) recieve the return value.
We note that it is important to handle the passing of primitives as well as aggregates, both of which are very common in C++.
The semantics for function calls specifies how to pass arguments to functions and (potentially) get back the return value, both for primitives and for aggregates.

|project| follows the C++ standard by `using initialization semantics to pass (and return) data to (and from) functions <https://eel.is/c++draft/expr.call#7>`_.
It is also the style taken by `Cerberus <https://www.cl.cam.ac.uk/~pes20/cerberus/>`_.

.. rubric:: Footnotes
.. [#parallel-destruction] We use `par` to under approximate the destruction order of temporaries when C++ does not guarantee it statically. For example, in the function call `f(a,b,c)`, the expressions `a`, `b`, and `c` can be evaluated in any order and we can approximate the ordering provided by c++ by saying they are destroyed in parallel.
.. [#non-observable-destructors] Part of the justification for this is that the arguments to functions do not have names in the callees stack frame, so the locations of those objects are not accessible to other objects (something that could influence the semantics due to live pointers).
