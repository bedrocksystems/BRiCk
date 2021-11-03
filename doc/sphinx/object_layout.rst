#############################################################
Object representation, layout and padding
#############################################################

.. todo::

   - primR
   - what makes up a struct (struct_def)
     - struct_paddingR
     - identityR
   - what makes up a union (union_def)
     - union_paddingR
   - implicit destruction
   - raw
     - Vraw
     - rawR
     - maybe? blockR and tblockR

This document highlights some tricky aspects around object
representation, layout and padding in C++ and describes how |project| deals with them.

A basic problem when formalizing C(++) is that there are multiple ways to view the same data [#krebbers-thesis-2.5]_:

- In a *high-level* way using arrays, structs and unions.
- In a *low-level* way using unstructured and untyped byte representations.

This especially affects reasoning about the representation of an object in memory, i.e. how it is laid out and how data that is part of the low-level presentation, but not part of the high-level representation is handled (i.e. padding).

.. warning::

  Much of the reasoning described in this section is still experimental and subject to change.
  In practice, most C++ programs do not require this level of reasoning.

Reasoning about the layout of a struct in memory
=================================================

Reasoning about the layout of an object in memory is often required when interacting with drivers.
For example, consider the following code:

.. code-block:: cpp

  void *dma_address = ...;
  struct dma_struct {
    uint64 a;
    uint64 b;
  };

  void do_dma() {
    struct dma_struct *ptr = dma_address;
    // This examples ignores concerns about UB via data-races or the compiler reordering writes or endianness concerns or alignment
    ptr->a = ...; // (1) This write must go to dma_address + 0
    ptr->b = ...; // (2) This write must go to dma_address + 8
  }

This code communicates with a device via DMA by casting a pointer to a `struct` and then uses field accesses to write to memory.
The important point is that the writes on line `(1)` and `(2)`, must go to the address `dma_address + 0` resp. `dma_address + 8` for correctness.
In particular, there must not be padding at the start of the `struct` and between `a` and `b`.

How can this reasoning be justified?
The C++ standard itself only gives light guarantees about `layout of structs <http://eel.is/c++draft/class.mem#26>`_:

.. pull-quote::

   If a standard-layout class object has any non-static data members, its address is the same as the address of its first non-static data member if that member is not a bit-field.
   Its address is also the same as the address of each of its base class subobjects.
   [Note: There might therefore be unnamed padding within a standard-layout struct object inserted by an implementation, but not at its beginning, as necessary to achieve appropriate alignment.
   — end note]

Thus, the C++ standard guarantees that the write on line `(1)` goes to  `dma_address + 0`, but on its own it does not guarantee that there won't be padding between `a` and `b`.
More concrete guarantees are given by the platform ABI. For example, the ARM ABI [#abi-arm]_ guarantees that

.. pull-quote::

   - The alignment of an aggregate shall be the alignment of its most-aligned component.

   - The size of an aggregate shall be the smallest multiple of its alignment that is sufficient to hold all of its members when they are laid out according to these rules.

.. note::

   Additional assumption: For standard-layout class objects, compilers only insert padding between fields if it is necessary to achieve alignment.

How is this reflected in |project|?
------------------------------------

The virtual address offset of a |link:bedrock.lang.cpp.semantics.ptrs#offset| is determined by |link:bedrock.lang.cpp.semantics.ptrs#eval_offset|.
|project| currently supports reasoning about the layout of (a limited number of) aggregates by embedding the layout information from the Clang front-end into the |project| abstract syntax tree (see |link:bedrock.lang.cpp.syntax.translation_unit#Struct| and |link:bedrock.lang.cpp.syntax.translation_unit#Union|\ ).
Because the C++ standard only requires portability of the layout of certain types of aggregates we limit the use of this information in our axioms to POD and standard layout classes (see |link:bedrock.lang.cpp.semantics.ptrs#eval_o_field|\ .

.. The `Definition struct_def <_static/coqdoc/bedrock.lang.cpp.logic.layout.html>`_ characterizes how a `struct` can be viewed as its constituent pieces and padding.
.. which shows how the `anyR` of a `struct` can be broken down into its constituent fields and padding but there are no axioms , but it only applies to `anyR (Tnamed cls)` and it represents padding as a magic wand. No axiom gives information about field offsets of a struct.

We believe that a good, platform independent way to reason about layout information is to use a combination of :cpp:`static_assert` and :cpp:`offsetof`.
|project| does not currently support this level of reasoning about :cpp:`offsetof`, but it is likely to be added in the future by connecting |link:bedrock.lang.cpp.semantics.ptrs#eval_offset| to the semantics of :cpp:`offsetof`.


Reasoning about the layout of an array in memory
=================================================

The C++ standard defines the `layout of arrays <http://eel.is/c++draft/dcl.array#6>`_ as follows:

.. pull-quote::

  An object of type “array of N U” contains a contiguously allocated non-empty set of N subobjects of type U, known as the elements of the array, and numbered 0 to N-1.

This means that there is no padding between elements of an array.

How is this reflected in |project|?
-------------------------------------

.. The fact that there is no padding in arrays is exploited by `_sub_def <https://gitlab.com/bedrocksystems/cpp2v-core/-/blob/232541a3a7410ac585908a35c50583007c3a391c/theories/lang/cpp/logic/path_pred.v#L306>`_ in combination with `Axiom wp_lval_subscript <https://gitlab.com/bedrocksystems/cpp2v-core/-/blob/232541a3a7410ac585908a35c50583007c3a391c/theories/lang/cpp/logic/expr.v#L141>`_.

.. Additionally `Axiom decompose_array <https://gitlab.com/bedrocksystems/cpp2v-core/-/blob/232541a3a7410ac585908a35c50583007c3a391c/theories/lang/cpp/logic/layout.v#L75>`_ as well as `ArrayR (cpp2v) <https://gitlab.com/bedrocksystems/cpp2v/-/blob/86cde4b410d50adcb05d78de31bdbcf6e04ec109/theories/lib/array.v#L34>`_ do not mention padding for arrays.

Reasoning about the layout of a union in memory
================================================

The C++ standard defines the `layout of unions <http://eel.is/c++draft/class.union#3>`_ as follows:

.. pull-quote::

   The size of a union is sufficient to contain the largest of its
   non-static data members. Each non-static data member is allocated
   as if it were the sole member of a non-union class. [Note: A union
   object and its non-static data members are pointer-interconvertible
   ([basic.compound], [expr.static.cast]). As a consequence, all
   non-static data members of a union object have the same address. —
   end note]

.. note::

   All members sharing the same address does not mean that the same
   pointer is valid to access all of them. In particular, accessing
   the member that is not the active member of a union is UB. This is currently
   the source of a `soundness bug in cpp2v <https://gitlab.com/bedrocksystems/cpp2v-core/-/issues/101>`_.

How is this reflected in cpp2v?
-------------------------------

cpp2v does not reflect that all members of the same union have the same address.
`Axiom decompose_union <https://gitlab.com/bedrocksystems/cpp2v-core/-/blob/232541a3a7410ac585908a35c50583007c3a391c/theories/lang/cpp/logic/layout.v#L61>`_ uses `_field` that in turn uses `offset_of` that uses opaque offset information from the translation unit.

**Potential solution**: Allow the user to assume some facts about the offset information in the translation unit.

Working with the low-level representation of objects
====================================================

Consider the following code that does not exhibit undefined behavior (can be checked using `Cerberus <https://cerberus.cl.cam.ac.uk/cerberus>`_):

.. code-block:: cpp

  #include<stddef.h>

  struct S {
    short a;
    // The compiler must insert padding here to satisfy the alignment requirement of b
    int b;
  };

  void custom_memcpy(void *dest, void *src, size_t n) {
     unsigned char *d = dest, *s = src;
     for(size_t i = 0; i < n; i++) {
       *d = *s;
       d++; s++;
     }
  }

  int main() {
    struct S s1, s2;
    s1.a = 1; s1.b = 2; // Create an object using its high-level representation
    custom_memcpy(&s2, &s1, sizeof(struct S)); // Copy the low-level representation of the object (including padding)
    assert(s2.b == 2); // Access the resulting memory via the high-level representation
  }

This code is interesting because it accesses both the high-level representation and low-level representation of an object.
In particular, there are parts of memory that are not accessible via the high-level representation (the padding of :cpp:`struct S`), but that are accessible via the low-level representation.

How is this reflected in |project|?
------------------------------------

|project| provides access to the low-level view of data via the `Vraw r` value where `r` represents a "raw byte". cpp2v is parametric in this notion of raw byte, but a simple model would instantiate it with `byte | pointer fragment | poison` (i.e. `runtime_val` in `simple_pred`).    `layout.v <https://gitlab.com/bedrocksystems/cpp2v-core/-/blob/master/theories/lang/cpp/logic/layout.v>`_ provides axioms for converting between the high-level representation (e.g. `primR`) and the low-level representation based on `Vraw`.

Thus, the example above can be verified by first converting the struct to raw bytes, copying the raw bytes and then converting the raw bytes back into the struct.


Representing Values
====================

.. The C++ standard `talks explicitly about when materialization occurs <https://eel.is/c++draft/class.temporary#2>`_.

In the |project| separation logic, we choose to immediately materialize all aggregates (i.e. aggregates do not have a Coq-value representation), and address the delayed materialization through the fact that not all pointers (|link:bedrock.lang.cpp.semantics.ptrs#ptr|) are required to be backed by memory.

Pinned Pointers
----------------

In certain instances, especially when communicating pointers with assembly, it is necessary to connect pointers to the virtual addresses.
To do this, |project| exposes a separation logic assertion `pinned_ptr : ptr -> vaddr -> mpred` (|link:bedrock.lang.cpp.logic.pred#pinned_ptr|) that connects the `ptr` to the virtual address that backs it.


Function Call Semantics
------------------------

.. todo::

  determine whether this is going to change before the release.

Following options:

**Pass as everything as values**: (as e.g. in RefinedC)

- Both primitives and aggregates are passed as values to and from functions
- Callee allocates space to put the values
- Con: Needs representation of structures as values (works in C, but more tricky in C++)

**Pass as everything via locations**: (as e.g. in Cerberus)

- Both primitives and aggregates are passed via locations to and from functions
- Caller allocates locations, stores values there and then passes them to the function
- Pro: Aggregates only need to be represented in locations, never as values
- Con: Since primitives are passed via the heap, the specification cannot directly destruct them

**Pass primitives as values and aggregates via locations**: (as currently in cpp2v)

- Primitives are passed as values and aggregates via locations
- Pro: Primitives can be directly destructed in specifications
- Con: Probably break templates because an instantiation with a primitive value would produce quite different code than an instantiatation with an aggregate value


.. rubric:: Footnotes

.. [#krebbers-thesis-2.5]
   Section 2.5 of `Robbert Krebbers - The C standard formalized in Coq <https://robbertkrebbers.nl/research/thesis.pdf>`_

.. [#abi-arm]
  `Procedure Call Standard for the Arm Architecture <https://developer.arm.com/documentation/ihi0042/latest?_ga=2.60211309.1506853196.1533541889-405231439.1528186050>`_
