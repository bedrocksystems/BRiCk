.. _machine-interop:

#############################################################
Assembly Interoperation
#############################################################

This section describes the mechanisms that |project| uses to connect C++ concepts to the underlying generated machine code.
These connections are generally necessary in low-level code that inter-operates with assembly.
For example, accessing C++ memory from assembly, calling C++ functions from assembly, changing the address space that the C++ program is running in, etc.

While crucial for low-level programs these features are generally not used in high-level programs.
Even for low-level programs, a relatively small amount of the program requires properties at this level.

Compiler Correctness
=====================

|project|'s strategy for connecting C++ programs to machine programs is to connect the weakest pre-condition of C++ functions to a weakest pre-condition for machine code.
The relevant definitions can be found in |link:bedrock.lang.cpp.compile|.

.. literalinclude:: ../../theories/lang/cpp/compile.v
   :start-after: (* BEGIN COMPILE SNIPPET *)
   :end-before: (* END COMPILE SNIPPET *)

This approach effectively casts C++ as a stylized way to write machine code; however, it is more than simply macros.
When C++ code is running, the C++ abstract machines *owns* the underlying memory and can use that ownership to assert invariants over the memory (e.g. that code is not written, :cpp:`const` objects do not change, etc).
This characterization makes it possible (and even natural) to escape the abstract machine in limited circumstances and interact at a lower-level of abstraction.
For example, a viable model of inline assembly is to borrow resources from the abstract machine, run the assembly, and then return the underlying resources back to the abstract machine.

Low-level Object Layout
========================

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

This code communicates with a device via memory-mapped IO by casting a pointer to a `struct` and then uses field accesses to write to memory.
The important point is that the writes on line `(1)` and `(2)`, must go to the address :cpp:`dma_address + 0` resp. :cpp:`dma_address + 8` for correctness.
In particular, there must not be padding at the start of the :cpp:`struct` and between :cpp:`a` and :cpp:`b`.

Low-level Layout in |project|
------------------------------

The virtual address offset of a |link:bedrock.lang.cpp.semantics.ptrs#PTRS.offset| is determined by |link:bedrock.lang.cpp.semantics.ptrs#eval_offset| (discussed more in :ref:`pointers-and-pointer-provenance`).
|project| exposes this information in the logic in the lemma
Because the C++ standard only requires portability of the layout of certain types of aggregates we limit the use of this information in our axioms to POD and standard layout classes (see |link:bedrock.lang.cpp.semantics.ptrs#eval_o_field|\ .

