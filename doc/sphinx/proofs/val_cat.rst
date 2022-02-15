`val_cat` - Stress Testing Calling Conventions
======================================================================

This test stress tests |project|'s calling convention ensuring that we properly handle pass-by-value, pass-by-references, and pass-by-rvalue-reference.
We also use it as small performance test for out automation.

- `specification <./../_static/proof_examples/val_cat_cpp_spec.v.html>`__

.. literalinclude:: ../_static/proof_examples/val_cat.cpp
   :language: cpp
