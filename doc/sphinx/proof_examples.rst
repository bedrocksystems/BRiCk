###############################
Proof Examples
###############################

|project| provides sufficient definitions and reasoning principles for specifying real C++ *programs* and verifying that their implementation satisfies their specification.
However, in practice, automation is necessary to use these rules to verify real programs.

Here we provide several examples of programs that we have used our semantics to verify.
The programs themselves (and their specifications) are generally *not* interesting, but they showcase a very small subset of the features that |project| supports.
The artifacts are rendered using the `Alectryon <https://github.com/cpitclaudel/alectryon>`_ documentation tool.

.. toctree::

   proofs/val_cat
