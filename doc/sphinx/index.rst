##############################
The BRiCk C++ Program Logic
##############################

BRiCk is a program logic for low-level, concurrent C++ built on the Iris separation logic.
BRiCk's goal is to develop a clear and compositional semantics of C++ programs, that can be used across many levels of abstraction.
It is not meant to provide usable verification tooling to apply these principles to real C++ programs.

.. topic:: Disclaimer

   This code is experimental and not feature complete. If it breaks, you get to keep both pieces.

The BRiCk release contains two pieces:

* The cpp2v tool transforms C++ programs into a format that is digestible by the Coq proof assistant;
* The BRiCk program logic describes the meaning of C++ constructs in terms of reasoning principles that enable users to modularly derive the meaning of programs from their constituent pieces.

BRiCk focuses on a tailored (but relatively large) portion of modern C++.
Some high-level features (and non-features) include the following:

* BRiCk does not support some C++ features: e.g. member pointers, exceptions, goto, and virtual inheritance.
* BRiCk is currently limited to reasoning about templated code after it has been instantiated.
* Some features have restricted use: e.g. BRiCk's support for switch statements does not support Duff's device.
* BRiCk adopts (limited) extensions to the C++ standard, based on existing research, e.g. for multi-address spaces, assembly interoperability, integer-to-pointer casts, and pointer provenance.

Our full feature set (as well as known issues) can be found on the `features <features>`_ page.

BRiCk is a work in progress. We welcome feedback, collaborations, and contributions.

.. toctree::
   :maxdepth: 2
   :caption: Table of Contents

   features
   undefined_behavior
   pointers
   object_layout
   machine
   documentation
   bibliography
   acknowledgements

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
