Require Import elpi.elpi.

Elpi Command program.
Elpi Accumulate lp:{{ main _ :- coq.say "program". }}.
Elpi Typecheck program.
Elpi Export program.
