cat > dune <<EOF
(coq.theory
 (name test)
 (theories Lens Lens.Elpi elpi elpi_elpi elpi.apps.derive stdpp Ltac2))
EOF

cat > dune-project <<EOF
(lang dune 3.8)
(using coq 0.8)
EOF

export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export DUNE_CACHE=disabled
