cat > dune <<EOF
(coq.theory
 (name test))
EOF

cat > dune-project <<EOF
(lang dune 3.6)
(using coq 0.6)
EOF

export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export DUNE_CACHE=disabled
