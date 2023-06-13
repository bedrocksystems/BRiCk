cat > dune <<EOF
(env
 (_
  (coq
   (flags
    (:standard
     ;see https://gitlab.mpi-sws.org/iris/iris/-/blob/master/_CoqProject
     -w -notation-overridden
     ; Similar to notation warnings.
     -w -custom-entry-overridden
     -w -redundant-canonical-projection
     -w -ambiguous-paths
     ; Turn warning on hints into error:
     -w +deprecated-hint-without-locality
     -w +deprecated-instance-without-locality
     -w +unknown-option
     -w +future-coercion-class-field)))))

(coq.theory
 (name test))
EOF

cat > dune-project <<EOF
(lang dune 3.6)
(using coq 0.6)
EOF

export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export DUNE_CACHE=disabled
