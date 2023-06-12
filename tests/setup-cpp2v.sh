export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"

check_cpp2v() {
  input="$1"
  base="${input%.*}"

  echo "cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++17"
  cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++17

  echo "coqc -w -notation-overridden ${base}_cpp_names.v"
  coqc -w -notation-overridden "${base}_cpp_names.v"

  echo "coqc -w -notation-overridden ${base}_cpp.v"
  coqc -w -notation-overridden "${base}_cpp.v"
}
