export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export COQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"

COQC_ARGS="-w -notation-overridden -w -notation-incompatible-prefix"

check_cpp2v_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        echo "cpp2v -v -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver}"
        cpp2v -v -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver}

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp_names.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp_names.v"

        echo "coqc ${COQC_ARGS} ${base}_${ver}_cpp.v"
        coqc ${COQC_ARGS} "${base}_${ver}_cpp.v"
    done
}

check_cpp2v() {
    input="$1"
    base="${input%.*}"
    ver="17"

    # Normalize the output since llvm17 and later quote text with line numbers and a pipe symbol.
    echo "cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'"
    cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++${ver} 2>&1 | sed 's/^ *[0-9]* | //'

    echo "coqc ${COQC_ARGS} ${base}_cpp_names.v"
    coqc ${COQC_ARGS} "${base}_cpp_names.v"

    echo "coqc ${COQC_ARGS} ${base}_cpp.v"
    coqc ${COQC_ARGS} "${base}_cpp.v"
}
