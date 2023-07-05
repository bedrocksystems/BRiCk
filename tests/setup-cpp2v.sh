export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"

check_cpp2v_versions() {
    input="$1"
    base="${input%.*}"

    shift
    for ver in "$@"
    do
        echo "cpp2v -v -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver}"
        cpp2v -v -names ${base}_${ver}_cpp_names.v -o ${base}_${ver}_cpp.v ${input} -- -std=c++${ver}

        echo "coqc -w -notation-overridden ${base}_${ver}_cpp_names.v"
        coqc -w -notation-overridden "${base}_${ver}_cpp_names.v"

        echo "coqc -w -notation-overridden ${base}_${ver}_cpp.v"
        coqc -w -notation-overridden "${base}_${ver}_cpp.v"
    done
}

check_cpp2v() {
    input="$1"
    base="${input%.*}"
    ver="17"

    echo "cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++${ver}"
    cpp2v -v -names ${base}_cpp_names.v -o ${base}_cpp.v ${input} -- -std=c++${ver}

    echo "coqc -w -notation-overridden ${base}_cpp_names.v"
    coqc -w -notation-overridden "${base}_cpp_names.v"

    echo "coqc -w -notation-overridden ${base}_cpp.v"
    coqc -w -notation-overridden "${base}_cpp.v"
}
