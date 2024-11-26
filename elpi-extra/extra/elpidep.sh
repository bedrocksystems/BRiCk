#!/bin/sh
# Annotate an Elpi file with hashes of its (manually specified)
# dependencies, outputting the annotated file.

# TODO: We should probably warn on no dependencies (with `-w` for silence).
# As things stand, typos in dune files can go unreported.

usage () {
	echo 2>&1 'usage: elpidep.sh template [dep ...]'
	exit 1
}

case $# in
0)	usage ;;
*)	;;
esac

echo '% DO NOT EDIT: Generated by dune'

cat -- "$1" || exit 1
shift

case $# in
0)	;;
*)
	echo '
/*'
	sha512sum -- "$@" || exit 1
	echo '*/'
	;;
esac

exit 0