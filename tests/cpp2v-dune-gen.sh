#!/bin/bash
#
# Copyright (C) BedRock Systems Inc. 2020-2023
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

usage() {
	cat >&2 <<-EOF
		usage: $0 <filename>.<ext> <options>

		This will output (to stdout) dune rules for building <filename>.<ext>,
		passing <options> to cpp2v. Redirect output to dune.inc and
		load via dune's include.

		The output is filesystem-independent and <filename>.<ext> need not exist.
		Placing the output in <base>/dune.inc will transform
		<base>/<filename>.<ext> into <base>/<filename>_<ext>.v and
		<base>/<filename>_<ext>_names.v.
	EOF
        exit 1
}

outRule() {
	fullName="$1"
	shift

	# The extension starts at the last dot:
	name="${fullName%.*}"
	if [ "$name" = "$fullName" ]; then
		echo -e "Error: filename '$fullName' has no extension\n" >&2
		usage
	fi
	ext="${fullName##*.}"

	cat <<-EOF
	(rule
	 (targets ${name}_${ext}.v ${name}_${ext}_names.v)
	 (deps (:input ${name}.${ext}))
	 (action
	EOF
	echo "  (run cpp2v -v %{input} -o ${name}_${ext}.v -names ${name}_${ext}_names.v -- $@)))"
}

traverse() {
	path="$1"
	shift
	firstDir="${path%%/*}"
	rest="${path#*/}"
	if [ "$firstDir" = "$path" ]; then
		outRule "$path" "$@"
	elif [ "$firstDir" = "." ]; then
		traverse "$rest" "$@"
	else
		#echo DIR $firstDir
		#echo REST $rest
		echo "(subdir ${firstDir}"
		traverse "$rest" "$@"
		echo ")"
	fi
}

[ $# -ge 1 ] || usage

echo "; DO NOT EDIT: Auto-generated by \"$0 $@\""
path="$1"
shift

traverse "$path" "$@"

# vim:set noet sw=8:
