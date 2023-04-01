#!/bin/bash
#
# Copyright (C) BedRock Systems Inc. 2020-2023
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

usage() {
	cat >&2 <<-EOF
		usage: $(basename "$0") [ -t ] <filename>.<ext> <cpp2v-options> -- [ <clang-options> ]

		This will output (to stdout) dune rules for building <filename>.<ext>,
		passing <options> to cpp2v. Redirect output to dune.inc and
		load via dune's include.

		The output is filesystem-independent and <filename>.<ext> need not exist.
		Placing the output in <base>/dune.inc will transform
		<base>/<filename>.<ext> into <base>/<filename>_<ext>.v and
		<base>/<filename>_<ext>_names.v and (with \`-t\`)
		<base>/<filename>_<ext>_templates.v.
	EOF
        exit 1
}

outRule() {
	local indent fullName name ext targ cmd
	indent="$1"
	fullName="$2"
	shift 2

	# The extension starts at the last dot:
	name="${fullName%.*}"
	if [ "$name" = "$fullName" ]; then
		echo -e "Error: filename '$fullName' has no extension\n" >&2
		usage
	fi
	ext="${fullName##*.}"
	cmd="cpp2v -v %{input} -o ${name}_${ext}.v -names ${name}_${ext}_names.v"
	targ="${name}_${ext}.v ${name}_${ext}_names.v"
	if [ "$templates" = 1 ]; then
		cmd="$cmd --templates=${name}_${ext}_templates.v"
		targ="$targ ${name}_${ext}_templates.v"
	fi
	cmd="$cmd${1+ $@}"
	sed "s/^/${indent}/" <<-EOF
		(rule
		 (targets ${targ})
		 (deps (:input ${name}.${ext}))
		 (action
		  (run ${cmd})))
	EOF
}

traverse() {
	local indent path firstDir rest
	indent="$1"
	path="$2"
	shift 2
	firstDir="${path%%/*}"
	rest="${path#*/}"
	if [ "$firstDir" = "$path" ]; then
		outRule "$indent" "$path" "$@"
	elif [ "$firstDir" = "." ]; then
		traverse "$indent" "$rest" "$@"
	else
		#echo DIR $firstDir
		#echo REST $rest
		echo "${indent}(subdir ${firstDir}"
		traverse " $indent" "$rest" "$@"
		echo "${indent})"
	fi
}

templates=0
while :
do
	case "$1" in
	-t)
		templates=1
		shift
		;;
	--)
		shift
		break
		;;
	-*)
		usage
		;;
	*)
		break
		;;
	esac
done
[ $# -ge 1 ] || usage

path="$1"
shift

traverse "" "$path" "$@"

# vim:set noet sw=8:
