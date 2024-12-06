#!/bin/bash
set -e

# This can be used to get the "SWI-Prolog.h" header file for all SWI-Prolog
# version tags greater than "MIN_VERSION".
#
# For each potentially supported <version> we produce the following files, in
# the directory "/tmp/ocaml-swipl/headers/":
# - "<version>.h" is the header file for version "<version>", with the version
#   identifier redacted so that it can be diffed more easily.
# - "<version>.h.diff", when it exists, gives the diff between the header at
#   the previous available version and "<version>.h". When the files does not
#   exist, the headers are identical. Generated diffs ignore space changes.

MIN_VERSION="9.0.0"
MIN_VMAJ=$(echo "${MIN_VERSION}" | cut -d. -f 1)
MIN_VMIN=$(echo "${MIN_VERSION}" | cut -d. -f 2)
MIN_VPCH=$(echo "${MIN_VERSION}" | cut -d. -f 3)

TMP_DIR="/tmp/ocaml-swipl"

HEADER_DIR="${TMP_DIR}/headers"

GIT_SWIPL="https://github.com/SWI-Prolog/swipl.git"
GIT_SWIPL_DEVEL="https://github.com/SWI-Prolog/swipl-devel.git"

CLONE_SWIPL="${TMP_DIR}/swipl"
CLONE_SWIPL_DEVEL="${TMP_DIR}/swipl_devel"

# Clone the repos if necessary.
if [[ ! -d ${CLONE_SWIPL} ]]; then
  git clone ${GIT_SWIPL} ${CLONE_SWIPL}
fi
if [[ ! -d ${CLONE_SWIPL_DEVEL} ]]; then
  git clone ${GIT_SWIPL_DEVEL} ${CLONE_SWIPL_DEVEL}
fi

# Fetch all the tags.
git -C ${CLONE_SWIPL} fetch --all --tags
git -C ${CLONE_SWIPL_DEVEL} fetch --all --tags

# Test if a version is supported.
function is_supported() {
  local vmaj
  local vmin
  local vpch
  local v=$1
  # Checking major version.
  vmaj=${v%.*.*}
  if [[ $vmaj < $MIN_VMAJ ]]; then
    false
  elif [[ $vmaj > $MIN_VMAJ ]]; then
    true
  else
    # Checking minor version.
    v=${v#*.}
    vmin=${v%.*}
    if [[ $vmin < $MIN_VMIN ]]; then
      false
    elif [[ $vmin > $MIN_VMIN ]]; then
      true
    else
      # Checking patch version.
      v=${v#*.}
      vpch=$v
      if [[ $vpch < $MIN_VPCH ]]; then
        false
      else
        true
      fi
    fi
  fi
}

# Reads lines with tag names, and for all supported versions, extract the
# corresponding header files. The arguments are the originating repo, and the
# directory in which to write the header files.
function extract_headers_if_supported() {
  local repo=$1
  local destdir=$2
  local git_tag
  local version

  while read -r git_tag; do
    # Extracting the version (removing "V" prefix).
    version=$git_tag
    while [[ $version != ${version#"V"} ]]; do
      version=${version#"V"}
    done

    # Extract the header if supported.
    if is_supported $version; then
      local header="$destdir/$version.h"
      echo "$repo#$git_tag:src/SWI-Prolog.h -> $header (PLVERSION redacted)"
      git -C "$repo" show "$git_tag:src/SWI-Prolog.h" > "$header"
      sed -i 's/^\(#define PLVERSION\) [0-9]*$/\1 REDACTED/' "$header"
    fi
  done
}

# Extracting header files for all supported versions.
function extract_supported_headers() {
  local re="V*[0-9]*\.[0-9]*\.[0-9]*"
  git -P -C ${CLONE_SWIPL} tag --list $re | sort -V \
    | extract_headers_if_supported ${CLONE_SWIPL} ${HEADER_DIR}
  git -P -C ${CLONE_SWIPL_DEVEL} tag --list $re | sort -V \
    | extract_headers_if_supported ${CLONE_SWIPL_DEVEL} ${HEADER_DIR}
}

# Reads a sorted list of headers and generates a diff file when they are not
# the same up to space changes.
function generate_diffs() {
  local header
  local previous_header=""
  while read -r header; do
    if [[ ! -z $previous_header ]]; then 
      (git diff --no-index --ignore-space-change \
        "$previous_header" "$header" > "$header.diff" && rm "$header.diff") ||
        echo "$previous_header != $header (see $header.diff)"
    fi
    previous_header=$header
  done
}

rm -rf "$HEADER_DIR" && mkdir -p "$HEADER_DIR"
extract_supported_headers

find "$HEADER_DIR" -type f | sort -V | generate_diffs

echo -e "\n### Successive diffs ###"
find "$HEADER_DIR" -type f -name '*.diff' | sort -V
