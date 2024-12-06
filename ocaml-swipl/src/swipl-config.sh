#!/bin/bash

set -Eeuo pipefail

MODNAME="swipl"
MIN_VER="9.0.0"
MAX_VER="9.3.8"

LIB_FILE=$1
VER_FILE=$2

CUR_VER=$(pkg-config --modversion ${MODNAME})

function version_to_int() {
  local vmaj
  local vmin
  local vpch
  local v=$1
  vmaj=${v%.*.*}
  v=${v#*.}
  vmin=${v%.*}
  vpch=${v#*.}
  let "res = ${vmaj} * 10000 + ${vmin} * 100 + ${vpch}"
  echo "${res}"
}

PL_CUR_VER=$(version_to_int ${CUR_VER})
PL_MIN_VER=$(version_to_int ${MIN_VER})
PL_MAX_VER=$(version_to_int ${MAX_VER})

if [[ $PL_CUR_VER -lt $PL_MIN_VER || $PL_CUR_VER -gt $PL_MAX_VER ]]; then
  >&2 echo -e "\033[0;31mError: your SWI-prolog version is not supported."
  >&2 echo -e "You need a version between ${MIN_VER} and ${MAX_VER},"
  >&2 echo -e "but you are currently running version ${CUR_VER}.\033[0m"
  exit 1
fi

pkg-config --libs-only-L swipl \
  | sed -E "s/-L([^ ]*) */\\1/g" \
  | tr -d '\n' > ${LIB_FILE}

echo "let version = \"${CUR_VER}\"" > ${VER_FILE}
