#!/bin/bash
#
# Copyright (C) BedRock Systems Inc. 2022
# All rights reserved.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#
# Some of the following code is derived from code original to the
# Iris project. That original code is
#
#	Copyright RefinedC developers and contributors
#
# and used according to the following license.
#
#	SPDX-License-Identifier: BSD-3-Clause
#
# Original RefinedC License:
# https://gitlab.mpi-sws.org/iris/refinedc/-/blob/9a34f05075fd946f83ddd1ab6d93b205c820c2c1/LICENSE

set -e

# Wrapper for coqc that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling coqc.
# we need to use opam exec -- coqc to get the coqc installed by opam, not this script

if [ -z "${TIMECMD}" ]; then
  opam exec -- coqc -color on "$@"
else
  opam exec -- ${TIMECMD} coqc -color on "$@"
fi
