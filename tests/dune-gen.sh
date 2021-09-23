#!/bin/sh
#
# Copyright (C) BedRock Systems Inc. 2020-21
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

find . -name '*.[ch]pp' | while read i; do ./cpp2v-dune-gen.sh $i -std=c++17; done > dune.inc
find . -name '*.[ch]' | while read i; do ./cpp2v-dune-gen.sh $i -std=c99; done >> dune.inc
