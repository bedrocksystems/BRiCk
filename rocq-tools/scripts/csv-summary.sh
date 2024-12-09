#!/bin/bash

# Copyright (C) 2023-2024 BlueRock Security Inc.
#
# This library is free software; you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation; version 2.1.
#
# This library is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
# for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with this library; if not, write to the Free Software Foundation,
# Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

echo "File,instructions,time (μs),Major heap words,Minor heap words"

csv_line(){
  INPUT="$1"
  LINE="$(cat "$INPUT")"
  FILE="${INPUT%.glob.perf.csvline}.v"
  echo "$FILE,$LINE"
}
export -f csv_line

find -type f -name '*.glob.perf.csvline' \
  | xargs -I {} bash -c 'csv_line "$@"' _ {} \
  | sed 's/^\.\/\(.*\)/\1/g' \
  | sed 's/^_build\/default\/\(.*\)/\1/g' \
  | sort
