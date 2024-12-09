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

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 src_dir dst_dir"
  exit 1
fi

SRC="$PWD/$1"
DST="$PWD/$2"

SUMMARY_CSV="$DST/perf_summary.csv"

cd "$SRC"

handle_glob(){
  GLOB="$1"
  BASE="${GLOB%.glob}"
  # Gather the performance data.
  PERF="$GLOB.perf.json"
  if [[ -f "$PERF" ]]; then
    mkdir -p "$DST/$(dirname $PERF)/"
    mv "$PERF" "$DST/$BASE.json"
    cp "$BASE.v" "$DST/$BASE.v"
    # Also add the csv line to the perf summary.
    CSVLINE="$GLOB.perf.csvline"
    echo "$BASE.v,$(cat $CSVLINE)" >> "$SUMMARY_CSV"
  else
    echo "$BASE.v" >> "$DST/no_data.txt"
  fi
  # Extract the log data if any.
  LOG="$GLOB.log.json"
  if [[ -f "$LOG" ]]; then
    mkdir -p "$DST/$(dirname $LOG)/"
    mv "$LOG" "$DST/$BASE.log.json"
  fi
}
export -f handle_glob
export DST
export SUMMARY_CSV

if [[ -d "$DST" ]]; then
  echo "Directory $DST already exists."
  exit 1
fi

mkdir "$DST"
touch "$SUMMARY_CSV"

find -type f -name '*.glob' \
  | xargs -I {} bash -c 'handle_glob "$@"' _ {}

echo "File,instructions,time (μs),Major heap words,Minor heap words" \
  > "$SUMMARY_CSV.sorted"
sort "$SUMMARY_CSV" >> "$SUMMARY_CSV.sorted"
mv "$SUMMARY_CSV.sorted" "$SUMMARY_CSV"
sed -i 's/^\.\/\(.*\)/\1/g' "$SUMMARY_CSV"

if [[ -f "$DST/no_data.txt" ]]; then
  sed -i 's/^\.\/\(.*\)/\1/g' "$DST/no_data.txt"
fi

find -type f -name '*.v' | sed 's/^\.\/\(.*\)/\1/g' > "$DST/sources.txt"
