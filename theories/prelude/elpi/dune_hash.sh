#!/bin/sh

# ../dune uses this script to hash .elpi files into .v files.

echo "Require Import bedrock.prelude.bytestring."
echo "Definition hash : bs :="
sha512sum $1 | awk '{printf "  \"%s\".\n",$1}'
