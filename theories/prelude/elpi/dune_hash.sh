#!/bin/sh

# ../dune uses this script to hash .elpi files into .v files.

echo "Require Import bedrock.prelude.bytestring."
echo -n "Definition hash : bs := "
sha512sum $1 | awk '{printf "\"%s\"%%bs.\n",$1}'
