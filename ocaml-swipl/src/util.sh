SED=$(if sed --version 2>/dev/null | grep -q GNU; \
      then which sed; \
      else which gsed 2>/dev/null; fi)

if [ -z "$SED" ]; then
  echo "Error: you need to install GNU sed as \"gsed\"."
  exit 1
fi

function sed() {
  $SED "$@"
}
