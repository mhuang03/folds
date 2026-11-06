#!/bin/bash
# build one Lean module of the repository (used for Folds.Structure2):
#   leanbuild.sh Folds.Structure2
# or check a file with `lake env lean`:  leanbuild.sh --file path/to/File.lean
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/../.."
if [ "$1" = --file ]; then lake env lean "$2"; else lake build "$@"; fi
