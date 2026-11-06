# Source this (or set CADICAL / LRAT_TRIM yourself) before running gen.py / mkfile.py.
# Tools used (built from source):
#   CaDiCaL 3.0.1, https://github.com/arminbiere/cadical  commit c60730422e758ef1cebe7aeddf2dda31c996bf04
#   lrat-trim,     https://github.com/arminbiere/lrat-trim commit b30f400f4ee5c32b77ee566a7c006081b521534f
#   (./configure && make in each)
export CADICAL=${CADICAL:-cadical}
export LRAT_TRIM=${LRAT_TRIM:-lrat-trim}
