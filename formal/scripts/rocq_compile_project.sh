#!/usr/bin/env sh
set -eu

project="${1:-_CoqProject}"
rocq="${ROCQ:-rocq}"
coq_flags="${COQ_FLAGS:-}"

while IFS= read -r file; do
  case "$file" in
     ""|\#*|-*) continue ;;
   esac
   echo "ROCQ c $file"
   # COQ_FLAGS intentionally splits into Rocq CLI arguments.
   "$rocq" c -q $coq_flags -o "${file%.v}.vo" "$file"
   if [ ! -f "${file%.v}.vo" ]; then
     echo "missing Rocq artifact: ${file%.v}.vo" >&2
     exit 1
   fi
done < "$project"
