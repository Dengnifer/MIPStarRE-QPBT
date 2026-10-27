#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"

modules=prove2me/extracted/participating-modules.txt
out_root=prove2me/extracted/sketch
progress=prove2me/records/stage2-progress.log
mkdir -p "$out_root"

total=$(wc -l < "$modules")
index=0
while IFS= read -r module; do
  index=$((index + 1))
  source_file="${module//.//}.lean"
  output="$out_root/${module//.//}.jsonl"
  mkdir -p "$(dirname "$output")"
  if [[ -s "$output" && "$output" -nt "$source_file" && "$output" -nt prove2me/tools/extract_sketch_info.lean ]]; then
    printf '[%d/%d] cached %s\n' "$index" "$total" "$module" | tee -a "$progress"
    continue
  fi
  temporary="$output.tmp.$$"
  printf '[%d/%d] extract %s\n' "$index" "$total" "$module" | tee -a "$progress"
  lake env lean --run prove2me/tools/extract_sketch_info.lean "$source_file" > "$temporary"
  mv "$temporary" "$output"
done < "$modules"

printf 'complete modules=%d\n' "$total" | tee -a "$progress"
