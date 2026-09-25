#!/usr/bin/env bash
# Reproduce the build and the trust check of this release tree.
#
#   release/reproduce.sh [STEP ...]      STEP in: toolchain cache build manifest check general
#                                                 emitters native      (default: toolchain cache build
#                                                 manifest check)
#
# LEAN_NUM_THREADS bounds Lake's worker pool (default here: 4). Lake otherwise starts one worker per
# CPU. The largest single Lean process of this build needs about 19 GiB, so the machine needs at
# least 24 GiB whatever the pool size; README.md gives the measured aggregate at 32 workers.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

timed() {
  if [ -x /usr/bin/time ]; then /usr/bin/time -v "$@"; else time "$@"; fi
}

step_toolchain() {
  # 1. The Lean toolchain named in lean-toolchain (installs elan's copy if missing).
  tc="$(cat lean-toolchain)"
  elan toolchain list | grep -qx "$tc" || elan toolchain install "$tc"
}

step_cache() {
  # 2. Mathlib's prebuilt oleans. If this fails with "SSL: unable to get local issuer certificate",
  #    point curl at the system CA bundle, e.g. CURL_CA_BUNDLE=/etc/ssl/certs/ca-bundle.crt (RHEL-like)
  #    or /etc/ssl/certs/ca-certificates.crt (Debian-like). An EMPTY CURL_CA_BUNDLE also fails.
  #    Do not continue to the build step without the cache: it would compile Mathlib from source.
  lake exe cache get
}

step_build() {
  # 3. The theorem module and its import cone (the default target builds the same cone).
  timed lake build OmegaBound.FinalBound
}

step_manifest() {
  # 4a. Every shipped file against release/MANIFEST.sha256.
  sha256sum --quiet -c release/MANIFEST.sha256 && echo "manifest: all files verified"
}

run_check() {  # run_check NAME: elaborate release/NAME.lean, diff against release/NAME.expected
  local out
  out="$(mktemp)"
  lake env lean "release/$1.lean" > "$out" 2>&1 || { cat "$out"; echo "FAIL: $1.lean did not elaborate"; rm -f "$out"; return 1; }
  if diff -u "release/$1.expected" "$out"; then echo "$1: output equals release/$1.expected"; rm -f "$out"
  else echo "FAIL: $1 output differs from release/$1.expected"; rm -f "$out"; return 1; fi
}

step_check() {
  # 4b. The two theorems and their two implementations print exactly the five axioms, and the two
  #     theorems have exactly the frozen statement types S_T8_1 and S_T8_F_1.
  run_check CheckAxioms
}

step_general() {
  # 5a. The general theorems of the route print exactly the three kernel axioms.
  run_check CheckGeneralAxioms
}

step_emitters() {
  # 5b. The generated modules that can be re-emitted from this tree alone, byte for byte.
  python3 release/emitters/emit_c5_reshard.py . --check
  python3 release/emitters/apply_gate_import.py . --check
  echo "emit_compact_rows.py and emit_round61_cohorts.py need inputs that are not shipped; see release/emitters/README.md"
}

step_native() {
  # 5c. Regenerate the list of native roots and the compiled surface from the built environment
  #     and compare them with the shipped ones (about 15 min and 14 GiB).
  local tmp
  tmp="$(mktemp -d)"
  NATIVE_OUT="$tmp" lake env lean release/NativeAudit.lean
  LC_ALL=C sort "$tmp/native-roots.tsv" | diff -u release/native-roots.tsv - \
    && LC_ALL=C sort "$tmp/native-surface.tsv" | diff -u release/native-surface.tsv - \
    && echo "native: roots and compiled surface equal the shipped lists"
  rm -rf "$tmp"
}

steps=("$@")
[ ${#steps[@]} -eq 0 ] && steps=(toolchain cache build manifest check)
for s in "${steps[@]}"; do
  echo "== $s"
  "step_$s"
done
