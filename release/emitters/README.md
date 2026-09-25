# Emitters of the generated compact modules

These are the four emitters that produced the compact modules of this release, copied from
`tools/release/` of the development repository. `emit_compact_rows.py` has since gained the
`--triples` option and commit-id defaults for `--ref`; its output is unchanged. Each `--check` re-emits the modules
in memory and compares them byte for byte with `OmegaBound/`. It exits non-zero on any difference.
Run the commands from the root of this tree.

| emitter | produces | external inputs | check |
|---|---|---|---|
| `emit_c5_reshard.py` | `ADVXXZT6Round82C5KernelK*` (the 21 equal-cost C5 kernels) and `ADVXXZT6Round82C5KernelChecked` | none | `python3 release/emitters/emit_c5_reshard.py . --check` |
| `apply_gate_import.py` | one scheduling import in `ADVXXZGeneralRowsBridgeIncidence30` (no mathematical content) | none | `python3 release/emitters/apply_gate_import.py . --check` |
| `emit_compact_rows.py` | `ReleaseCompactRowsBase`, `ReleaseCompactRows<C>Check` | the retired row-bridge modules `ADVXXZGeneralRowsBridge<C>{Source30,Leaves30,Final30}` of the development tree (not shipped) | see below |
| `emit_round61_cohorts.py` | `ReleaseCompactR61Cohort*` (the Round-61 count cohorts) | the development repository, the authors' upstream data file and a Sage verifier (not shipped) | see below |

**`emit_compact_rows.py`.** Each cohort module was emitted from three row-bridge modules that the
release no longer contains. With those modules available in a directory `DIR`, the check is
`python3 release/emitters/emit_compact_rows.py . --cohort <C> --triples DIR --check`.

**`emit_round61_cohorts.py`.** This emitter recomputes the Round-61 counts from the certificate
itself, so it has more inputs:

- the development repository's `tools/advxxz_cert.py`, `tools/advxxz_retained_cert.py` and
  `tools/advxxz_t6_round60.py`, each pinned by SHA-256 inside the emitter;
- the authors' upstream data file `W1.00_2.371339.mat`, SHA-256
  `783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3`, and a Sage verifier, not
  shipped. The emitter reads both from the directory named by the environment variable
  `MATMUL_UPSTREAM_DIR`: the data file at
  `experiments/more_asymmetry_reference/upstream/data/W1.00_2.371339.mat` and the verifier as the
  Python package `experiments.more_asymmetry_sage_verifier`. It refuses to run if the variable is
  unset, and accepts the data file only by its SHA-256;
- `numpy`, `scipy` and `sympy`.

It is shipped for inspection. Its `--check` runs only from a development-repository checkout, as
`MATMUL_UPSTREAM_DIR=<dir> python3 tools/release/emit_round61_cohorts.py --check`. The Lean build
does not need it: the cohort modules are ordinary Lean source, checked by the build (each with one
`native_decide`).
