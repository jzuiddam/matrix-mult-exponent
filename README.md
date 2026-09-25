# A Lean 4 proof that ω < 2.371339

A Lean 4 formalisation of the bound ω < 2.371339 on the exponent of matrix multiplication, from
Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, *More Asymmetry Yields Faster Matrix
Multiplication* ([arXiv:2404.16349](https://arxiv.org/abs/2404.16349)), using the authors' released certificate. This is the paper's
fourth-power bound, not the eighth-power bound ω < 2.371177 that version 3 of the paper also
reports. Line references in docstrings are to arXiv v2; "ADVXXZ" in module names abbreviates the
six authors.

## The theorems

`OmegaBound/FinalBound.lean`:

```lean
/-- `omegaMM F < 2.371339` for every field. -/
theorem omegaMM_lt_2371339_allFields : ∀ (F : Type u) [Field F], omegaMM F < (2371339 : ℝ) / 10 ^ 6 :=
  ADVXXZGeneral.omegaMM_lt_target_allFields.{u}

/-- `omegaMM ℚ < 2.371339`. -/
theorem omegaMM_lt_2371339 : omegaMM ℚ < (2371339 : ℝ) / 10 ^ 6 :=
  ADVXXZFinal.omegaMM_lt_target114
```

`omegaMM F` (`OmegaBound/Omega.lean`) is the infimum of the exponents τ such that the rank of the
`n × n` matrix-multiplication tensor over `F` is at most `C · n^τ` for some constant `C` and all
`n ≥ 1`.

## Axioms

Both theorems use exactly `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool` and
`Lean.trustCompiler`. The last two come from `native_decide`, used for 191 finite checks
over the certificate's integer tables; the general theorems of the paper's route use only the first
three.

## Building

```
elan toolchain install $(cat lean-toolchain)      # leanprover/lean4:v4.27.0
lake exe cache get                                 # prebuilt Mathlib v4.27.0 (a3a10db0e9d6)
LEAN_NUM_THREADS=4 lake build OmegaBound.FinalBound
```

The build needs about 20 GiB of disk and 24 GiB of memory (the largest single Lean process peaks
at 18.69 GiB); set `LEAN_NUM_THREADS` to fit your memory. Measured for this tree: 9,904 Lake jobs, 50 min 30 s wall and 24.78 CPU-hours with 32 workers.
`release/reproduce.sh` runs the whole sequence, including the axiom checks.

## The certificate

The certificate is the authors' `W1.00_2.371339.mat` from the code archive linked in the paper (OSF
project `mw5ak`). Its coordinates enter this tree as exact integer tables (`OmegaBound/ADVXXZCert*`),
from which the admissibility is proved; `release/DETAILS.md` gives the file hashes.

## Layout

| path | content |
|---|---|
| `OmegaBound/` | the 2,003 Lean modules; the docstring of `FinalBound.lean` maps the paper's sections to modules |
| `PLATFORM/` | the `S_…` statement definitions that some theorems are stated against |
| `release/` | axiom checks, the list of `native_decide` roots, the reproduction script, checksums, and `DETAILS.md` (paper-to-module table, build figures, module map) |
| `LICENSE` | Apache License 2.0 |

## Author

Jeroen Zuiddam (University of Amsterdam).

## Licence

See `LICENSE`.
