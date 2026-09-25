# Details

Supplementary material for `README.md`: the frozen statements and their hashes, the native roots by
stratum, the paper-to-module table, the certificate's scale, the measured build, how the tree was
generated, and the module map.

## Frozen statements

The two theorem statements were frozen before they were proved. Each is a `def S_… : Prop` in its
own file under `PLATFORM/Statements/`. The statement SHA-256 is the hash of the file's text after
its header comment; `PLATFORM/README.md` explains the header and how to recompute the hash.

| id | frozen statement | file | file SHA-256 | statement SHA-256 |
|---|---|---|---|---|
| T8.1 | `S_T8_1` | `PLATFORM/Statements/T8.1.lean` | `3cb1823233095001…` | `9f5ec0e45a9b074b…` |
| T8_F.1 | `OmegaBound.ADVXXZGeneral.S_T8_F_1` | `PLATFORM/Statements/T8_F.1.lean` | `7209a3d1fc0a0592…` | `326ade3088dcc81f…` |

`release/CheckAxioms.lean` checks `example : S_T8_1 := OmegaBound.omegaMM_lt_2371339` and the
matching `S_T8_F_1` example. They elaborate only if the theorems have exactly these types. The other
15 statement files under `PLATFORM/Statements/` are imported by modules of the tree.

## Native roots

`#print axioms` gives exactly `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
Lean.trustCompiler}` for both theorems and for the two declarations they wrap
(`OmegaBound.ADVXXZFinal.omegaMM_lt_target114`, `OmegaBound.ADVXXZGeneral.omegaMM_lt_target_allFields`).
`release/native-manifest.json` lists the `native_decide` roots: 191 in the constant closure
of the theorems, and 13 entries in kept modules outside that closure, which do
not bear on the theorems.

| stratum (closure roots) | count |
|---|---:|
| compact row-bridge checks `rowsCompact<C>_check` | 96 |
| Round-82 C5 kernels (`c5ShardK*`) and child kernels | 27 |
| Round-61 count cohorts | 24 |
| T7 enriched split and special inventory | 20 |
| T6 split target (node rows, word equivalences, fine index) | 9 |
| T1 bijections and incidence laws | 6 |
| G1 mirror, support and row shapes | 3 |
| other inventory checks (T2, T6 denominators/selection/inventory, T9R16) | 6 |

The compiled code these terms reach calls 62 constants that have `@[extern]` or
`@[implemented_by]`. All of them come from Lean core (`Init`); none comes from Mathlib or from this
repository. They are GMP-backed `Nat`/`Int` arithmetic and comparisons, `Array`/`ByteArray`/`String`
primitives, `List.attachWith`, `Nat.repr` and the `Lean.Name` constructors. The full list, with the
per-root table, is in `release/native-manifest.md`; `release/reproduce.sh native` regenerates both
lists from the built environment with `release/NativeAudit.lean` and compares them.

The general theorems of the route print only the three kernel axioms: the constituent and global
stages, the recursion, the certificate bound and its closure. So do the level-2 and global legs of
the released instance. `release/reproduce.sh check general` runs `release/CheckAxioms.lean` and
`release/CheckGeneralAxioms.lean` and diffs their output against the committed `release/*.expected`.

## Paper versions

Line references in the docstrings are to arXiv:2404.16349v2. Version 3 (August 2026) shifts
`numerical.tex` by two lines and adds the bound ω < 2.371177 obtained by a later note of Dupont and
coauthors (arXiv:2608.16884) by applying the paper's analysis to the eighth power of the
Coppersmith–Winograd tensor; the paper's own fourth-power parameters give ω < 2.371339, which is what
this repository formalises.

## Paper mapping

This table follows the module docstring of `OmegaBound/FinalBound.lean`. Docstrings cite the paper's
LaTeX source (arXiv:2404.16349) as `P/<file>.tex:<lines>`, and the hole-repair argument of
Vassilevska Williams, Xu, Xu and Zhou, *New Bounds for Matrix Multiplication: from Alpha to Omega*
(arXiv:2307.07970), as `H/<file>.tex:<lines>`.

| paper | Lean |
|---|---|
| certificate interface: `Certificate`, its admissibility `AdmissibleAt` and numerical fit `CertificateNumericalFitAt` | `ADVXXZGeneralCertInventory`, `ADVXXZGeneralCertCore`, `ADVXXZGeneralCertScaleV22`, `ADVXXZGeneralRatesFitV22` |
| constituent stage (`constituent.tex`:113-171) | `ADVXXZGeneralCExact*`; exits `constituent_positive_exact_regional33`, `constituent_positive_positive_regional33`, `constituent_pooled_positive33` (`ADVXXZGeneralCExact42*`) |
| global stage (`global.tex`:79-125) | `global_exact_uniform` (`ADVXXZGeneralGlobalExactConsumer37`), `global_nearby_uniform` (`ADVXXZGeneralGlobalNear`), `global_positive_integral_for_iterate` (`ADVXXZGeneralIterateStagesGlobal`) |
| recursion and closure (`numerical.tex`:16-22) | `iterate_stages`, `certificate_bound`, `omegaRect_le_of_certificates_tendsto` (`ADVXXZGeneralIterateStagesUnconditional`) |
| released instance (`numerical.tex`:24-40) | admissibility over ℤ (`ADVXXZCert*`), retained rows and the level-2/level-3/global legs (`ADVXXZGeneralRows*`, `ADVXXZGeneralReleasedRetained*`), `released_numerical_fit` (`ADVXXZGeneralCapstone30`) |
| the final bound (`numerical.tex`:57-60) | `ADVXXZGeneralCapstone30`, `FinalBound` |

## The certificate

The released certificate is the authors' `W1.00_2.371339.mat` (SHA-256
`783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3`), from the `data/` directory of
the optimisation and verification code released with the paper (code archive
`code_matrix_mult.zip`, SHA-256 `a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8`).
The certificate data are the authors' work and are included with attribution; this repository's
Apache licence covers the Lean formalisation, not the authors' data.

The released certificate has parameters q = 5, width 4, three levels and κ = 1; its tables have the
common denominator 3·2^85 (`ADVXXZT2.certDen`). The proof instantiates it as the certificate
`releasedOrdinaryCertificatePhysical`, whose scale is `D = ordinaryD ^ 2 = (3·2^85)^2`
(`ADVXXZGeneralReleasedOrdinaryPhysical`); its admissibility is `released_ordinary_physical_admissible`.
The tree also defines `releasedCertificate` with `D = 3·2^85` and proves that it is not admissible
(`releasedCertificate_not_admissible_at`); the proof does not use it.

## Measured build

Measured for this tree: 9,904 Lake jobs, 50 min 30 s wall and 24.78 CPU-hours with 32 workers; largest single process 18.69 GiB, all workers together at most 29.27 GiB; disk 20 GiB (13.1 GiB of build output plus about 6.5 GiB of Lake packages, 5.6 GiB of them Mathlib's build). Source: acceptance build of this export, 2026-09-24, plain Lake (LEAN_NUM_THREADS=32) on a 96-core node, Mathlib oleans prebuilt, /usr/bin/time -v; aggregate memory: sum of the Lean workers' PSS sampled every 5-7 s.

The build prints about 56,611 warnings. They come from Lean's and Mathlib's linters: `<;>` where `;`
would do, `maxHeartbeats` without a comment (including 50 file-wide settings that the linter flags),
long lines, unused or unreachable tactics, unused `simp` arguments. None of them is an error. The
build also prints the output of 535 `#print axioms` commands in
238 modules; they are kept as each module's record of its axioms and change
nothing. The default target `OmegaBound` is the one-line root `OmegaBound.lean`, which imports
exactly `OmegaBound.FinalBound`, so `lake build` builds the same cone plus that line.

## How the tree was generated

This tree is generated, not hand-assembled. A generator keeps the theorem's import cone of a larger
development tree, prunes declarations that the cone does not use, applies a reviewed list of
docstring corrections, and removes what the pruning leaves without effect. Its inputs are pinned by
SHA-256. Four emitters in `release/emitters/` then replaced generated shards by compact modules;
each has a `--check` mode that re-emits and compares byte for byte (`release/emitters/README.md`
gives the commands and says which inputs are not shipped). `release/MANIFEST.sha256` lists every
file of the tree; check it with `sha256sum -c release/MANIFEST.sha256`. The Lean build needs none of
these tools.

## Module map

2,003 modules under `OmegaBound/`, plus 17 statement files under
`PLATFORM/Statements/` and the root `OmegaBound.lean`. Modules are grouped by name prefix; the first
matching row wins.

| stratum | prefix | modules | of which import-only |
|---|---|---:|---:|
| constituent stage | `ADVXXZGeneralCExact` | 60 | 0 |
| global stage | `ADVXXZGeneralGlobal` | 43 | 0 |
| recursion and closure | `ADVXXZGeneralIterateStages` | 10 | 0 |
| released instance: level-3 row leg | `ADVXXZGeneralRows` | 162 | 0 |
| released instance: level-2 and global legs | `ADVXXZGeneralReleasedRetained` | 224 | 0 |
| general layer: certificate interface, stages, capstone | `ADVXXZGeneral` | 229 | 0 |
| emitted compact modules (row cohorts, Round-61 cohorts) | `ReleaseCompact` | 122 | 0 |
| released certificate tables and admissibility | `ADVXXZCert` | 150 | 0 |
| retained rows | `ADVXXZRetained` | 445 | 174 |
| released tables | `ADVXXZReleased` | 160 | 0 |
| instance inventories (T1-T9 rounds) | `ADVXXZT` | 212 | 99 |
| combinatorial core and other ADVXXZ modules | `ADVXXZ` | 143 | 0 |
| `Audit*`-named closure modules | `Audit` | 4 | 0 |
| base definitions (omega, rank, tensors, ...) | `(other)` | 39 | 0 |

An *import-only* module has no declarations, only imports; the generator leaves these as carriers of
the environment their consumers need. Three further modules (`ADVXXZBlockTens`, `ADVXXZGeneralGlobalOrderedDeletions`, `ADVXXZT6Round26CountingSpine`) have no declarations either, only commands such as `set_option`, `open`, `variable` or `namespace`. Not every declaration in the tree is used by
the proof: about 20,000 lie outside the constant closure of the two theorems, most of them (about
18,000) lemmas that the compact row modules re-declare for compatibility. Numbers in module names
(`Round82`, `T6`, `CExact38`, `Amend25`, `V22`, a trailing `30`) are development labels and carry no
meaning here. Some module names describe content these modules no longer have:

- `OmegaBound.ADVXXZT6Round61ReleasedCountProbe`: a closure module whose constants the proof uses.
- `OmegaBound.ADVXXZT6Round64RegionNegatives`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round64SelectedGroupingNegative`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round67CompatibilityAudit`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round67RepairFitAudit`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round69PresentationAudit`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round70TargetNegative`: an import-only module with no declarations of its own.
- `OmegaBound.ADVXXZT6Round71AdmissibleFitAudit`: an import-only module with no declarations of its own.
- `OmegaBound.AuditIrowsFrozen8`: a closure module whose constants the proof uses.
- `OmegaBound.AuditIrowsMatrixX`: a closure module whose constants the proof uses.
- `OmegaBound.AuditIrowsMatrixY`: a closure module whose constants the proof uses.
- `OmegaBound.AuditIrowsMatrixZ`: a closure module whose constants the proof uses.
