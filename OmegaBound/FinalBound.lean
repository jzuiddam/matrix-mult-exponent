import OmegaBound.ADVXXZGeneralCapstone30

/-!
# The final bound: `omegaMM ℚ < 2.371339`

**Theorem.** `omegaMM F < 2371339 / 10^6` for every field `F` (`omegaMM_lt_2371339_allFields`, which
is `ADVXXZGeneral.omegaMM_lt_target_allFields`), and in particular over `ℚ` (`omegaMM_lt_2371339`,
which is `ADVXXZFinal.omegaMM_lt_target114`). This is the bound of Alman, Duan, Vassilevska Williams,
Xu, Xu and Zhou, *More Asymmetry Yields Faster Matrix Multiplication* (2024), formalised along the
paper's own route. The general propositions are parametric in an admissible certificate over an
arbitrary field. The released certificate (q = 5, width 4, three levels, κ = 1; tables over ℤ with
common denominator `ADVXXZT2.certDen` = 3·2^85) enters as an instance of them: the certificate
`releasedOrdinaryCertificatePhysical`, whose scale is `D = ordinaryD ^ 2 = (3·2^85)^2`, admissible by
`released_ordinary_physical_admissible`. (The variant `releasedCertificate` with `D = 3·2^85` is not
admissible, `releasedCertificate_not_admissible_at`, and the proof does not use it.) The instance's
finite checks are discharged partly by the kernel (`decide +kernel`, `rfl`, `norm_num`) and partly by
`native_decide`.

**Axioms.** `#print axioms` gives exactly `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
Lean.trustCompiler}` for both theorems of this module. The last two come from `native_decide`: the
proof trusts that compiled code evaluates finitely many closed Boolean terms to `true`.
`release/native-manifest.json` lists them: 191 native roots lie in the constant closure of these
theorems, and the manifest also lists 13 declarations of modules outside that closure (12 native roots
and one dependant of a root). The general theorems named below for the constituent stage, the global
stage and the recursion and closure print exactly `{propext, Classical.choice, Quot.sound}`, as do
`released_level2_retained_leg` and `released_global_retained_leg` (`release/CheckGeneralAxioms.lean`);
`released_level3_retained_leg` and `released_numerical_fit` print the five.

**Proof architecture** (bracketed ids are the frozen statements in `PLATFORM/Statements/`; `P/…tex:lines`
are lines of the LaTeX source of the paper, arXiv:2404.16349):

* Certificate interface: the record `Certificate` (`ADVXXZGeneralCertInventory`), its admissibility
  `AdmissibleAt` (`ADVXXZGeneralCertScaleV22`, over `GlobalAdmissible` of `ADVXXZGeneralCertCore`) and
  its numerical fit `CertificateNumericalFitAt` (`ADVXXZGeneralRatesFitV22`); stage populations and
  rates, tensors, grids, inventories, repair.
* Combinatorial core: hashing, compatibility, counts, entropy, realisation, demand, good families,
  field maps and rank.
* Constituent stage (P/constituent.tex:113-171): partition, embedding, repair, input concentration,
  ordered deletions, the exact and positive regional exits `constituent_positive_exact_regional33`
  [V17_C_Exact.3] and `constituent_positive_positive_regional33` [V17_C_Exact.4], the pooled producer
  `constituent_pooled_positive33` (`ADVXXZGeneralCExact42*`).
* Global stage (P/global.tex:79-125): `global_exact_uniform` [V17_G_Exact.1]
  (`ADVXXZGeneralGlobalExactConsumer37`), `global_nearby_uniform` [V17_G_Near.1]
  (`ADVXXZGeneralGlobalNear`); the positive global stage enters the recursion as
  `global_positive_integral_for_iterate` (`ADVXXZGeneralIterateStagesGlobal`).
* Recursion and closure (P/numerical.tex:16-22): `iterate_stages` [V17_N_Iterate.1], `certificate_bound`
  [V17_N_Closure.1], `omegaRect_le_of_certificates_tendsto` [V17_N_Closure.2]
  (`ADVXXZGeneralIterateStages*`, `ADVXXZGeneralIterateStagesUnconditional`).
* Released instance (P/numerical.tex:24-40): the tables over ℤ (`ADVXXZCert*`), the admissibility
  `released_ordinary_physical_admissible`, the retained rows and the level-2/level-3/global legs
  [V17_I_Rows.8, V17_I_Rows.10] (`ADVXXZGeneralRows*`, `ADVXXZGeneralReleasedRetained*`), the numerical
  fit `released_numerical_fit` [V17_I_Apply.1].
* Capstone: `ADVXXZGeneralCapstone30` → `omegaMM_lt_target_allFields` [T8_F.1], `omegaMM_lt_target114`
  [T8.1], through `omegaMM_le_tauCert_allFields_of` and `omegaMM_lt_target_allFields_of`
  (`ADVXXZGeneralClosureConditional`).

**Build.** Measured build figures (Lake jobs, wall time, CPU time, peak memory) are in `README.md`; a
machine needs at least 24 GiB of memory.
-/

universe u

namespace OmegaBound

/-- `omegaMM F < 2.371339` for every field. -/
theorem omegaMM_lt_2371339_allFields : ∀ (F : Type u) [Field F], omegaMM F < (2371339 : ℝ) / 10 ^ 6 :=
  ADVXXZGeneral.omegaMM_lt_target_allFields.{u}

/-- `omegaMM ℚ < 2.371339`. -/
theorem omegaMM_lt_2371339 : omegaMM ℚ < (2371339 : ℝ) / 10 ^ 6 :=
  ADVXXZFinal.omegaMM_lt_target114

end OmegaBound

#print axioms OmegaBound.omegaMM_lt_2371339
#print axioms OmegaBound.omegaMM_lt_2371339_allFields
