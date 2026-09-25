import OmegaBound.ADVXXZGeneralGlobalExactPCompBound

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The literal exact-grid replacement of the paper's split distributions. -/
noncomputable def globalExactGridBeta27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (W : Side) (r : Fin 6) (u : Shape w) : SplitDist w :=
  let k := ((n : ℚ) * g.joint.prob (r, u)).floor.toNat
  if hk : 0 < k then
    { num := xi.count W r u
      den := k
      den_pos := hk
      sum_num := xi.total W r u }
  else
    g.beta W r u

/-- The paper global datum with only beta replaced by the exact integer histograms. -/
noncomputable def globalExactGridData27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) : GlobalData w :=
  { g.toPaper with beta := globalExactGridBeta27 g xi }

/-- `gridRate` is the weighted paper regional minimum for the literal exact-grid datum. -/
theorem gridRate_eq_globalExactGridData27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) :
    gridRate g n xi = Real.log 2 * ∑ r, g.A.probR r *
      globalRegionRate (globalExactGridData27 g xi) r := by
  rfl

/-- A positive exact cell has precisely its normalized integer histogram as probability law. -/
theorem globalExactGridBeta_probR27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (W : Side) (r : Fin 6) (u : Shape w)
    (sigma : Chunk w)
    (hk : 0 < ((n : ℚ) * g.joint.prob (r, u)).floor.toNat) :
    (globalExactGridBeta27 g xi W r u).probR sigma =
      (xi.count W r u sigma : ℝ) /
        (((n : ℚ) * g.joint.prob (r, u)).floor.toNat : ℝ) := by
  unfold globalExactGridBeta27
  rw [dif_pos hk]
  rfl

private theorem globalCoordFin_val27 {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem globalGridGradeSum27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (S : Side) (u : Shape w)
    (c : Fin (2 * w + 1)) :
    ∑ sigma ∈ Finset.univ.filter
        (fun sigma : Chunk w => Parent25.grade sigma = c), xi.count S r u sigma =
      if Parent25.coordFin S u = c then
        ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
  classical
  by_cases huc : Parent25.coordFin S u = c
  · rw [if_pos huc, ← xi.total S r u]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro sigma _ hnot
    apply xi.graded S r u sigma
    intro hgrade
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Fin.ext
    exact hgrade.trans (globalCoordFin_val27 S u).symm |>.trans
      (congrArg Fin.val huc)
  · rw [if_neg huc]
    apply Finset.sum_eq_zero
    intro sigma hsigma
    apply xi.graded S r u sigma
    intro hgrade
    apply huc
    apply Fin.ext
    exact (globalCoordFin_val27 S u).trans hgrade.symm |>.trans
      (congrArg Fin.val (Finset.mem_filter.mp hsigma).2)

private theorem globalProjectedLawCount27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) (c : Fin (2 * w + 1)) :
    projectedCount Parent25.grade beta.val c =
      ∑ u : Shape w,
        if Parent25.coordFin (GlobalBridge25.side g r which) u = c then
          ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
  classical
  have hbeta : ∀ sigma, beta.val sigma =
      ∑ u : Shape w, xi.count (GlobalBridge25.side g r which) r u sigma :=
    (Finset.mem_filter.mp beta.property).2
  unfold projectedCount
  simp_rw [hbeta]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact globalGridGradeSum27 g xi r (GlobalBridge25.side g r which) u c

/-- The finite P exponent is exactly the entropy difference of the physical aggregate
    histogram and its role-side grade projection. -/
theorem globalPExponent_exactGrid27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    GlobalBridge25.pExponent g n xi r which beta =
      let N := (globalPopulation g n xi r).n
      (N : ℝ) *
        (entropyNats (fun sigma : Chunk w =>
          ((∑ u : Shape w,
            xi.count (GlobalBridge25.side g r which) r u sigma : ℕ) : ℝ) / N) -
        entropyNats (fun c : Fin (2 * w + 1) =>
          ((∑ u : Shape w,
            if Parent25.coordFin (GlobalBridge25.side g r which) u = c then
              ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 : ℕ) : ℝ) / N)) := by
  dsimp only [GlobalBridge25.pExponent]
  congr 2
  · apply congrArg entropyNats
    funext sigma
    rw [(Finset.mem_filter.mp beta.property).2 sigma]
    rfl
  · apply congrArg entropyNats
    funext c
    rw [globalProjectedLawCount27 g xi r which beta c]

end
end OmegaBound.ADVXXZGeneral
end
