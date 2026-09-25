import OmegaBound.ADVXXZGeneralGlobalExactEntropyMixture

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The entropy obtained by first grouping the exact-grid split laws into the paper's boundary
    singleton and residual cells. -/
noncomputable def globalGroupedEntropy27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) : ℝ :=
  ∑ c : GlobalBridge25.Cell w,
    let mass := ∑ u ∈ Finset.univ.filter
      (fun u => GlobalBridge25.key g r which u = c), (g.alpha r).probR u
    mass * entropy (fun sigma =>
      (∑ u ∈ Finset.univ.filter (fun u => GlobalBridge25.key g r which u = c),
        (g.alpha r).probR u *
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r u).probR sigma) /
        mass)

/-- Grouping cannot increase the conditional split entropy, so the grouped paper quantity is
    bounded by the entropy of the complete exact-grid average law. -/
theorem globalGroupedEntropy_le_average27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    globalGroupedEntropy27 g xi r which ≤
      entropy (globalAverage (globalExactGridData27 g xi) r
        (GlobalBridge25.side g r which)) := by
  have h := entropy_grouped_mixture_le27
    (g.alpha r).probR ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩
    (fun u => (globalExactGridBeta27 g xi
      (GlobalBridge25.side g r which) r u).probR)
    (fun u sigma => (globalExactGridBeta27 g xi
      (GlobalBridge25.side g r which) r u).probR_nonneg sigma)
    (fun u => (globalExactGridBeta27 g xi
      (GlobalBridge25.side g r which) r u).sum_probR)
    (GlobalBridge25.key g r which)
  unfold globalGroupedEntropy27
  simpa only [globalAverage, globalExactGridData27, GlobalSpec.toPaper] using h

private theorem rateYZ_key_eq_inl_iff27 {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (which : Fin 2) (u v : Shape w) :
    GlobalBridge25.key g r which u = Sum.inl v ↔
      GlobalBridge25.boundary g r which u ∧ u = v := by
  classical
  unfold GlobalBridge25.key
  split <;> simp_all

private theorem rateYZ_key_eq_inr_iff27 {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (which : Fin 2) (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r which u = Sum.inr k ↔
      ¬ GlobalBridge25.boundary g r which u ∧
        Parent25.coordFin (GlobalBridge25.side g r which) u = k := by
  classical
  unfold GlobalBridge25.key
  split <;> simp_all

private theorem rateYZ_coordFin_val27 {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem rateYZ_scalar_entropy27 {iota : Type*} [Fintype iota]
    (a : ℝ) (p : iota → ℝ) :
    a * entropy (fun x => a * p x / a) = a * entropy p := by
  by_cases ha : a = 0
  · rw [ha]
    simp
  · have hp : (fun x => a * p x / a) = p := by
      funext x
      field_simp
    rw [hp]

private theorem rateYZ_inl_cell27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) (v : Shape w) :
    let mass := ∑ u ∈ Finset.univ.filter
      (fun u => GlobalBridge25.key g r which u = Sum.inl v), (g.alpha r).probR u
    mass * entropy (fun sigma =>
      (∑ u ∈ Finset.univ.filter
        (fun u => GlobalBridge25.key g r which u = Sum.inl v),
        (g.alpha r).probR u *
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r u).probR sigma) /
        mass) =
      if GlobalBridge25.boundary g r which v then
        (g.alpha r).probR v * splitEntropy
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r v)
      else 0 := by
  classical
  dsimp only
  by_cases hv : GlobalBridge25.boundary g r which v
  · have hfilter : Finset.univ.filter
        (fun u => GlobalBridge25.key g r which u = Sum.inl v) = {v} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [rateYZ_key_eq_inl_iff27]
      constructor
      · exact fun h => h.2
      · intro huv
        subst u
        exact ⟨hv, rfl⟩
    rw [if_pos hv, hfilter]
    simp only [Finset.sum_singleton, splitEntropy]
    exact rateYZ_scalar_entropy27 _ _
  · have hfilter : Finset.univ.filter
        (fun u => GlobalBridge25.key g r which u = Sum.inl v) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [rateYZ_key_eq_inl_iff27]
      constructor
      · intro h
        exact (hv (h.2 ▸ h.1)).elim
      · intro hu
        simpa using hu
    rw [if_neg hv, hfilter]
    simp

private theorem rateYZ_key_y_iff27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r (0 : Fin 2) u = Sum.inr k ↔
      coord (g.perm r .Y) u = k.val ∧ 0 < coord (g.perm r .Z) u := by
  rw [rateYZ_key_eq_inr_iff27]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, if_pos,
    Fin.ext_iff, rateYZ_coordFin_val27]
  omega

private theorem rateYZ_key_z_iff27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r (1 : Fin 2) u = Sum.inr k ↔
      0 < coord (g.perm r .X) u ∧ 0 < coord (g.perm r .Y) u ∧
        coord (g.perm r .Z) u = k.val := by
  have h10 : (1 : Fin 2) ≠ 0 := by omega
  rw [rateYZ_key_eq_inr_iff27]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, h10, if_false,
    Fin.ext_iff, rateYZ_coordFin_val27]
  omega

private theorem rateYZ_inr_cell_congr27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) (k : Fin (2 * w + 1))
    (selected : Shape w → Prop) [DecidablePred selected]
    (hselected : ∀ u, GlobalBridge25.key g r which u = Sum.inr k ↔ selected u) :
    let mass := ∑ u ∈ Finset.univ.filter
      (fun u => GlobalBridge25.key g r which u = Sum.inr k), (g.alpha r).probR u
    mass * entropy (fun sigma =>
      (∑ u ∈ Finset.univ.filter
        (fun u => GlobalBridge25.key g r which u = Sum.inr k),
        (g.alpha r).probR u *
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r u).probR sigma) /
        mass) =
      (∑ u, if selected u then (g.alpha r).probR u else 0) *
        entropy (weightedSplit (g.alpha r).probR
          (fun u => globalExactGridBeta27 g xi
            (GlobalBridge25.side g r which) r u) selected) := by
  classical
  dsimp only
  unfold weightedSplit
  simp_rw [Finset.sum_filter]
  have hmass : (∑ u, if GlobalBridge25.key g r which u = Sum.inr k then
      (g.alpha r).probR u else 0) =
      ∑ u, if selected u then (g.alpha r).probR u else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    exact if_congr (hselected u) rfl rfl
  have hnum : (fun sigma =>
      ∑ u, if GlobalBridge25.key g r which u = Sum.inr k then
        (g.alpha r).probR u *
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r u).probR sigma
        else 0) =
      (fun sigma => ∑ u, if selected u then (g.alpha r).probR u *
        (globalExactGridBeta27 g xi (GlobalBridge25.side g r which) r u).probR sigma
        else 0) := by
    funext sigma
    apply Finset.sum_congr rfl
    intro u _
    exact if_congr (hselected u) rfl rfl
  rw [hmass]
  apply congrArg (fun H : ℝ =>
    (∑ u, if selected u then (g.alpha r).probR u else 0) * H)
  apply congrArg entropy
  funext sigma
  apply congrArg (fun z : ℝ => z /
    ∑ u, if selected u then (g.alpha r).probR u else 0)
  exact congrFun hnum sigma

/-- The first grouped quantity is exactly the paper's `globalEta`. -/
theorem globalGroupedEntropy_eq_eta27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    globalGroupedEntropy27 g xi r 0 =
      globalEta (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  classical
  unfold globalGroupedEntropy27
  rw [Fintype.sum_sum_type]
  unfold globalEta
  dsimp only [globalExactGridData27, GlobalSpec.toPaper]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, if_pos]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro v _
    simpa only [GlobalBridge25.boundary, GlobalBridge25.side, if_pos] using
      rateYZ_inl_cell27 g xi r (0 : Fin 2) v
  · apply Finset.sum_congr rfl
    intro k _
    exact rateYZ_inr_cell_congr27 g xi r (0 : Fin 2) k
      (fun u => coord (g.perm r .Y) u = k.val ∧ 0 < coord (g.perm r .Z) u)
      (rateYZ_key_y_iff27 g r · k)

/-- The second grouped quantity is exactly the paper's `globalLambda`. -/
theorem globalGroupedEntropy_eq_lambda27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    globalGroupedEntropy27 g xi r 1 =
      globalLambda (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by omega
  unfold globalGroupedEntropy27
  rw [Fintype.sum_sum_type]
  unfold globalLambda
  dsimp only [globalExactGridData27, GlobalSpec.toPaper]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, h10, if_false]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro v _
    simpa only [GlobalBridge25.boundary, GlobalBridge25.side, h10, if_false] using
      rateYZ_inl_cell27 g xi r (1 : Fin 2) v
  · apply Finset.sum_congr rfl
    intro k _
    exact rateYZ_inr_cell_congr27 g xi r (1 : Fin 2) k
      (fun u => 0 < coord (g.perm r .X) u ∧ 0 < coord (g.perm r .Y) u ∧
        coord (g.perm r .Z) u = k.val)
      (rateYZ_key_z_iff27 g r · k)

/-- The Eta branch of every exact-grid regional rate is nonnegative. -/
theorem globalRegionRate_eta_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    0 ≤ entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y)) -
      globalEta (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  rw [← globalGroupedEntropy_eq_eta27 g xi r]
  exact sub_nonneg.mpr (by
    simpa only [GlobalBridge25.side, if_pos] using
      globalGroupedEntropy_le_average27 g xi r (0 : Fin 2))

/-- The Lambda branch of every exact-grid regional rate is nonnegative. -/
theorem globalRegionRate_lambda_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    0 ≤ entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)) -
      globalLambda (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  have h10 : (1 : Fin 2) ≠ 0 := by omega
  rw [← globalGroupedEntropy_eq_lambda27 g xi r]
  exact sub_nonneg.mpr (by
    simpa only [GlobalBridge25.side, h10, if_false] using
      globalGroupedEntropy_le_average27 g xi r (1 : Fin 2))

end
end OmegaBound.ADVXXZGeneral
end
