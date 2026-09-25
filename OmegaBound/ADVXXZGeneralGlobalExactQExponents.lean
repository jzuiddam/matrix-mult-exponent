import OmegaBound.ADVXXZGeneralGlobalExactScaleBridge

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem qex_scaled_entropy_rho27 {alpha : Type*} [Fintype alpha]
    (n : ℕ) (k : alpha → ℕ) (L mass : ℝ) (rho : alpha → ℝ)
    (hn : (n : ℝ) = L * mass)
    (hk : ∀ a, (k a : ℝ) = L * mass * rho a) :
    (n : ℝ) * entropyNats (fun a => (k a : ℝ) / n) =
      L * mass * entropyNats rho := by
  by_cases hn0 : n = 0
  · have hzero : L * mass = 0 := by simpa [hn0] using hn.symm
    simp [hn0, hzero]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hnormalized : (fun a => (k a : ℝ) / n) = rho := by
      funext a
      rw [hk a, ← hn]
      exact mul_div_cancel_left₀ _ hnR
    rw [hnormalized, hn]

private theorem qex_scaled_entropy_num27 {alpha : Type*} [Fintype alpha]
    (n : ℕ) (k : alpha → ℕ) (L mass : ℝ) (num : alpha → ℝ)
    (hn : (n : ℝ) = L * mass)
    (hk : ∀ a, (k a : ℝ) = L * num a) :
    (n : ℝ) * entropyNats (fun a => (k a : ℝ) / n) =
      L * mass * entropyNats (fun a => num a / mass) := by
  by_cases hn0 : n = 0
  · have hzero : L * mass = 0 := by simpa [hn0] using hn.symm
    simp [hn0, hzero]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hprod : L * mass ≠ 0 := hn ▸ hnR
    have hL : L ≠ 0 := left_ne_zero_of_mul hprod
    have hmass : mass ≠ 0 := right_ne_zero_of_mul hprod
    have hnormalized : (fun a => (k a : ℝ) / n) = fun a => num a / mass := by
      funext a
      rw [hk a, hn]
      field_simp [hL, hmass]
    rw [hnormalized, hn]

private theorem qex_coordFin_val27 {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem qex_count_cast27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (S : Side)
    (u : Shape w) (sigma : Chunk w) :
    (xi.count S r u sigma : ℝ) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR u *
        (globalExactGridBeta27 g xi S r u).probR sigma := by
  let k := (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat
  by_cases hk : 0 < k
  · rw [globalExactGridBeta_probR27 g xi S r u sigma hk]
    have hcell := globalCellCount_cast27 g hg hb xi r u
    change (k : ℝ) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR u at hcell
    change (xi.count S r u sigma : ℝ) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR u *
        ((xi.count S r u sigma : ℝ) / (k : ℝ))
    rw [← hcell]
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp [hkR]
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hcount : xi.count S r u sigma = 0 := by
      have hle : xi.count S r u sigma ≤ ∑ tau, xi.count S r u tau :=
        Finset.single_le_sum (fun tau _ => Nat.zero_le _) (Finset.mem_univ sigma)
      rw [xi.total S r u, show
        (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0 from hk0] at hle
      omega
    have hcell := globalCellCount_cast27 g hg hb xi r u
    rw [show
      (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0 from hk0,
      Nat.cast_zero] at hcell
    rw [hcount, Nat.cast_zero, ← hcell]
    simp

private theorem qex_key_eq_inl_iff27 {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (W : Fin 2) (u v : Shape w) :
    GlobalBridge25.key g r W u = Sum.inl v ↔
      GlobalBridge25.boundary g r W u ∧ u = v := by
  classical
  unfold GlobalBridge25.key
  by_cases h : GlobalBridge25.boundary g r W u
  · simp [h]
  · simp [h]

private theorem qex_key_eq_inr_iff27 {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (W : Fin 2) (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r W u = Sum.inr k ↔
      ¬ GlobalBridge25.boundary g r W u ∧
        Parent25.coordFin (GlobalBridge25.side g r W) u = k := by
  classical
  unfold GlobalBridge25.key
  by_cases h : GlobalBridge25.boundary g r W u
  · simp [h]
  · simp [h]

private theorem qex_boundary_histogram_of27 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (v : Shape w) (sigma : Chunk w) (hv : GlobalBridge25.boundary g r W v) :
    GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma =
      xi.count (GlobalBridge25.side g r W) r v sigma := by
  classical
  unfold GlobalBridge25.histogram
  simp only [qex_key_eq_inl_iff27]
  have hcond : ∀ u : Shape w,
      (GlobalBridge25.boundary g r W u ∧ u = v) ↔ u = v := by
    intro u
    constructor
    · exact And.right
    · intro huv
      subst u
      exact ⟨hv, rfl⟩
  simp_rw [hcond]
  rw [Finset.sum_ite_eq']
  simp

private theorem qex_boundary_histogram_not27 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (v : Shape w) (sigma : Chunk w) (hv : ¬ GlobalBridge25.boundary g r W v) :
    GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma = 0 := by
  classical
  unfold GlobalBridge25.histogram
  simp only [qex_key_eq_inl_iff27]
  have hnone : ∀ u : Shape w,
      ¬(GlobalBridge25.boundary g r W u ∧ u = v) := by
    intro u hu
    exact hv (hu.2 ▸ hu.1)
  simp [hnone]

private theorem qex_residual_histogram_cast27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (k : Fin (2 * w + 1)) (sigma : Chunk w) :
    (GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma : ℝ) =
      ((globalPopulation g (b * m) xi r).n : ℝ) *
        (∑ u, if GlobalBridge25.key g r W u = Sum.inr k then
          (g.alpha r).probR u *
            (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r u).probR sigma
          else 0) := by
  classical
  unfold GlobalBridge25.histogram
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : GlobalBridge25.key g r W u = Sum.inr k
  · simp only [hu, if_pos]
    simpa only [mul_assoc] using
      qex_count_cast27 g hg hb xi r (GlobalBridge25.side g r W) u sigma
  · simp [hu]

private theorem qex_boundary_cell_entropy_of27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (v : Shape w) (hv : GlobalBridge25.boundary g r W v) :
    let n := ∑ sigma, GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma
    (n : ℝ) * entropyNats (fun sigma =>
      (GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma : ℝ) / n) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR v *
        entropyNats
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r v).probR := by
  classical
  dsimp only
  let n := ∑ sigma, GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma
  let L := ((globalPopulation g (b * m) xi r).n : ℝ)
  have hhist : ∀ sigma : Chunk w,
      (GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma : ℝ) =
        L * (g.alpha r).probR v *
          (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r v).probR sigma := by
    intro sigma
    rw [qex_boundary_histogram_of27 g xi r W v sigma hv]
    exact qex_count_cast27 g hg hb xi r (GlobalBridge25.side g r W) v sigma
  have hn : (n : ℝ) = L * (g.alpha r).probR v := by
    calc
      (n : ℝ) = ∑ sigma,
          (GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma : ℝ) := by
            norm_cast
      _ = ∑ sigma, L * (g.alpha r).probR v *
          (globalExactGridBeta27 g xi
            (GlobalBridge25.side g r W) r v).probR sigma := by
            apply Finset.sum_congr rfl
            intro sigma _
            exact hhist sigma
      _ = L * (g.alpha r).probR v := by
            rw [← Finset.mul_sum,
              (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r v).sum_probR,
              mul_one]
  exact qex_scaled_entropy_rho27 n
    (GlobalBridge25.histogram g (b * m) xi r W (.inl v)) L
    ((g.alpha r).probR v)
    (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r v).probR hn hhist

private theorem qex_boundary_cell_entropy_not27 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (v : Shape w) (hv : ¬ GlobalBridge25.boundary g r W v) :
    let n := ∑ sigma, GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma
    (n : ℝ) * entropyNats (fun sigma =>
      (GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma : ℝ) / n) = 0 := by
  classical
  dsimp only
  have hhist : ∀ sigma : Chunk w,
      GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma = 0 := by
    intro sigma
    exact qex_boundary_histogram_not27 g xi r W v sigma hv
  have hn : (∑ sigma,
      GlobalBridge25.histogram g (b * m) xi r W (.inl v) sigma) = 0 := by
    simp only [hhist, Finset.sum_const_zero]
  rw [hn]
  simp

private theorem qex_residual_cell_entropy27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (W : Fin 2)
    (k : Fin (2 * w + 1)) :
    let n := ∑ sigma, GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma
    let mass := ∑ u, if GlobalBridge25.key g r W u = Sum.inr k then
      (g.alpha r).probR u else 0
    (n : ℝ) * entropyNats (fun sigma =>
      (GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma : ℝ) / n) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * mass *
        entropyNats (weightedSplit (g.alpha r).probR
          (fun u => globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r u)
          (fun u => GlobalBridge25.key g r W u = Sum.inr k)) := by
  classical
  dsimp only
  let n := ∑ sigma, GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma
  let L := ((globalPopulation g (b * m) xi r).n : ℝ)
  let mass := ∑ u, if GlobalBridge25.key g r W u = Sum.inr k then
    (g.alpha r).probR u else 0
  let num : Chunk w → ℝ := fun sigma =>
    ∑ u, if GlobalBridge25.key g r W u = Sum.inr k then
      (g.alpha r).probR u *
        (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r u).probR sigma
      else 0
  have hhist : ∀ sigma,
      (GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma : ℝ) =
        L * num sigma := by
    intro sigma
    exact qex_residual_histogram_cast27 g hg hb xi r W k sigma
  have hnumsum : ∑ sigma, num sigma = mass := by
    unfold num mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : GlobalBridge25.key g r W u = Sum.inr k
    · simp only [hu, if_pos, ← Finset.mul_sum,
        (globalExactGridBeta27 g xi (GlobalBridge25.side g r W) r u).sum_probR,
        mul_one]
    · simp [hu]
  have hn : (n : ℝ) = L * mass := by
    calc
      (n : ℝ) = ∑ sigma,
          (GlobalBridge25.histogram g (b * m) xi r W (.inr k) sigma : ℝ) := by
            norm_cast
      _ = ∑ sigma, L * num sigma := by
            apply Finset.sum_congr rfl
            intro sigma _
            exact hhist sigma
      _ = L * mass := by rw [← Finset.mul_sum, hnumsum]
  have hscaled := qex_scaled_entropy_num27 n
    (GlobalBridge25.histogram g (b * m) xi r W (.inr k)) L mass num hn hhist
  simpa only [weightedSplit, num, mass] using hscaled

private theorem qex_key_y_iff27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r (0 : Fin 2) u = Sum.inr k ↔
      coord (g.perm r .Y) u = k.val ∧ 0 < coord (g.perm r .Z) u := by
  rw [qex_key_eq_inr_iff27]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, if_pos,
    Fin.ext_iff, qex_coordFin_val27]
  omega

private theorem qex_key_z_iff27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (u : Shape w) (k : Fin (2 * w + 1)) :
    GlobalBridge25.key g r (1 : Fin 2) u = Sum.inr k ↔
      0 < coord (g.perm r .X) u ∧ 0 < coord (g.perm r .Y) u ∧
        coord (g.perm r .Z) u = k.val := by
  have h10 : (1 : Fin 2) ≠ 0 := by omega
  rw [qex_key_eq_inr_iff27]
  simp only [GlobalBridge25.boundary, GlobalBridge25.side, h10, if_false,
    Fin.ext_iff, qex_coordFin_val27]
  omega

private theorem qex_weightedSplit_congr27 {iota : Type*} [Fintype iota]
    {w : ℕ} (mass : iota → ℝ) (laws : iota → SplitDist w)
    (P Q : iota → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ u, P u ↔ Q u) :
    weightedSplit mass laws P = weightedSplit mass laws Q := by
  funext sigma
  unfold weightedSplit
  apply congrArg₂ (· / ·)
  · apply Finset.sum_congr rfl
    intro u _
    exact if_congr (h u) rfl rfl
  · apply Finset.sum_congr rfl
    intro u _
    exact if_congr (h u) rfl rfl

/-- The exact finite Q exponent is the paper Eta/Lambda perspective for the literal grid
    datum. The statement includes zero-mass merged cells. -/
theorem globalQExponent_paper27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (which : Fin 2) :
    GlobalBridge25.qExponent g (b * m) xi r which =
      ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        (if which = 0 then
          globalEta (globalExactGridData27 g xi) r
            (g.perm r .X) (g.perm r .Y) (g.perm r .Z)
        else
          globalLambda (globalExactGridData27 g xi) r
            (g.perm r .X) (g.perm r .Y) (g.perm r .Z)) := by
  classical
  unfold GlobalBridge25.qExponent
  rw [Fintype.sum_sum_type]
  let L := ((globalPopulation g (b * m) xi r).n : ℝ)
  have hcells :
      (∑ v : Shape w,
          let n := ∑ sigma,
            GlobalBridge25.histogram g (b * m) xi r which (.inl v) sigma
          (n : ℝ) * entropyNats (fun sigma =>
            (GlobalBridge25.histogram g (b * m) xi r which (.inl v) sigma : ℝ) / n)) +
        (∑ k : Fin (2 * w + 1),
          let n := ∑ sigma,
            GlobalBridge25.histogram g (b * m) xi r which (.inr k) sigma
          (n : ℝ) * entropyNats (fun sigma =>
            (GlobalBridge25.histogram g (b * m) xi r which (.inr k) sigma : ℝ) / n)) =
      (∑ v : Shape w,
          if GlobalBridge25.boundary g r which v then
            L * (g.alpha r).probR v *
              entropyNats (globalExactGridBeta27 g xi
                (GlobalBridge25.side g r which) r v).probR
          else 0) +
        ∑ k : Fin (2 * w + 1),
          let mass := ∑ u, if GlobalBridge25.key g r which u = Sum.inr k then
            (g.alpha r).probR u else 0
          L * mass * entropyNats
            (weightedSplit (g.alpha r).probR
              (fun u => globalExactGridBeta27 g xi
                (GlobalBridge25.side g r which) r u)
              (fun u => GlobalBridge25.key g r which u = Sum.inr k)) := by
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : GlobalBridge25.boundary g r which v
      · rw [if_pos hv]
        exact qex_boundary_cell_entropy_of27 g hg hb xi r which v hv
      · rw [if_neg hv]
        exact qex_boundary_cell_entropy_not27 g xi r which v hv
    · apply Finset.sum_congr rfl
      intro k _
      exact qex_residual_cell_entropy27 g hg hb xi r which k
  rw [hcells]
  by_cases hwhich : which = 0
  · subst which
    simp only [GlobalBridge25.boundary, GlobalBridge25.side, if_pos]
    simp_rw [entropyNats_eq_log_two_mul_entropy]
    simp_rw [qex_key_y_iff27]
    unfold globalEta splitEntropy
    dsimp only [globalExactGridData27, GlobalSpec.toPaper]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : coord (g.perm r .Z) v = 0
      · simp only [hv, if_pos]
        ring
      · simp [hv]
    · apply Finset.sum_congr rfl
      intro k _
      have hweighted :
          weightedSplit (g.alpha r).probR
              (fun u => globalExactGridBeta27 g xi (g.perm r .Y) r u)
              (fun u => GlobalBridge25.key g r (0 : Fin 2) u = Sum.inr k) =
            weightedSplit (g.alpha r).probR
              (fun u => globalExactGridBeta27 g xi (g.perm r .Y) r u)
              (fun u => coord (g.perm r .Y) u = k.val ∧
                0 < coord (g.perm r .Z) u) := by
        apply qex_weightedSplit_congr27
        intro u
        exact qex_key_y_iff27 g r u k
      rw [hweighted]
      ring
  · have hwhich1 : which = 1 := by omega
    subst which
    have h10 : (1 : Fin 2) ≠ 0 := by omega
    simp only [GlobalBridge25.boundary, GlobalBridge25.side, h10, if_false]
    simp_rw [entropyNats_eq_log_two_mul_entropy]
    simp_rw [qex_key_z_iff27]
    unfold globalLambda splitEntropy
    dsimp only [globalExactGridData27, GlobalSpec.toPaper]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : coord (g.perm r .X) v = 0 ∨ coord (g.perm r .Y) v = 0
      · simp only [hv, if_pos]
        ring
      · simp [hv]
    · apply Finset.sum_congr rfl
      intro k _
      have hweighted :
          weightedSplit (g.alpha r).probR
              (fun u => globalExactGridBeta27 g xi (g.perm r .Z) r u)
              (fun u => GlobalBridge25.key g r (1 : Fin 2) u = Sum.inr k) =
            weightedSplit (g.alpha r).probR
              (fun u => globalExactGridBeta27 g xi (g.perm r .Z) r u)
              (fun u => 0 < coord (g.perm r .X) u ∧
                0 < coord (g.perm r .Y) u ∧ coord (g.perm r .Z) u = k.val) := by
        apply qex_weightedSplit_congr27
        intro u
        exact qex_key_z_iff27 g r u k
      rw [hweighted]
      ring

/-- The `which = 0` specialization of the exact global Q exponent. -/
theorem globalQExponent_eta27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) :
    GlobalBridge25.qExponent g (b * m) xi r 0 =
      ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        globalEta (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  simpa using globalQExponent_paper27 g hg hb xi r (0 : Fin 2)

/-- The `which = 1` specialization of the exact global Q exponent. -/
theorem globalQExponent_lambda27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) :
    GlobalBridge25.qExponent g (b * m) xi r 1 =
      ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        globalLambda (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) := by
  simpa using globalQExponent_paper27 g hg hb xi r (1 : Fin 2)

end
end OmegaBound.ADVXXZGeneral
end
