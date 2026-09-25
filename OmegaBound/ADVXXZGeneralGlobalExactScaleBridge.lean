import OmegaBound.ADVXXZGeneralGlobalExactExponentIdentities

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem scaledIntegralCount27 (b m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * a = (k : ℚ)) :
    (((b * m : ℕ) : ℚ) * a).floor.toNat = k * m := by
  have hq : (((b * m : ℕ) : ℚ) * a) = ((k * m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k * m : ℕ) : ℚ).floor) = (k * m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k * m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k * m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

private theorem probR_eq_castProb27 {α : Type*} [Fintype α]
    (P : RatDist α) (a : α) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem globalScaleCoordFin_val27 {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem globalCellCount_cast_raw27 {w b m : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (r : Fin 6) (u : Shape w) :
    ((((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℝ) =
      ((b * m : ℕ) : ℝ) * g.joint.probR (r, u) := by
  let k : ℕ := Classical.choose (((hb.2 r).2 u).1)
  have hk : (b : ℚ) * g.joint.prob (r, u) = (k : ℚ) :=
    Classical.choose_spec (((hb.2 r).2 u).1)
  rw [scaledIntegralCount27 b m k (g.joint.prob (r, u)) hk]
  have hkR := congrArg (fun x : ℚ => (x : ℝ)) hk
  rw [probR_eq_castProb27]
  push_cast at hkR ⊢
  nlinarith

/-- At an integral scale, a regional population has exactly `b*m*A_r` positions. -/
theorem globalPopulation_n_cast27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) :
    ((globalPopulation g (b * m) xi r).n : ℝ) =
      ((b * m : ℕ) : ℝ) * g.A.probR r := by
  classical
  let kA : ℕ := Classical.choose (hb.2 r).1
  let k : Shape w → ℕ := fun u => Classical.choose (((hb.2 r).2 u).1)
  have hkA : (b : ℚ) * g.A.prob r = (kA : ℚ) :=
    Classical.choose_spec (hb.2 r).1
  have hk : ∀ u, (b : ℚ) * g.joint.prob (r, u) = (k u : ℚ) :=
    fun u => Classical.choose_spec (((hb.2 r).2 u).1)
  have hksum : ∑ u, k u = kA := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    calc
      ∑ u : Shape w, (k u : ℚ) =
          ∑ u : Shape w, (b : ℚ) * g.joint.prob (r, u) := by
        apply Finset.sum_congr rfl
        intro u _
        exact (hk u).symm
      _ = (b : ℚ) * ∑ u : Shape w, g.joint.prob (r, u) := by
        rw [Finset.mul_sum]
      _ = (b : ℚ) * g.A.prob r := by
        apply congrArg ((b : ℚ) * ·)
        calc
          ∑ u : Shape w, g.joint.prob (r, u) =
              ∑ u : Shape w, g.A.prob r * (g.alpha r).prob u := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hg.joint_eq r u]
          _ = g.A.prob r * ∑ u : Shape w, (g.alpha r).prob u := by
            rw [Finset.mul_sum]
          _ = g.A.prob r := by rw [(g.alpha r).sum_prob, mul_one]
      _ = (kA : ℚ) := hkA
  have hn : (globalPopulation g (b * m) xi r).n = kA * m := by
    change ∑ u : Shape w,
      ((((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) = kA * m
    simp_rw [fun u => scaledIntegralCount27 b m (k u) (g.joint.prob (r, u)) (hk u)]
    rw [← Finset.sum_mul, hksum]
  rw [hn, probR_eq_castProb27]
  have hkR := congrArg (fun x : ℚ => (x : ℝ)) hkA
  push_cast at hkR ⊢
  nlinarith

/-- Every physical shape cell has mass `N_r * alpha_r(u)` at an integral scale. -/
theorem globalCellCount_cast27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (u : Shape w) :
    ((((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℝ) =
      ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR u := by
  rw [globalCellCount_cast_raw27 g hb r u, globalPopulation_n_cast27 g hg hb xi r]
  have hj := congrArg (fun x : ℚ => (x : ℝ)) (hg.joint_eq r u)
  have hjR : g.joint.probR (r, u) = g.A.probR r * (g.alpha r).probR u := by
    simpa only [probR_eq_castProb27, Rat.cast_mul] using hj
  rw [hjR]
  ring

/-- On every occupied region, the exact target type-class exponent is the paper alpha
    entropy, with the standard polynomial type loss. -/
theorem globalTargetLabel_paper_entropy_bounds27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    let N := (globalPopulation g (b * m) xi r).n
    Real.exp ((N : ℝ) * (Real.log 2 * entropy (g.toPaper.alpha r))) /
          ((N : ℝ) + 1) ^ Fintype.card (Shape w) ≤
        (Fintype.card (GlobalTargetLabel27 g xi r) : ℝ) ∧
      (Fintype.card (GlobalTargetLabel27 g xi r) : ℝ) ≤
        Real.exp ((N : ℝ) * (Real.log 2 * entropy (g.toPaper.alpha r))) := by
  let N := (globalPopulation g (b * m) xi r).n
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdist : (fun u : Shape w =>
      ((((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℝ) / N) =
      g.toPaper.alpha r := by
    funext u
    rw [globalCellCount_cast27 g hg hb xi r u]
    change (N : ℝ) * (g.alpha r).probR u / N = (g.alpha r).probR u
    field_simp
  have hH : entropyNats (fun u : Shape w =>
      ((((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℝ) / N) =
      Real.log 2 * entropy (g.toPaper.alpha r) := by
    rw [hdist, entropyNats_eq_log_two_mul_entropy]
  have h := globalTargetLabel_entropy_bounds27 g xi r
  dsimp only at h ⊢
  simpa only [N, hH] using h

private theorem globalExactGridAverage_prob27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (S : Side) (sigma : Chunk w) :
    ((∑ u : Shape w, xi.count S r u sigma : ℕ) : ℝ) /
        (globalPopulation g (b * m) xi r).n =
      globalAverage (globalExactGridData27 g xi) r S sigma := by
  classical
  let N := (globalPopulation g (b * m) xi r).n
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Nat.cast_sum, Finset.sum_div]
  unfold globalAverage globalExactGridData27
  dsimp only [GlobalSpec.toPaper]
  apply Finset.sum_congr rfl
  intro u _
  let k := (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat
  by_cases hk : 0 < k
  · rw [globalExactGridBeta_probR27 g xi S r u sigma hk]
    change (xi.count S r u sigma : ℝ) / (N : ℝ) =
      (g.alpha r).probR u * ((xi.count S r u sigma : ℝ) / (k : ℝ))
    have hkR : (k : ℝ) = (N : ℝ) * (g.alpha r).probR u := by
      simpa only [k, N] using globalCellCount_cast27 g hg hb xi r u
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp
    nlinarith
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hcount : xi.count S r u sigma = 0 := by
      have hle : xi.count S r u sigma ≤ ∑ tau, xi.count S r u tau :=
        Finset.single_le_sum (fun tau _ => Nat.zero_le _) (Finset.mem_univ sigma)
      rw [xi.total S r u, show
        (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0 from hk0] at hle
      omega
    have halpha : (g.alpha r).probR u = 0 := by
      have hcell := globalCellCount_cast27 g hg hb xi r u
      rw [show
        (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0 from hk0,
        Nat.cast_zero] at hcell
      exact (mul_eq_zero.mp hcell.symm).resolve_left hNR
    rw [hcount, halpha]
    norm_num

private theorem globalExactGridMarginal_prob27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (S : Side) (c : Fin (2 * w + 1)) :
    ((∑ u : Shape w,
      if Parent25.coordFin S u = c then
        (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 : ℕ) : ℝ) /
        (globalPopulation g (b * m) xi r).n =
      marginal (g.toPaper.alpha r) S c := by
  classical
  let N := (globalPopulation g (b * m) xi r).n
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Nat.cast_sum, Finset.sum_div]
  unfold marginal
  apply Finset.sum_congr rfl
  intro u _
  by_cases huc : Parent25.coordFin S u = c
  · have hcoord : coord S u = (c : ℕ) := by
      exact (globalScaleCoordFin_val27 S u).symm.trans (congrArg Fin.val huc)
    rw [if_pos huc, if_pos hcoord, globalCellCount_cast27 g hg hb xi r u]
    change ((N : ℝ) * (g.alpha r).probR u) / N = (g.alpha r).probR u
    field_simp
  · have hcoord : coord S u ≠ (c : ℕ) := by
      intro h
      apply huc
      apply Fin.ext
      exact (globalScaleCoordFin_val27 S u).trans h
    rw [if_neg huc, if_neg hcoord]
    norm_num

/-- On an occupied integral region, the finite P exponent is exactly the paper aggregate
    entropy minus the corresponding shape marginal entropy. -/
theorem globalPExponent_paper27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (which : Fin 2) (beta : GlobalRepresentedLaw g (b * m) xi r which) :
    GlobalBridge25.pExponent g (b * m) xi r which beta =
      ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        (entropy (globalAverage (globalExactGridData27 g xi) r
            (GlobalBridge25.side g r which)) -
          entropy (marginal (g.toPaper.alpha r)
            (GlobalBridge25.side g r which))) := by
  rw [globalPExponent_exactGrid27 g xi r which beta]
  dsimp only
  have havg : (fun sigma : Chunk w =>
      ((∑ u : Shape w,
        xi.count (GlobalBridge25.side g r which) r u sigma : ℕ) : ℝ) /
          (globalPopulation g (b * m) xi r).n) =
      globalAverage (globalExactGridData27 g xi) r
        (GlobalBridge25.side g r which) := by
    funext sigma
    exact globalExactGridAverage_prob27 g hg hb xi r hn _ sigma
  have hmarg : (fun c : Fin (2 * w + 1) =>
      ((∑ u : Shape w,
        if Parent25.coordFin (GlobalBridge25.side g r which) u = c then
          (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 : ℕ) : ℝ) /
          (globalPopulation g (b * m) xi r).n) =
      marginal (g.toPaper.alpha r) (GlobalBridge25.side g r which) := by
    funext c
    exact globalExactGridMarginal_prob27 g hg hb xi r hn _ c
  rw [havg, hmarg, entropyNats_eq_log_two_mul_entropy,
    entropyNats_eq_log_two_mul_entropy]
  ring

end
end OmegaBound.ADVXXZGeneral
end
