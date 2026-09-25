import OmegaBound.ADVXXZGeneralCExact41Continuity
import OmegaBound.ADVXXZGeneralCExact41DemandCompat
import OmegaBound.ADVXXZGeneralCExact39RawSelection
import OmegaBound.ADVXXZGeneralCExact33Sublinear

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The alpha type-class exponent, restated on the CExact40 import path. -/
noncomputable def constituentAlphaNats41 {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * (d.A t).probR r *
    entropy (d.toPaper.alpha t r)

/-- The exact target type-class denominator, restated on the CExact40 import path. -/
noncomputable def constituentTargetPoly41 {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  ∏ t : Fin s, ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
    Fintype.card (ChildShape p t)

private theorem c41_rat_floor_nat (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem c41_stageAlphaCount_cast {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) :
    ((StageCandidateRaw.stageAlphaCount b m p d r t u : ℕ) : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u := by
  rcases hb.alphaIntegral t r u with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob u = ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) * ((b : ℚ) * p.baseN t * (d.A t).prob r *
          (d.alpha t r).prob u) := by push_cast; ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  unfold StageCandidateRaw.stageAlphaCount
  rw [hscaled, c41_rat_floor_nat]

private theorem c41_stageParentCount_cast {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    ((StageCandidateRaw.stageParentCount b m p d r t : ℕ) : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r := by
  rw [StageCandidateRaw.stageParentCount, Nat.cast_sum]
  simp_rw [c41_stageAlphaCount_cast p d hb r t]
  rw [← Finset.mul_sum, (d.alpha t r).sum_prob, mul_one]

private theorem c41_stageAlpha_normalized {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s)
    (hn : StageCandidateRaw.stageParentCount b m p d r t ≠ 0) :
    (fun u : ChildShape p t =>
      (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
        StageCandidateRaw.stageParentCount b m p d r t) = d.toPaper.alpha t r := by
  funext u
  have hnumQ := c41_stageAlphaCount_cast p d hb r t u
  have hdenQ := c41_stageParentCount_cast p d hb r t
  have hnumR :
      (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) =
        ((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r *
          (d.alpha t r).probR u := by
    rw [probR_eq_cast_prob33, probR_eq_cast_prob33]
    exact_mod_cast hnumQ
  have hdenR :
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) =
        ((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r := by
    rw [probR_eq_cast_prob33]
    exact_mod_cast hdenQ
  have hscale :
      ((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r ≠ 0 := by
    rw [← hdenR]
    exact_mod_cast hn
  simp only [ConstituentSpec.toPaper]
  rw [hnumR, hdenR]
  exact mul_div_cancel_left₀ _ hscale

private theorem c41_target_factor_numerator {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
      entropyNats (fun u : ChildShape p t =>
        (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
          StageCandidateRaw.stageParentCount b m p d r t)) =
      Real.exp (((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r *
        (Real.log 2 * entropy (d.toPaper.alpha t r))) := by
  by_cases hn : StageCandidateRaw.stageParentCount b m p d r t = 0
  · have hdenQ := c41_stageParentCount_cast p d hb r t
    rw [hn, Nat.cast_zero] at hdenQ
    have hmassQ : ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r = 0 :=
      hdenQ.symm
    have hmassR : ((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r = 0 := by
      rw [probR_eq_cast_prob33]
      exact_mod_cast hmassQ
    rw [hn]
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero]
    rw [hmassR, zero_mul]
    exact Real.exp_zero.symm
  · rw [c41_stageAlpha_normalized p d hb r t hn,
      entropyNats_eq_log_two_mul_entropy40]
    congr 1
    have hdenQ := c41_stageParentCount_cast p d hb r t
    have hdenR :
        (StageCandidateRaw.stageParentCount b m p d r t : ℝ) =
          ((b * m * p.baseN t : ℕ) : ℝ) * (d.A t).probR r := by
      rw [probR_eq_cast_prob33]
      exact_mod_cast hdenQ
    rw [hdenR]

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent product of target type-class bounds is the only large step here.
/-- Exact target-label entropy lower bound, on the CExact40-compatible import path. -/
theorem stageTargetLabel_rate_lower41 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    Real.exp (constituentAlphaNats41 p d r * (b * m : ℝ)) /
        constituentTargetPoly41 (b := b) (m := m) p d r ≤
      (Fintype.card (StageTargetLabel37 q p d b m r) : ℝ) := by
  have hbank := stageTargetLabel_typeClass_lower37 (b := b) (m := m) q p d r
  rw [Finset.prod_div_distrib] at hbank
  have hnum : (∏ t : Fin s,
      Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        entropyNats (fun u : ChildShape p t =>
          (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
            StageCandidateRaw.stageParentCount b m p d r t))) =
      Real.exp (constituentAlphaNats41 p d r * (b * m : ℝ)) := by
    simp_rw [c41_target_factor_numerator p d hb r]
    rw [← Real.exp_sum]
    congr 1
    unfold constituentAlphaNats41
    push_cast
    calc
      (∑ x, (b : ℝ) * m * p.baseN x * (d.A x).probR r *
          (Real.log 2 * entropy (d.toPaper.alpha x r))) =
          ∑ x, ((b : ℝ) * m) *
            ((p.baseN x : ℝ) * (d.A x).probR r *
              entropy (d.toPaper.alpha x r)) * Real.log 2 := by
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = ((b : ℝ) * m) *
          (∑ x, ((p.baseN x : ℝ) * (d.A x).probR r *
            entropy (d.toPaper.alpha x r))) * Real.log 2 := by
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
      _ = _ := by ring
  rw [hnum] at hbank
  simpa only [constituentTargetPoly41] using hbank

/-- Total exponent of the uniform polynomial envelope for constituent target type classes. -/
def constituentTargetDegree41 {w s : ℕ} (p : ConstituentInput w s) : ℕ :=
  ∑ t : Fin s, Fintype.card (ChildShape p t)

/-- The target type-class denominator is bounded by one polynomial fixed before the grid. -/
theorem constituentTargetPoly_le41 {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    constituentTargetPoly41 (b := b) (m := m) p d r ≤
      ((cLength p b m : ℝ) + 1) ^ constituentTargetDegree41 p := by
  have hparent : ∀ t : Fin s,
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) ≤ cLength p b m := by
    intro t
    have hbase : p.baseN t ≤ constituentBaseTotal p := by
      unfold constituentBaseTotal
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)
    have hnat : StageCandidateRaw.stageParentCount b m p d r t ≤ cLength p b m :=
      (stageParentCount_le b m p d r t).trans (by
        unfold cLength
        calc
          b * m * p.baseN t = p.baseN t * (b * m) := by ring
          _ ≤ constituentBaseTotal p * (b * m) := Nat.mul_le_mul_right _ hbase)
    exact_mod_cast hnat
  unfold constituentTargetPoly41 constituentTargetDegree41
  calc
    (∏ t : Fin s, ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
        Fintype.card (ChildShape p t)) ≤
      ∏ t : Fin s, ((cLength p b m : ℝ) + 1) ^
        Fintype.card (ChildShape p t) := by
          refine Finset.prod_le_prod (fun _ _ => by positivity) (fun t _ => ?_)
          exact pow_le_pow_left₀ (by positivity) (by linarith [hparent t]) _
    _ = ((cLength p b m : ℝ) + 1) ^
        ∑ t : Fin s, Fintype.card (ChildShape p t) :=
      Finset.prod_pow_eq_pow_sum _ _ _

private theorem c41_sub_max_eq_min_sub (a x y z : ℝ) :
    a - max x (max y z) = min (a - x) (min (a - y) (a - z)) := by
  rw [min_sub_sub_left, min_sub_sub_left]

private theorem c41_alpha_sub_x {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r * entropy (d.toPaper.alpha t r)) -
      (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
        (entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r -
          entropy (constituentMarginal d.toPaper t r (d.perm r .X)))) =
      constituentRowX d.toPaper r (d.perm r .X) := by
  unfold constituentRowX
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem c41_alpha_sub_y {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r * entropy (d.toPaper.alpha t r)) -
      (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
        (entropy (d.toPaper.alpha t r) +
          constituentEta d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
          splitEntropy (d.betaRegion (d.perm r .Y) t r))) =
      constituentRowY d.toPaper r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) := by
  unfold constituentRowY
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ConstituentSpec.toPaper]
  ring

private theorem c41_alpha_sub_z {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r * entropy (d.toPaper.alpha t r)) -
      (∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
        (entropy (d.toPaper.alpha t r) +
          constituentLambda d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
          splitEntropy (d.betaRegion (d.perm r .Z) t r))) =
      constituentRowZ d.toPaper r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) := by
  unfold constituentRowZ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ConstituentSpec.toPaper]
  ring

/-- The alpha target exponent minus demand is the paper constituent rate, in nats. -/
theorem constituentAlphaNats_sub_demand41 {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    constituentAlphaNats41 p d r - demandExponent p d r =
      Real.log 2 * constituentRegionRate d.toPaper r := by
  let A : ℝ := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    entropy (d.toPaper.alpha t r)
  let X : ℝ := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r -
      entropy (constituentMarginal d.toPaper t r (d.perm r .X)))
  let Y : ℝ := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) +
      constituentEta d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
      splitEntropy (d.betaRegion (d.perm r .Y) t r))
  let Z : ℝ := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) +
      constituentLambda d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
      splitEntropy (d.betaRegion (d.perm r .Z) t r))
  have hAprob : (∑ t, (p.baseN t : ℝ) * (d.A t).probR r *
      entropy (d.toPaper.alpha t r)) = A := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [ConstituentSpec.toPaper, RatDist.probR]
  have hx : A - X = constituentRowX d.toPaper r (d.perm r .X) :=
    c41_alpha_sub_x p d r
  have hy : A - Y = constituentRowY d.toPaper r
      (d.perm r .X) (d.perm r .Y) (d.perm r .Z) := c41_alpha_sub_y p d r
  have hz : A - Z = constituentRowZ d.toPaper r
      (d.perm r .X) (d.perm r .Y) (d.perm r .Z) := c41_alpha_sub_z p d r
  unfold constituentAlphaNats41 demandExponent constituentRegionRate
  dsimp only
  rw [hAprob]
  calc
    Real.log 2 * A - Real.log 2 * max X (max Y Z) =
        Real.log 2 * (A - max X (max Y Z)) := by ring
    _ = Real.log 2 * min (A - X) (min (A - Y) (A - Z)) := by
      rw [c41_sub_max_eq_min_sub]
    _ = _ := by rw [hx, hy, hz]; simp only [ConstituentSpec.toPaper]

theorem selection_budget_quotient_arith41
    {Er E P Cap R es k M T Bc ell : ℝ}
    (hEr : 0 < Er) (hE : 0 < E) (hP : 0 < P) (hCap : 0 < Cap)
    (hR : 0 < R) (hes : 0 < es) (hk : 1 ≤ k) (hM : 0 < M)
    (hMfourk : M ≤ 4*k) (hMcap : M ≤ 4*Cap*E)
    (hB : k*es⁻¹ ≤ Bc) (hT : Er*E/P ≤ T)
    (hloss : Real.log (320/11:ℝ) + Real.log Cap + Real.log P +
      Real.log R + Real.log es ≤ ell) :
    Real.exp (Real.log Er - ell) ≤ (11/20:ℝ)*T*Bc/(M^2*R) := by
  have hT0 : 0 ≤ T := (div_pos (mul_pos hEr hE) hP).le.trans hT
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hlowB0 : 0 ≤ k*es⁻¹ := mul_nonneg hk0 (inv_nonneg.mpr hes.le)
  have hB0 : 0 ≤ Bc := hlowB0.trans hB
  have hnum : (Er*E/P)*(k*es⁻¹) ≤ T*Bc :=
    mul_le_mul hT hB hlowB0 hT0
  have hMsq : M^2 ≤ 16*k*Cap*E := by
    calc
      M^2 = M*M := by ring
      _ ≤ (4*k)*(4*Cap*E) := mul_le_mul hMfourk hMcap hM.le (by positivity)
      _ = 16*k*Cap*E := by ring
  have hden : M^2*R ≤ (16*k*Cap*E)*R :=
    mul_le_mul_of_nonneg_right hMsq hR.le
  have hsmallDen : 0 < M^2*R := mul_pos (sq_pos_of_pos hM) hR
  have hquot : Er/((320/11:ℝ)*Cap*P*R*es) ≤
      (11/20:ℝ)*T*Bc/(M^2*R) := by
    calc
      Er/((320/11:ℝ)*Cap*P*R*es) =
          (11/20:ℝ)*((Er*E/P)*(k*es⁻¹))/((16*k*Cap*E)*R) := by
        field_simp [ne_of_gt hE, ne_of_gt hP, ne_of_gt hCap, ne_of_gt hR,
          ne_of_gt hes, ne_of_gt (lt_of_lt_of_le zero_lt_one hk)]
        ring
      _ ≤ (11/20:ℝ)*(T*Bc)/((16*k*Cap*E)*R) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnum (by norm_num)) (by positivity)
      _ ≤ (11/20:ℝ)*(T*Bc)/(M^2*R) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) (mul_nonneg hT0 hB0)) hsmallDen hden
      _ = (11/20:ℝ)*T*Bc/(M^2*R) := by ring
  have hratio : (0:ℝ) < 320/11 := by norm_num
  have hexpTerms : Real.exp (Real.log (320/11:ℝ) + Real.log Cap + Real.log P +
      Real.log R + Real.log es) = (320/11:ℝ)*Cap*P*R*es := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log hratio, Real.exp_log hCap, Real.exp_log hP,
      Real.exp_log hR, Real.exp_log hes]
  calc
    Real.exp (Real.log Er-ell) ≤ Real.exp (Real.log Er-
        (Real.log (320/11:ℝ)+Real.log Cap+Real.log P+Real.log R+Real.log es)) := by
      exact Real.exp_le_exp.mpr (sub_le_sub_left hloss _)
    _ = Er/((320/11:ℝ)*Cap*P*R*es) := by
      rw [Real.exp_sub, Real.exp_log hEr, hexpTerms]
    _ ≤ (11/20:ℝ)*T*Bc/(M^2*R) := hquot

end
end OmegaBound.ADVXXZGeneral
