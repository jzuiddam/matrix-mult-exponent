import OmegaBound.ADVXXZGeneralGlobalExactEnvelope37
import OmegaBound.ADVXXZGeneralGlobalExactRateNonneg
import OmegaBound.ADVXXZGeneralGlobalExactEntropyCaps
import OmegaBound.ADVXXZGeneralCExact33Sublinear
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Uniform analytic envelopes for the global repair budget

These bounds implement the grid-independent part of `globalRepairBudget_uniform37`.  The loss is fixed from
`w` and the integral scale `b`, before an exact grid is supplied.  Its repair component uses
the unrestricted-top base `max 2 (2*m)` and an ambient part count at the whole scale.
-/

section
open OmegaBound Tensor3 Filter Asymptotics
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- A polynomial coefficient dominating the floor-zero demand cap. -/
noncomputable def globalBudgetPolyConst37 (w : ℕ) : ℝ := 162 * (w : ℝ) + 12

/-- A degree dominating all three summands of the floor-zero demand cap. -/
def globalBudgetPolyDegree37 (w : ℕ) : ℕ :=
  max (Fintype.card (Shape w) + Fintype.card (Fin (2*w+1)))
    (Fintype.card (Chunk w) + Fintype.card (Fin (2*w+1)) + 1)

/-- The common real scale variable used by all polynomial envelopes. -/
noncomputable def globalBudgetScale37 (b m : ℕ) : ℝ := ((b*m : ℕ) : ℝ) + 1

/-- A single repair reserve which dominates every occupied regional reserve. -/
def globalRepairCap37 (w b m : ℕ) : ℕ :=
  repairReserve (max 2 (2*m)) (fun _W => 3^(w*(b*m)))

/-- Coefficient for the square-root Salem--Spencer envelope. -/
noncomputable def globalBudgetRootConst37 (w : ℕ) : ℝ :=
  Real.log (4 * globalBudgetPolyConst37 w) + globalBudgetPolyDegree37 w +
    Real.log (Fintype.card (Shape w) : ℝ)

/-- The one loss function selected before the grid. -/
noncomputable def globalRepairLoss37 (w b : ℕ) (m : ℕ) : ℝ :=
  Real.log (640 / 11 : ℝ) + Real.log (globalBudgetPolyConst37 w) +
    (globalBudgetPolyDegree37 w + Fintype.card (Shape w)) *
      Real.log (globalBudgetScale37 b m) +
    Real.log (globalRepairCap37 w b m : ℝ) +
    4 * Real.sqrt (globalBudgetRootConst37 w) *
      Real.sqrt (globalBudgetScale37 b m)

theorem globalBudgetPolyConst37_one_le (w : ℕ) :
    1 ≤ globalBudgetPolyConst37 w := by
  unfold globalBudgetPolyConst37
  have hw : (0:ℝ) ≤ w := Nat.cast_nonneg w
  linarith

theorem globalBudgetScale37_one_le (b m : ℕ) : 1 ≤ globalBudgetScale37 b m := by
  unfold globalBudgetScale37
  have hbm : (0:ℝ) ≤ ((b*m:ℕ):ℝ) := Nat.cast_nonneg _
  linarith

set_option maxHeartbeats 400000 in
/-- The explicit demand cap is bounded by one fixed polynomial in `b*m+1`. -/
theorem globalDemandCap27_le_budgetPoly37 (w b m : ℕ) :
    globalDemandCap27 w b 0 m ≤
      globalBudgetPolyConst37 w *
        (globalBudgetScale37 b m)^(globalBudgetPolyDegree37 w) := by
  let x : ℝ := globalBudgetScale37 b m
  let a : ℕ := Fintype.card (Shape w) + Fintype.card (Fin (2*w+1))
  let c : ℕ := Fintype.card (Chunk w) + Fintype.card (Fin (2*w+1))
  let d : ℕ := globalBudgetPolyDegree37 w
  have hx : 1 ≤ x := globalBudgetScale37_one_le b m
  have had : a ≤ d := by
    dsimp only [a, d, globalBudgetPolyDegree37]
    exact le_max_left _ _
  have hcd : c + 1 ≤ d := by
    dsimp only [c, d, globalBudgetPolyDegree37]
    exact le_max_right _ _
  have ha : x^a ≤ x^d := pow_le_pow_right₀ hx had
  have hc : x^c ≤ x^d :=
    (pow_le_pow_right₀ hx (Nat.le_succ c)).trans (pow_le_pow_right₀ hx hcd)
  have hxd : 1 ≤ x^d := one_le_pow₀ hx
  have hbm : (((b*m : ℕ) : ℝ)) ≤ x := by
    dsimp only [x, globalBudgetScale37]
    linarith
  have hlast : 160 * (w:ℝ) * (b:ℝ) * (m:ℝ) * x^c ≤
      (160 * (w : ℝ)) * x^d := by
    have hprod : ((b*m : ℕ) : ℝ) * x^c ≤ x^d := by
      calc
        ((b*m : ℕ) : ℝ) * x^c ≤ x * x^c :=
          mul_le_mul_of_nonneg_right hbm (by positivity)
        _ = x^(c+1) := by rw [pow_succ]; ring
        _ ≤ x^d := pow_le_pow_right₀ hx hcd
    have := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ 160*w)
    push_cast at this
    nlinarith
  unfold globalDemandCap27
  change ((2*w+3 : ℕ) : ℝ) + 1 + 8*x^a +
      160 * (((w*(b*m) : ℕ) : ℝ)) * x^c ≤ _
  rw [show globalBudgetPolyConst37 w = 162*(w:ℝ)+12 by
    rfl]
  push_cast
  have hfirst : 2*(w:ℝ)+4 ≤ (2*(w:ℝ)+4)*x^d := by
    nlinarith [mul_le_mul_of_nonneg_left hxd (by positivity : (0:ℝ) ≤ 2*w+4)]
  have hmiddle : 8*x^a ≤ 8*x^d :=
    mul_le_mul_of_nonneg_left ha (by norm_num)
  have htotal : (2*(w:ℝ)+4) + 8*x^a + 160*(w:ℝ)*(b:ℝ)*(m:ℝ)*x^c ≤
      (2*(w:ℝ)+4)*x^d + 8*x^d + (160*(w:ℝ))*x^d :=
    add_le_add (add_le_add hfirst hmiddle) hlast
  calc
    _ ≤ (2*(w:ℝ)+4)*x^d + 8*x^d + (160*(w:ℝ))*x^d := by
      convert htotal using 1 <;> ring
    _ = (162*(w:ℝ)+12)*x^d := by ring

private theorem globalPopulation_ge_stage37 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m)) (r : Fin 6) (hm : 0 < m)
    (hn : (globalPopulation g (b*m) xi r).n ≠ 0) :
    m ≤ (globalPopulation g (b*m) xi r).n := by
  let kA : ℕ := Classical.choose (hb.2 r).1
  have hkA : (b : ℚ) * g.A.prob r = (kA : ℚ) :=
    Classical.choose_spec (hb.2 r).1
  have hkAR := congrArg (fun x : ℚ => (x : ℝ)) hkA
  have hprob : g.A.probR r = ((g.A.prob r : ℚ) : ℝ) := by
    simp [RatDist.probR, RatDist.prob, Rat.cast_div]
  have hNcast := globalPopulation_n_cast27 g hg hb xi r
  have hN : (globalPopulation g (b*m) xi r).n = kA*m := by
    apply Nat.cast_injective (R := ℝ)
    rw [hNcast, hprob]
    push_cast at hkAR ⊢
    nlinarith
  have hkApos : 0 < kA := by
    by_contra hk
    have hk0 : kA = 0 := Nat.eq_zero_of_not_pos hk
    apply hn
    rw [hN, hk0, zero_mul]
  rw [hN]
  exact Nat.le_mul_of_pos_left m hkApos

private theorem globalPart_card37 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b*m)) (r : Fin 6) (W : Side) :
    Fintype.card ((globalPopulation g (b*m) xi r).Part W) =
      3^(w*(globalPopulation g (b*m) xi r).n) := by
  classical
  have h1 : Fintype.card ((globalPopulation g (b*m) xi r).Part W) =
      @Fintype.card (Fin (globalPopulation g (b*m) xi r).n → Chunk w) inferInstance :=
    @Fintype.card_congr _ _ _ inferInstance (Equiv.refl _)
  have hchunk : Fintype.card (Chunk w) = 3^w := by simp [Chunk]
  rw [h1, Fintype.card_fun, Fintype.card_fin, hchunk, ← pow_mul]

set_option maxHeartbeats 400000 in
/-- Every target-dependent regional reserve is below the pre-grid reserve cap. -/
theorem globalRepairReserve_le_cap37 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m)) (r : Fin 6) (j0 : GlobalTargetLabel27 g xi r)
    (hm : 0 < m) (hn : (globalPopulation g (b*m) xi r).n ≠ 0) :
    repairReserve (2*(globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) ≤
      globalRepairCap37 w b m := by
  classical
  let N := (globalPopulation g (b*m) xi r).n
  have hmN : m ≤ N := globalPopulation_ge_stage37 g hg hb xi r hm hn
  have hNbm : N ≤ b*m := globalPopulation_n_le27 g xi hb r
  have hbase2 : 1 < max 2 (2*m) := by omega
  have hbase : max 2 (2*m) ≤ 2*N := by omega
  have hparts (W : Side) :
      Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W) ≤ 3^(w*(b*m)) := by
    calc
      Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W) ≤
          Fintype.card ((globalPopulation g (b*m) xi r).Part W) :=
        Fintype.card_subtype_le _
      _ = 3^(w*N) := globalPart_card37 g xi r W
      _ ≤ 3^(w*(b*m)) := Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left w hNbm)
  unfold repairReserve globalRepairCap37
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro W hW
  exact Nat.log_mono hbase2 hbase (hparts W)

private theorem natLog_budget_bound37 (k w b m : ℕ) (hk : 0 < k) :
    Nat.log (max 2 (2*m)) (3^(w*(b*m))) ≤
      2*w*b*3^k + (w*(b*m))/k := by
  by_cases hbase : 3^k ≤ max 2 (2*m)
  · exact le_trans
      (natLog_le_div_base k (w*(b*m)) (3^(w*(b*m))) (max 2 (2*m))
        hk hbase (le_refl _))
      (Nat.le_add_left _ _)
  · push_neg at hbase
    have hm : m ≤ 3^k := by omega
    calc
      Nat.log (max 2 (2*m)) (3^(w*(b*m))) ≤ 2*(w*(b*m)) :=
        natLog_three_pow_le (max 2 (2*m)) (w*(b*m))
      _ = (2*w*b)*m := by ring
      _ ≤ (2*w*b)*3^k := Nat.mul_le_mul_left (2*w*b) hm
      _ = 2*w*b*3^k := by ring
      _ ≤ 2*w*b*3^k + (w*(b*m))/k := Nat.le_add_right _ _

private theorem globalRepairCap37_pow_bound (w b m k : ℕ) (hk : 0 < k) :
    globalRepairCap37 w b m ≤
      4^(3*(2*w*b*3^k + (w*(b*m))/k)+1) := by
  unfold globalRepairCap37 repairReserve
  apply Nat.pow_le_pow_right (by norm_num)
  have hsum : (∑ _W : Side, Nat.log (max 2 (2*m)) (3^(w*(b*m)))) =
      3 * Nat.log (max 2 (2*m)) (3^(w*(b*m))) := by
    rw [Finset.sum_const, Finset.card_univ,
      show Fintype.card Side = 3 from by decide +kernel, smul_eq_mul]
  rw [hsum]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (le_refl 3) (natLog_budget_bound37 k w b m hk)) 1

/-- The logarithm of the common repair cap is sublinear in the whole scale `b*m`. -/
theorem globalRepairCap37_log_sublinear (w b : ℕ) (hb : 0 < b) :
    Sublinear (fun m => b*m) (fun m => Real.log (globalRepairCap37 w b m : ℝ)) := by
  intro δ hδ
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨k, hkpos, hkbig⟩ :
      ∃ k : ℕ, 0 < k ∧ 12*(w:ℝ)*Real.log 4/δ < (k:ℝ) := by
    obtain ⟨k0, hk0⟩ := exists_nat_gt (12*(w:ℝ)*Real.log 4/δ)
    exact ⟨k0+1, Nat.succ_pos _, by push_cast; linarith⟩
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hcoef : 12*(w:ℝ)*Real.log 4 < (k:ℝ)*δ :=
    (div_lt_iff₀ hδ).mp hkbig
  obtain ⟨M, hM⟩ :=
    exists_nat_gt (2*((3*((2*w*b*3^k : ℕ):ℝ)+1)*Real.log 4)/δ)
  refine ⟨M, fun m hm => ?_⟩
  let L := b*m
  have hL0 : (0:ℝ) ≤ (L:ℝ) := by positivity
  have hmL : (m:ℝ) ≤ (L:ℝ) := by
    exact_mod_cast (show m ≤ b*m by
      exact Nat.le_mul_of_pos_left m hb)
  have hcapPos : 0 < globalRepairCap37 w b m := repairReserve_pos _ _
  have hcapOne : (1:ℝ) ≤ (globalRepairCap37 w b m : ℝ) := by exact_mod_cast hcapPos
  have hnn : 0 ≤ Real.log (globalRepairCap37 w b m : ℝ) := Real.log_nonneg hcapOne
  rw [abs_of_nonneg hnn]
  have hcapR : (globalRepairCap37 w b m : ℝ) ≤
      (4:ℝ)^(3*(2*w*b*3^k + (w*(b*m))/k)+1) := by
    exact_mod_cast globalRepairCap37_pow_bound w b m k hkpos
  have hlogcap : Real.log (globalRepairCap37 w b m : ℝ) ≤
      ((3*(2*w*b*3^k + (w*(b*m))/k)+1 : ℕ):ℝ)*Real.log 4 := by
    have hstep := Real.log_le_log (by linarith) hcapR
    rwa [Real.log_pow] at hstep
  have hdiv : ((((w*(b*m))/k : ℕ):ℝ)) ≤
      (w:ℝ)*(L:ℝ)/(k:ℝ) := by
    refine le_trans (Nat.cast_div_le :
      ((((w*(b*m))/k : ℕ):ℝ)) ≤ (((w*(b*m):ℕ):ℝ))/(k:ℝ)) ?_
    dsimp only [L]
    push_cast
    rfl
  have hlinear : 3*((((w*(b*m))/k : ℕ):ℝ))*Real.log 4 ≤
      (δ/2)*(L:ℝ) := by
    have hbig : 3*((((w*(b*m))/k : ℕ):ℝ))*Real.log 4 ≤
        3*((w:ℝ)*(L:ℝ)/(k:ℝ))*Real.log 4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiv (by norm_num)) hlog4.le
    have hkey : 3*((w:ℝ)*(L:ℝ)/(k:ℝ))*Real.log 4 ≤
        (δ/2)*(L:ℝ) := by
      rw [show 3*((w:ℝ)*(L:ℝ)/(k:ℝ))*Real.log 4 =
        (3*(w:ℝ)*Real.log 4*(L:ℝ))/(k:ℝ) by ring, div_le_iff₀ hkR]
      have hwlog : 0 ≤ (w:ℝ)*Real.log 4 := mul_nonneg (Nat.cast_nonneg _) hlog4.le
      have hcoef6 : 6*(w:ℝ)*Real.log 4 ≤ (k:ℝ)*δ := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef6 hL0
      calc
        3*(w:ℝ)*Real.log 4*(L:ℝ) =
            (1/2:ℝ)*(6*(w:ℝ)*Real.log 4*(L:ℝ)) := by ring
        _ ≤ (1/2:ℝ)*((k:ℝ)*δ*(L:ℝ)) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = δ/2*(L:ℝ)*(k:ℝ) := by ring
    exact hbig.trans hkey
  have hconst : (3*((2*w*b*3^k : ℕ):ℝ)+1)*Real.log 4 ≤
      (δ/2)*(L:ℝ) := by
    have hmR : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have h1 : 2*((3*((2*w*b*3^k : ℕ):ℝ)+1)*Real.log 4)/δ < (m:ℝ) :=
      lt_of_lt_of_le hM hmR
    have h2 : 2*((3*((2*w*b*3^k : ℕ):ℝ)+1)*Real.log 4) < (m:ℝ)*δ :=
      (div_lt_iff₀ hδ).mp h1
    have h3 : (m:ℝ)*δ ≤ (L:ℝ)*δ := mul_le_mul_of_nonneg_right hmL hδ.le
    linarith
  have hcast : ((3*(2*w*b*3^k + (w*(b*m))/k)+1 : ℕ):ℝ) =
      (3*((2*w*b*3^k : ℕ):ℝ)+1) + 3*((((w*(b*m))/k : ℕ):ℝ)) := by
    push_cast
    ring
  calc
    Real.log (globalRepairCap37 w b m : ℝ) ≤
        ((3*(2*w*b*3^k + (w*(b*m))/k)+1 : ℕ):ℝ)*Real.log 4 := hlogcap
    _ = (3*((2*w*b*3^k : ℕ):ℝ)+1)*Real.log 4 +
        3*((((w*(b*m))/k : ℕ):ℝ))*Real.log 4 := by rw [hcast]; ring
    _ ≤ (δ/2)*(L:ℝ) + (δ/2)*(L:ℝ) := add_le_add hconst hlinear
    _ = δ*((b*m:ℕ):ℝ) := by dsimp only [L]; ring

private theorem globalBudgetScale37_tendsto (b : ℕ) (hb : 0 < b) :
    Tendsto (globalBudgetScale37 b) atTop atTop := by
  unfold globalBudgetScale37
  simpa [Nat.cast_mul] using tendsto_atTop_add_const_right atTop (1:ℝ)
    (Tendsto.const_mul_atTop (by exact_mod_cast hb) tendsto_natCast_atTop_atTop)

private theorem globalBudgetScale37_isBigO (b : ℕ) (hb : 0 < b) :
    globalBudgetScale37 b =O[atTop] (fun m => ((b*m:ℕ):ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by exact (globalBudgetScale37_one_le b m).trans' zero_le_one),
    abs_of_nonneg (Nat.cast_nonneg _)]
  unfold globalBudgetScale37
  have hbm : (1:ℕ) ≤ b*m := Nat.mul_pos hb (by omega)
  exact_mod_cast (show b*m+1 ≤ 2*(b*m) by omega)

private theorem globalBudgetLog37_isLittleO (b : ℕ) (hb : 0 < b) :
    (fun m => Real.log (globalBudgetScale37 b m)) =o[atTop]
      (fun m => ((b*m:ℕ):ℝ)) := by
  have hlog : (fun m => Real.log (globalBudgetScale37 b m)) =o[atTop]
      globalBudgetScale37 b := by
    simpa only [Function.comp_apply] using
      Real.isLittleO_log_id_atTop.comp_tendsto (globalBudgetScale37_tendsto b hb)
  exact hlog.trans_isBigO (globalBudgetScale37_isBigO b hb)

private theorem globalBudgetSqrt37_isLittleO (b : ℕ) (hb : 0 < b) :
    (fun m => Real.sqrt (globalBudgetScale37 b m)) =o[atTop]
      (fun m => ((b*m:ℕ):ℝ)) := by
  have hsqrt : (fun m => Real.sqrt (globalBudgetScale37 b m)) =o[atTop]
      globalBudgetScale37 b := by
    rw [isLittleO_iff_tendsto']
    · simpa [Real.sqrt_div_self] using tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp (globalBudgetScale37_tendsto b hb))
    · filter_upwards with m hm
      have hx : 0 < globalBudgetScale37 b m :=
        lt_of_lt_of_le zero_lt_one (globalBudgetScale37_one_le b m)
      exact (hx.ne' hm).elim
  exact hsqrt.trans_isBigO (globalBudgetScale37_isBigO b hb)

private theorem globalBudgetConst37_isLittleO (b : ℕ) (hb : 0 < b) (C : ℝ) :
    (fun _m : ℕ => C) =o[atTop] (fun m => ((b*m:ℕ):ℝ)) := by
  have ht : Tendsto (fun m : ℕ => ((b*m:ℕ):ℝ)) atTop atTop := by
    simpa [Nat.cast_mul] using
      Tendsto.const_mul_atTop (by exact_mod_cast hb) tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using (isLittleO_const_id_atTop C).comp_tendsto ht

private theorem sublinear_add37 {L : ℕ → ℕ} {f h : ℕ → ℝ}
    (hf : Sublinear L f) (hh : Sublinear L h) :
    Sublinear L (fun m => f m + h m) := by
  intro δ hδ
  obtain ⟨Mf, hMf⟩ := hf (δ/2) (by linarith)
  obtain ⟨Mh, hMh⟩ := hh (δ/2) (by linarith)
  refine ⟨max Mf Mh, fun m hm => ?_⟩
  have hf' := hMf m (le_trans (le_max_left _ _) hm)
  have hh' := hMh m (le_trans (le_max_right _ _) hm)
  calc
    |f m + h m| ≤ |f m| + |h m| := abs_add_le _ _
    _ ≤ (δ/2)*(L m:ℝ) + (δ/2)*(L m:ℝ) := add_le_add hf' hh'
    _ = δ*(L m:ℝ) := by ring

private theorem globalRepairSimpleLoss37_sublinear (w b : ℕ) (hb : 0 < b) :
    Sublinear (fun m => b*m) (fun m =>
      Real.log (640/11:ℝ) + Real.log (globalBudgetPolyConst37 w) +
        (globalBudgetPolyDegree37 w + Fintype.card (Shape w)) *
          Real.log (globalBudgetScale37 b m) +
        4*Real.sqrt (globalBudgetRootConst37 w)*
          Real.sqrt (globalBudgetScale37 b m)) := by
  let C0 := Real.log (640/11:ℝ) + Real.log (globalBudgetPolyConst37 w)
  let Cl := ((globalBudgetPolyDegree37 w + Fintype.card (Shape w) : ℕ):ℝ)
  let Cs := 4*Real.sqrt (globalBudgetRootConst37 w)
  have h : (fun m : ℕ => C0 + Cl*Real.log (globalBudgetScale37 b m) +
      Cs*Real.sqrt (globalBudgetScale37 b m)) =o[atTop]
      (fun m => ((b*m:ℕ):ℝ)) :=
    ((globalBudgetConst37_isLittleO b hb C0).add
      ((globalBudgetLog37_isLittleO b hb).const_mul_left Cl)).add
      ((globalBudgetSqrt37_isLittleO b hb).const_mul_left Cs)
  apply sublinear_of_isLittleO
  simpa only [C0, Cl, Cs, Nat.cast_add, Nat.cast_ofNat] using h

theorem globalBudgetRootConst37_nonneg (w : ℕ) : 0 ≤ globalBudgetRootConst37 w := by
  unfold globalBudgetRootConst37
  have hC : 1 ≤ 4*globalBudgetPolyConst37 w := by
    nlinarith [globalBudgetPolyConst37_one_le w]
  have hQ : 1 ≤ (Fintype.card (Shape w) : ℝ) := by
    have hQnat : 0 < Fintype.card (Shape w) := Fintype.card_pos
    exact_mod_cast hQnat
  have hlogC : 0 ≤ Real.log (4*globalBudgetPolyConst37 w) := Real.log_nonneg hC
  have hlogQ : 0 ≤ Real.log (Fintype.card (Shape w) : ℝ) := Real.log_nonneg hQ
  positivity

/-- The selected loss is nonnegative at every stage. -/
theorem globalRepairLoss37_nonneg (w b m : ℕ) : 0 ≤ globalRepairLoss37 w b m := by
  unfold globalRepairLoss37
  have hratio : (1:ℝ) ≤ 640/11 := by norm_num
  have hC := globalBudgetPolyConst37_one_le w
  have hx := globalBudgetScale37_one_le b m
  have hR : (1:ℝ) ≤ (globalRepairCap37 w b m : ℝ) := by
    exact_mod_cast repairReserve_pos (max 2 (2*m)) (fun _W : Side => 3^(w*(b*m)))
  have hroot := globalBudgetRootConst37_nonneg w
  have hlogRatio : 0 ≤ Real.log (640/11:ℝ) := Real.log_nonneg hratio
  have hlogC : 0 ≤ Real.log (globalBudgetPolyConst37 w) := Real.log_nonneg hC
  have hlogX : 0 ≤ Real.log (globalBudgetScale37 b m) := Real.log_nonneg hx
  have hlogR : 0 ≤ Real.log (globalRepairCap37 w b m : ℝ) := Real.log_nonneg hR
  positivity

/-- The selected loss is `o(b*m)`. -/
theorem globalRepairLoss37_sublinear (w b : ℕ) (hb : 0 < b) :
    Sublinear (fun m => b*m) (globalRepairLoss37 w b) := by
  have hs := globalRepairSimpleLoss37_sublinear w b hb
  have hr := globalRepairCap37_log_sublinear w b hb
  have hadd := sublinear_add37 hs hr
  have heq : globalRepairLoss37 w b = fun m =>
      (Real.log (640/11:ℝ) + Real.log (globalBudgetPolyConst37 w) +
        (globalBudgetPolyDegree37 w + Fintype.card (Shape w)) *
          Real.log (globalBudgetScale37 b m) +
        4*Real.sqrt (globalBudgetRootConst37 w)*Real.sqrt (globalBudgetScale37 b m)) +
      Real.log (globalRepairCap37 w b m : ℝ) := by
    funext m
    unfold globalRepairLoss37
    ring
  rw [heq]
  exact hadd

end
end OmegaBound.ADVXXZGeneral
end
