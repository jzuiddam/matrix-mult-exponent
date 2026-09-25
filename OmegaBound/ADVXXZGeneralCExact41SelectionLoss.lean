import OmegaBound.ADVXXZGeneralCExact41SelectionAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open OmegaBound Tensor3 Filter Asymptotics
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The coefficient of the demand logarithm `constituentDemandLogLoss40`. -/
noncomputable def constituentDemandCoeff41 {w s : ℕ} (p : ConstituentInput w s)
    (b floor : ℕ) : ℝ :=
  constituentDemandLogLoss40 p b floor 1 / Real.log 2

theorem constituentDemandLogLoss_eq41 {w s : ℕ} (p : ConstituentInput w s)
    (b floor m : ℕ) :
    constituentDemandLogLoss40 p b floor m =
      constituentDemandCoeff41 p b floor * Real.log ((m : ℝ) + 1) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold constituentDemandCoeff41 constituentDemandLogLoss40 constituentPCompLoss40
  rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
  field_simp

theorem constituentDemandCoeff_nonneg41 {w s : ℕ} (p : ConstituentInput w s)
    (b floor : ℕ) : 0 ≤ constituentDemandCoeff41 p b floor := by
  unfold constituentDemandCoeff41
  apply div_nonneg
  · unfold constituentDemandLogLoss40 constituentPCompLoss40
    positivity
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- A fixed coefficient bounding `log k` by a multiple of the whole scale plus one. -/
noncomputable def constituentSelectionRootCoeff41 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b floor : ℕ)
    (rho : ℚ → ℝ) (ε : ℚ) : ℝ :=
  Real.log 4 + constituentDemandCoeff41 p b floor +
    (∑ r : Fin 6, |demandExponent p d r|) + rho ε +
      constituentPCompDelta40 p ε

/-- The finite part of the selection ledger.  The repair reserve is deliberately absent:
it is charged to the vanishing `|ε|` part of the exponential debit. -/
noncomputable def constituentSelectionLoss41 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b floor : ℕ)
    (rho : ℚ → ℝ) (ε : ℚ) (m : ℕ) : ℝ :=
  Real.log (320 / 11 : ℝ) + constituentDemandLogLoss40 p b floor m +
    (constituentTargetDegree41 p : ℝ) *
      Real.log ((cLength p b m : ℝ) + 1) +
    4 * Real.sqrt (constituentSelectionRootCoeff41 p d b floor rho ε) *
      Real.sqrt ((cLength p b m : ℝ) + 1)

private theorem c41_loss_add {L : ℕ → ℕ} {f g : ℚ → ℕ → ℝ}
    (hf : Loss L f) (hg : Loss L g) :
    Loss L (fun ε m => f ε m + g ε m) := by
  constructor
  · intro ε m
    exact add_nonneg (hf.1 ε m) (hg.1 ε m)
  · intro ε hε δ hδ
    obtain ⟨Mf, hMf⟩ := hf.2 ε hε (δ / 2) (half_pos hδ)
    obtain ⟨Mg, hMg⟩ := hg.2 ε hε (δ / 2) (half_pos hδ)
    refine ⟨max Mf Mg, fun m hm => ?_⟩
    calc
      |f ε m + g ε m| ≤ |f ε m| + |g ε m| := abs_add_le _ _
      _ ≤ (δ / 2) * (L m : ℝ) + (δ / 2) * (L m : ℝ) :=
        add_le_add (hMf m ((le_max_left _ _).trans hm))
          (hMg m ((le_max_right _ _).trans hm))
      _ = δ * (L m : ℝ) := by ring

private theorem c41_baseTotal_pos {w s : ℕ} (p : ConstituentInput w s) :
    0 < constituentBaseTotal p := by
  unfold constituentBaseTotal
  let t : Fin s := ⟨0, p.terms_nonempty⟩
  exact lt_of_lt_of_le (p.baseN_pos t)
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))

private theorem c41_cLength_tendsto {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) :
    Tendsto (fun m => (cLength p b m : ℝ)) atTop atTop := by
  have hcoef : (0 : ℝ) < constituentBaseTotal p * b := by
    positivity [c41_baseTotal_pos p]
  simpa only [cLength, Nat.cast_mul, mul_assoc] using
    Tendsto.const_mul_atTop hcoef tendsto_natCast_atTop_atTop

private theorem c41_scale_tendsto {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) :
    Tendsto (fun m => (cLength p b m : ℝ) + 1) atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 1 (c41_cLength_tendsto p hb)

private theorem c41_scale_isBigO {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) :
    (fun m => (cLength p b m : ℝ) + 1) =O[atTop]
      (fun m => (cLength p b m : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (cLength p b m : ℝ) + 1),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hmL : m ≤ cLength p b m := by
    have hbase : 1 ≤ constituentBaseTotal p := c41_baseTotal_pos p
    have hb1 : 1 ≤ b := hb
    unfold cLength
    calc
      m = 1 * (1 * m) := by ring
      _ ≤ constituentBaseTotal p * (b * m) :=
        Nat.mul_le_mul hbase (Nat.mul_le_mul hb1 le_rfl)
  have hL : 1 ≤ cLength p b m := hm.trans hmL
  exact_mod_cast (show cLength p b m + 1 ≤ 2 * cLength p b m by omega)

private theorem c41_log_scale_isLittleO {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) :
    (fun m => Real.log ((cLength p b m : ℝ) + 1)) =o[atTop]
      (fun m => (cLength p b m : ℝ)) := by
  have hlog : (fun m => Real.log ((cLength p b m : ℝ) + 1)) =o[atTop]
      (fun m => (cLength p b m : ℝ) + 1) := by
    simpa only [Function.comp_apply] using
      Real.isLittleO_log_id_atTop.comp_tendsto (c41_scale_tendsto p hb)
  exact hlog.trans_isBigO (c41_scale_isBigO p hb)

private theorem c41_sqrt_scale_isLittleO {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) :
    (fun m => Real.sqrt ((cLength p b m : ℝ) + 1)) =o[atTop]
      (fun m => (cLength p b m : ℝ)) := by
  have hsqrt : (fun m => Real.sqrt ((cLength p b m : ℝ) + 1)) =o[atTop]
      (fun m => (cLength p b m : ℝ) + 1) := by
    rw [isLittleO_iff_tendsto']
    · simpa [Real.sqrt_div_self] using tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp (c41_scale_tendsto p hb))
    · filter_upwards with m hm
      have hx : 0 < (cLength p b m : ℝ) + 1 := by positivity
      exact (hx.ne' hm).elim
  exact hsqrt.trans_isBigO (c41_scale_isBigO p hb)

private theorem c41_const_isLittleO {w s b : ℕ} (p : ConstituentInput w s)
    (hb : 0 < b) (C : ℝ) :
    (fun _m : ℕ => C) =o[atTop] (fun m => (cLength p b m : ℝ)) := by
  simpa [Function.comp_def] using
    (isLittleO_const_id_atTop C).comp_tendsto (c41_cLength_tendsto p hb)

private theorem c41_demand_loss {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hb : 0 < b) (floor : ℕ) :
    Loss (cLength p b)
      (fun _ε m => constituentDemandLogLoss40 p b floor m) := by
  have hC := constituentDemandCoeff_nonneg41 p b floor
  have hold := log_succ_loss b hb (constituentDemandCoeff41 p b floor) hC
  constructor
  · intro ε m
    change 0 ≤ constituentDemandLogLoss40 p b floor m
    rw [constituentDemandLogLoss_eq41]
    exact hold.1 ε m
  · intro ε hε δ hδ
    obtain ⟨M, hM⟩ := hold.2 ε hε δ hδ
    refine ⟨M, fun m hm => ?_⟩
    change |constituentDemandLogLoss40 p b floor m| ≤
      δ * (cLength p b m : ℝ)
    rw [constituentDemandLogLoss_eq41]
    have hbound := hM m hm
    have hbm : b * m ≤ cLength p b m := by
      unfold cLength
      calc
        b * m = 1 * (b * m) := by ring
        _ ≤ constituentBaseTotal p * (b * m) :=
          Nat.mul_le_mul_right (b * m)
            (Nat.succ_le_iff.mpr (c41_baseTotal_pos p))
    exact hbound.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbm) hδ.le)

theorem constituentSelectionRootCoeff_nonneg41 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (floor : ℕ) (rho : ℚ → ℝ)
    (hrho : VanishesWithTolerance rho) (ε : ℚ) :
    0 ≤ constituentSelectionRootCoeff41 p d b floor rho ε := by
  unfold constituentSelectionRootCoeff41
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsum : 0 ≤ ∑ r : Fin 6, |demandExponent p d r| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpcomp := (constituentPCompDelta40_vanishes p).1 ε
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg hlog (constituentDemandCoeff_nonneg41 p b floor)) hsum)
      (hrho.1 ε)) hpcomp

/-- The selected finite ledger satisfies both clauses of `ConstituentFiniteLoss29`. -/
theorem constituentSelectionLoss_finite41 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hb : 0 < b) (floor : ℕ) (rho : ℚ → ℝ)
    (hrho : VanishesWithTolerance rho) :
    ConstituentFiniteLoss29 p b
      (constituentSelectionLoss41 p d b floor rho) := by
  have hC0 : 0 ≤ Real.log (320 / 11 : ℝ) := Real.log_nonneg (by norm_num)
  have hconst : Loss (cLength p b)
      (fun _ε _m => Real.log (320 / 11 : ℝ)) := by
    constructor
    · intro ε m
      exact hC0
    · intro ε hε
      apply sublinear_of_isLittleO
      exact c41_const_isLittleO p hb _
  have hdemand := c41_demand_loss p d hb floor
  have htarget : Loss (cLength p b) (fun _ε m =>
      (constituentTargetDegree41 p : ℝ) *
        Real.log ((cLength p b m : ℝ) + 1)) := by
    constructor
    · intro ε m
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by
          have hL : (0 : ℝ) ≤ cLength p b m := Nat.cast_nonneg _
          linarith))
    · intro ε hε
      apply sublinear_of_isLittleO
      exact (c41_log_scale_isLittleO p hb).const_mul_left _
  have hroot : Loss (cLength p b) (fun ε m =>
      4 * Real.sqrt (constituentSelectionRootCoeff41 p d b floor rho ε) *
        Real.sqrt ((cLength p b m : ℝ) + 1)) := by
    constructor
    · intro ε m
      exact mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    · intro ε hε
      apply sublinear_of_isLittleO
      exact (c41_sqrt_scale_isLittleO p hb).const_mul_left _
  have hloss : Loss (cLength p b) (constituentSelectionLoss41 p d b floor rho) := by
    simpa only [constituentSelectionLoss41] using
      c41_loss_add (c41_loss_add (c41_loss_add hconst hdemand) htarget) hroot
  refine ⟨hloss, ?_⟩
  intro ε hε
  let C0 : ℝ := Real.log (320 / 11 : ℝ)
  let Cd : ℝ := constituentDemandCoeff41 p b floor
  let Ct : ℝ := constituentTargetDegree41 p
  let Cs : ℝ := 4 * Real.sqrt (constituentSelectionRootCoeff41 p d b floor rho ε)
  let C : ℝ := C0 + Cd + Ct + Cs
  have hCd : 0 ≤ Cd := constituentDemandCoeff_nonneg41 p b floor
  have hCt : 0 ≤ Ct := Nat.cast_nonneg _
  have hCs : 0 ≤ Cs := by positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, 0, ?_⟩
  intro m hm
  let L : ℝ := cLength p b m
  let G : ℝ := L / Real.log (L + 2) + Real.sqrt (L + 1) +
    Real.log (L + 2) + 1
  have hlog2 : 0 < Real.log (L + 2) := Real.log_pos (by
    dsimp only [L]
    have hL : (0 : ℝ) ≤ cLength p b m := Nat.cast_nonneg _
    linarith)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hGone : 1 ≤ G := by
    dsimp only [G]
    have hdiv : 0 ≤ L / Real.log (L + 2) := div_nonneg (by positivity) hlog2.le
    have hsqrt : 0 ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log (L + 2) := hlog2.le
    linarith
  have hGsqrt : Real.sqrt (L + 1) ≤ G := by
    dsimp only [G]
    have hdiv : 0 ≤ L / Real.log (L + 2) := div_nonneg (by positivity) hlog2.le
    have hlog : 0 ≤ Real.log (L + 2) := hlog2.le
    linarith
  have hGlog : Real.log (L + 2) ≤ G := by
    dsimp only [G]
    have hdiv : 0 ≤ L / Real.log (L + 2) := div_nonneg (by positivity) hlog2.le
    have hsqrt : 0 ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
    linarith
  have hmLnat : m ≤ cLength p b m := le_cLength 1 p d b m hb
  have hmL : (m : ℝ) + 1 ≤ L + 2 := by
    dsimp only [L]
    exact_mod_cast (show m + 1 ≤ cLength p b m + 2 by omega)
  have hLlog : Real.log ((m : ℝ) + 1) ≤ Real.log (L + 2) := by
    exact Real.log_le_log (by positivity) hmL
  have honeL : L + 1 ≤ L + 2 := by linarith
  have htargetLog : Real.log (L + 1) ≤ Real.log (L + 2) :=
    Real.log_le_log (by positivity) honeL
  show constituentSelectionLoss41 p d b floor rho ε m ≤ C * G
  rw [constituentSelectionLoss41, constituentDemandLogLoss_eq41]
  change C0 + Cd * Real.log ((m : ℝ) + 1) +
      Ct * Real.log (L + 1) + Cs * Real.sqrt (L + 1) ≤ C * G
  calc
    _ ≤ C0 * G + Cd * G + Ct * G + Cs * G := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · calc
              C0 = C0 * 1 := by ring
              _ ≤ C0 * G := mul_le_mul_of_nonneg_left hGone hC0
          · exact mul_le_mul_of_nonneg_left (hLlog.trans hGlog) hCd
        · exact mul_le_mul_of_nonneg_left (htargetLog.trans hGlog) hCt
      · exact mul_le_mul_of_nonneg_left hGsqrt hCs
    _ = C * G := by dsimp only [C]; ring

end
end OmegaBound.ADVXXZGeneral
