import OmegaBound.ADVXXZGeneralCExact42GridPool

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3 Filter
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The exact full-grid cardinality has sublinear logarithm in the constituent scale. -/
theorem constituent_full_grid_pool28_log_sublinear {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (b : ℕ)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (ε : ℚ) (hε : 0 < ε) :
    Sublinear (cLength p b)
      (fun m => Real.log (Fintype.card (ConstituentFullGrid27 d m ε) : ℝ)) := by
  intro δ hδ
  let dim := ConstituentGridDimension p d
  let c : ℝ := δ / (2 * ((dim : ℝ) + 1))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htend : Tendsto (fun m : ℕ => ((cLength p b m + 1 : ℕ) : ℝ))
      atTop atTop := by
    rw [tendsto_atTop]
    intro A
    obtain ⟨M, hM⟩ := exists_nat_ge A
    refine eventually_atTop.2 ⟨M, fun m hm => ?_⟩
    have hnat : M ≤ cLength p b m + 1 := by
      exact le_trans hm (le_trans (le_cLength 1 p d b m hb.1)
        (Nat.le_succ _))
    exact hM.trans (by exact_mod_cast hnat)
  have hlo := Real.isLittleO_log_id_atTop.comp_tendsto htend
  have hev := hlo.bound hc
  rw [eventually_atTop] at hev
  obtain ⟨M₀, hM₀⟩ := hev
  obtain ⟨Mp, hMp⟩ := constituent_full_grid_pool28 d b hd hb ε hε
  refine ⟨max (max M₀ Mp) 1, fun m hm => ?_⟩
  have hm₀ : M₀ ≤ m := (Nat.le_max_left M₀ Mp).trans
    ((Nat.le_max_left (max M₀ Mp) 1).trans hm)
  have hmp : Mp ≤ m := (Nat.le_max_right M₀ Mp).trans
    ((Nat.le_max_left (max M₀ Mp) 1).trans hm)
  have hm1 : 1 ≤ m := (Nat.le_max_right (max M₀ Mp) 1).trans hm
  let L := cLength p b m
  have hL : 0 < L := lt_of_lt_of_le (Nat.zero_lt_succ 0)
    (le_trans hm1 (le_cLength 1 p d b m hb.1))
  have hxpos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
  have hxone : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
  have hlogx : Real.log ((L + 1 : ℕ) : ℝ) ≤ c * ((L + 1 : ℕ) : ℝ) := by
    have hs := hM₀ m hm₀
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs, L] at hs
    rw [abs_of_nonneg (Real.log_nonneg hxone), abs_of_nonneg hxpos.le] at hs
    exact hs
  have hQpos : 0 < Fintype.card (ConstituentFullGrid27 d m ε) :=
    Fintype.card_pos_iff.mpr ⟨constituentCentreFullGrid42 d hd hb m ε hε.le⟩
  have hQone : (1 : ℝ) ≤
      (Fintype.card (ConstituentFullGrid27 d m ε) : ℝ) := by
    exact_mod_cast hQpos
  have hcard := (hMp m hmp).2
  have hQposR : (0 : ℝ) <
      (Fintype.card (ConstituentFullGrid27 d m ε) : ℝ) := by
    exact_mod_cast hQpos
  have hcardR :
      (Fintype.card (ConstituentFullGrid27 d m ε) : ℝ) ≤
        (((L + 1)^ConstituentGridDimension p d : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hlogcard := Real.log_le_log hQposR hcardR
  have hcastpow : ((((L + 1)^ConstituentGridDimension p d : ℕ) : ℝ)) =
      (((L + 1 : ℕ) : ℝ) ^ ConstituentGridDimension p d) := by norm_num
  rw [hcastpow, Real.log_pow] at hlogcard
  have hden : (0 : ℝ) < 2 * ((dim : ℝ) + 1) := by positivity
  have hcoef : 2 * (dim : ℝ) * c ≤ δ := by
    calc
      2 * (dim : ℝ) * c =
          (2 * (dim : ℝ) * δ) / (2 * ((dim : ℝ) + 1)) := by
            dsimp [c]
            ring
      _ ≤ δ := (div_le_iff₀ hden).2 (by
        have hdim : (0 : ℝ) ≤ dim := by positivity
        nlinarith)
  have hxle : (((L + 1 : ℕ) : ℝ)) ≤ 2 * ((L : ℕ) : ℝ) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  rw [abs_of_nonneg (Real.log_nonneg hQone)]
  calc
    Real.log (Fintype.card (ConstituentFullGrid27 d m ε) : ℝ) ≤
        (ConstituentGridDimension p d : ℝ) *
          Real.log ((L + 1 : ℕ) : ℝ) := hlogcard
    _ ≤ (dim : ℝ) * (c * ((L + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlogx (by positivity)
    _ ≤ (dim : ℝ) * (c * (2 * ((L : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxle hc.le) (by positivity)
    _ = (2 * (dim : ℝ) * c) * ((L : ℕ) : ℝ) := by ring
    _ ≤ δ * ((L : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

end
end OmegaBound.ADVXXZGeneral
end
