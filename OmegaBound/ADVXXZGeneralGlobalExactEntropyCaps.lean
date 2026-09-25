import OmegaBound.ADVXXZGeneralGlobalExactDemandCap

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Base-two Shannon entropy of a finite probability distribution never exceeds the
    base-two logarithm of the alphabet size. -/
theorem entropy_le_logb_card27 {iota : Type*} [Fintype iota] (p : iota → ℝ)
    (hp : IsProbability p) :
    entropy p ≤ Real.log (Fintype.card iota : ℝ) / Real.log 2 := by
  classical
  have hne : Nonempty iota := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hsum := hp.2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hH := Entropy.H_le_log_card (s := (Finset.univ : Finset iota))
    Finset.univ_nonempty (fun u _ => hp.1 u) (by simpa using hp.2)
  have hHn : entropyNats p ≤ Real.log (Fintype.card iota : ℝ) := by
    calc
      entropyNats p = Entropy.H Finset.univ p :=
        (Entropy.H_eq_neg_sum Finset.univ p).symm
      _ ≤ Real.log ((Finset.univ : Finset iota).card : ℝ) := hH
      _ = _ := by simp
  rw [entropyNats_eq_log_two_mul_entropy, mul_comm] at hHn
  exact (le_div_iff₀ (Real.log_pos one_lt_two)).2 hHn

/-- The paper's shape entropy plus its marginal penalty is still at most the base-two
    logarithm of the shape alphabet: the penalty is measured against the same alphabet. -/
theorem entropy_add_penalty_le_logb_card27 {w : ℕ} (p : Shape w → ℝ)
    (hp : IsProbability p) :
    entropy p + penalty p ≤ Real.log (Fintype.card (Shape w) : ℝ) / Real.log 2 := by
  classical
  have hmem : entropy p ∈ {h : ℝ | ∃ p' : Shape w → ℝ,
      IsProbability p' ∧ SameMarginals p p' ∧ h = entropy p'} :=
    ⟨p, hp, fun _ _ => rfl, rfl⟩
  have hsup : sSup {h : ℝ | ∃ p' : Shape w → ℝ,
      IsProbability p' ∧ SameMarginals p p' ∧ h = entropy p'} ≤
      Real.log (Fintype.card (Shape w) : ℝ) / Real.log 2 := by
    refine csSup_le ⟨entropy p, hmem⟩ ?_
    rintro h ⟨p', hp', -, rfl⟩
    exact entropy_le_logb_card27 p' hp'
  unfold penalty
  linarith

private theorem gec_ratio_le_one27 (a c : ℕ) (h : a ≤ c) : ((a : ℝ)) / (c : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · rw [div_le_one (by exact_mod_cast hc)]
    exact_mod_cast h

private theorem gec_globalPcomp_le_one27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    globalPcomp g n xi r which beta ≤ 1 := by
  classical
  unfold globalPcomp
  dsimp only
  exact gec_ratio_le_one27 _ _ (Finset.card_filter_le _ _)

/-- The compatibility maximum is a ratio of finite fibres, hence at most one. -/
theorem globalPcompMax_le_one27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    globalPcompMax g n xi r which ≤ 1 := by
  classical
  unfold globalPcompMax
  dsimp only
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g n xi r which)).image
    (globalPcomp g n xi r which)
  by_cases hv : values.Nonempty
  · rw [dif_pos hv]
    rcases Finset.mem_image.mp (Finset.max'_mem values hv) with ⟨beta, -, hbeta⟩
    rw [← hbeta]
    exact gec_globalPcomp_le_one27 g xi r which beta
  · rw [dif_neg hv]
    norm_num

theorem globalDemandCap27_pos (w b floor m : ℕ) : 0 < globalDemandCap27 w b floor m := by
  unfold globalDemandCap27
  have hfl : (0 : ℝ) ≤ ((max floor (2 * w + 3) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h8 : (0 : ℝ) ≤ 8 * (((b * m : ℕ) : ℝ) + 1) ^
      (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) := by positivity
  have h160 : (0 : ℝ) ≤ 160 * ((w * (b * m) : ℕ) : ℝ) * (((b * m : ℕ) : ℝ) + 1) ^
      (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) := by positivity
  linarith

/--
**Logarithmic demand cap.**  The logarithm of the global natural demand splits into
a grid-free polynomial term and the region's paper demand exponent.
-/
theorem globalDemand_log_cap27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (floor : ℕ) (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    Real.log (globalDemand g b floor m xi r) ≤
      Real.log (globalDemandCap27 w b floor m) +
        ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          globalDemandBits27 g xi r := by
  have hcap := globalDemand_paper_cap27 g hg hb floor xi hxi r hn
  have hpos : (0 : ℝ) < (globalDemand g b floor m xi r : ℝ) := by
    have hfloor : max floor (2 * w + 3) ≤ globalDemand g b floor m xi r :=
      globalDemand_floor_le g floor m xi r
    have : 0 < globalDemand g b floor m xi r := by omega
    exact_mod_cast this
  have hlog := Real.log_le_log hpos hcap
  refine le_trans hlog (le_of_eq ?_)
  rw [Real.log_mul (ne_of_gt (globalDemandCap27_pos w b floor m)) (Real.exp_ne_zero _),
    Real.log_exp]

/--
The same bound with the demand exponent replaced by its paper form: the region's alpha entropy
minus the region rate of the grid data.  Only the second summand depends on the grid.
-/
theorem globalDemand_log_regionRate_cap27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (floor : ℕ) (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    Real.log (globalDemand g b floor m xi r) ≤
      Real.log (globalDemandCap27 w b floor m) +
        ((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) -
            globalRegionRate (globalExactGridData27 g xi) r) := by
  have h := globalDemand_log_cap27 g hg hb floor xi hxi r hn
  have hid := globalRegionRate_eq_entropy_sub_demand27 g xi r
  have hbits : globalDemandBits27 g xi r =
      entropy ((g.alpha r).probR) - globalRegionRate (globalExactGridData27 g xi) r := by
    rw [hid]
    ring
  rwa [hbits] at h

/-- The region's alpha entropy is capped by the shape alphabet, uniformly in the grid. -/
theorem globalAlphaEntropy_le_logb_card27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6) :
    entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR) ≤
      Real.log (Fintype.card (Shape w) : ℝ) / Real.log 2 :=
  entropy_add_penalty_le_logb_card27 (g.alpha r).probR
    ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩

end
end OmegaBound.ADVXXZGeneral
end
