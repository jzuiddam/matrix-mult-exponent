import OmegaBound.ADVXXZGeneralGlobalExactDemandBound

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/--
The grid-uniform polynomial cap on the global natural demand.

It depends only on the width, the integral scale, the chosen floor and the stage `m`; it does
not mention the exact grid `ξ`, so any threshold built from it is chosen before `ξ`.
-/
noncomputable def globalDemandCap27 (w b floor m : ℕ) : ℝ :=
  ((max floor (2 * w + 3) : ℕ) : ℝ) + 1
    + 8 * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1)))
    + 160 * ((w * (b * m) : ℕ) : ℝ) * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1)))

theorem globalDemandCap27_nonneg (w b floor m : ℕ) :
    0 ≤ globalDemandCap27 w b floor m := by
  unfold globalDemandCap27
  positivity

private theorem gdc_ceil_branch27 (Nw : ℕ) (x c : ℝ) (hx : 0 ≤ x) (hxc : x ≤ c) :
    (((if Nw = 0 then 0 else ⌈x⌉₊ : ℕ)) : ℝ) ≤ c + 1 := by
  have hc : 0 ≤ c := hx.trans hxc
  by_cases h : Nw = 0
  · rw [if_pos h]
    simpa using by linarith
  · rw [if_neg h]
    have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    linarith

private theorem gdc_cast_max_le {a b : ℕ} {c : ℝ} (ha : (a : ℝ) ≤ c) (hb : (b : ℝ) ≤ c) :
    ((max a b : ℕ) : ℝ) ≤ c := by
  rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption

private theorem gdc_globalPcomp_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    0 ≤ globalPcomp g n xi r which beta := by
  classical
  unfold globalPcomp
  dsimp only
  split_ifs <;> positivity

/-- The compatibility maximum is never negative, including the empty-law branch. -/
theorem globalPcompMax_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    0 ≤ globalPcompMax g n xi r which := by
  classical
  unfold globalPcompMax
  dsimp only
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g n xi r which)).image
    (globalPcomp g n xi r which)
  by_cases hv : values.Nonempty
  · rw [dif_pos hv]
    rcases Finset.mem_image.mp (Finset.max'_mem values hv) with ⟨beta, -, hbeta⟩
    rw [← hbeta]
    exact gdc_globalPcomp_nonneg27 g xi r which beta
  · rw [dif_neg hv]

set_option maxHeartbeats 1000000 in
-- The unfolded natural demand carries four branches with dependent coarse-image types.
/--
**Grid-uniform demand cap.**  The global natural demand of any occupied region of
any exact grid at scale `b*m` is at most a polynomial cap, chosen before the grid, times the
exponential of that region's paper demand exponent.
-/
theorem globalDemand_paper_cap27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (floor : ℕ) (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    (globalDemand g b floor m xi r : ℝ) ≤
      globalDemandCap27 w b floor m *
        Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          globalDemandBits27 g xi r) := by
  classical
  set P := globalPopulation g (b * m) xi r with hPdef
  let NX := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .X)).card
  let NY := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Y)).card
  let NZ := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Z)).card
  have hdem : globalDemand g b floor m xi r =
      max (max floor (2 * w + 3))
        (max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX))
          (max (if NY = 0 then 0 else Nat.ceil
                (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                  globalPcompMax g (b * m) xi r 0 / NY))
            (if NZ = 0 then 0 else Nat.ceil
                (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                  globalPcompMax g (b * m) xi r 1 / NZ)))) := by
    unfold globalDemand natural_demand
    dsimp only
  -- the exponential factor
  set D : ℝ := globalDemandBits27 g xi r with hDdef
  set N : ℝ := (P.n : ℝ) with hNdef
  have hD0 : 0 ≤ D := globalDemandBits_nonneg27 g xi r
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  set E : ℝ := Real.exp (N * Real.log 2 * D) with hEdef
  have hE1 : (1 : ℝ) ≤ E := by
    have h0 : (0 : ℝ) ≤ N * Real.log 2 * D :=
      mul_nonneg (mul_nonneg hN0 hlog2) hD0
    have h := Real.exp_le_exp.mpr h0
    rw [Real.exp_zero] at h
    exact h
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE1
  -- population never exceeds the whole lattice
  have hNle : N ≤ ((b * m : ℕ) : ℝ) := by
    rw [hNdef]
    exact_mod_cast globalPopulation_n_le27 g xi hb r
  -- the three paper branch exponents lie below the demand exponent
  have hxbits : entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR) -
      entropy (marginal (g.alpha r).probR (g.perm r .X)) ≤ D := by
    rw [hDdef]
    unfold globalDemandBits27
    dsimp only
    exact le_max_left _ _
  have hybits : entropy ((g.alpha r).probR) +
      globalEta (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
      entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y)) ≤ D := by
    rw [hDdef]
    unfold globalDemandBits27
    dsimp only
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hzbits : entropy ((g.alpha r).probR) +
      globalLambda (globalExactGridData27 g xi) r
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
      entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)) ≤ D := by
    rw [hDdef]
    unfold globalDemandBits27
    dsimp only
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the two polynomial type losses, uniformly in the grid
  set PX : ℝ := (((b * m : ℕ) : ℝ) + 1) ^
    (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) with hPXdef
  set PQ : ℝ := (((b * m : ℕ) : ℝ) + 1) ^
    (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) with hPQdef
  have hPX0 : (0 : ℝ) ≤ PX := by rw [hPXdef]; positivity
  have hPQ0 : (0 : ℝ) ≤ PQ := by rw [hPQdef]; positivity
  have hPXle : (N + 1) ^ (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) ≤ PX := by
    rw [hPXdef]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hPQle : (N + 1) ^ (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) ≤ PQ := by
    rw [hPQdef]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  -- the three ratio estimates, with the branch exponents replaced by the demand exponent
  have hxratio : (Fintype.card P.Label : ℝ) / (NX : ℝ) ≤ PX * E := by
    have h := globalDemand_x_ratio_bound27 g hg hb xi r hn
    refine le_trans h ?_
    refine mul_le_mul hPXle ?_ (Real.exp_pos _).le hPX0
    rw [hEdef]
    refine Real.exp_le_exp.mpr ?_
    have := mul_nonneg hN0 hlog2
    nlinarith
  have hyratio : (P.target.card : ℝ) * globalPcompMax g (b * m) xi r 0 / (NY : ℝ)
      ≤ PQ * E := by
    have h := globalDemand_target_pcomp_ratio_bound27 g hg hb xi hxi r hn 0
    simp only [GlobalBridge25.side, if_pos] at h
    refine le_trans h ?_
    refine mul_le_mul hPQle ?_ (Real.exp_pos _).le hPQ0
    rw [hEdef]
    refine Real.exp_le_exp.mpr ?_
    have := mul_nonneg hN0 hlog2
    nlinarith
  have hzratio : (P.target.card : ℝ) * globalPcompMax g (b * m) xi r 1 / (NZ : ℝ)
      ≤ PQ * E := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide +kernel
    have h := globalDemand_target_pcomp_ratio_bound27 g hg hb xi hxi r hn 1
    simp only [GlobalBridge25.side, h10, if_false] at h
    refine le_trans h ?_
    refine mul_le_mul hPQle ?_ (Real.exp_pos _).le hPQ0
    rw [hEdef]
    refine Real.exp_le_exp.mpr ?_
    have := mul_nonneg hN0 hlog2
    nlinarith
  -- cap comparisons
  have hcap0 : (0 : ℝ) ≤ globalDemandCap27 w b floor m := globalDemandCap27_nonneg _ _ _ _
  have hcapFloor : ((max floor (2 * w + 3) : ℕ) : ℝ) ≤ globalDemandCap27 w b floor m := by
    unfold globalDemandCap27
    have h8 : (0 : ℝ) ≤ 8 * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) := by positivity
    have h160 : (0 : ℝ) ≤ 160 * ((w * (b * m) : ℕ) : ℝ) * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) := by positivity
    linarith
  have hcapX : 8 * PX + 1 ≤ globalDemandCap27 w b floor m := by
    unfold globalDemandCap27
    rw [hPXdef]
    have hfl : (0 : ℝ) ≤ ((max floor (2 * w + 3) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h160 : (0 : ℝ) ≤ 160 * ((w * (b * m) : ℕ) : ℝ) * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) := by positivity
    linarith
  have hcapQ : ((80 * (w * (b * m)) : ℕ) : ℝ) * PQ + 1 ≤ globalDemandCap27 w b floor m := by
    unfold globalDemandCap27
    rw [hPQdef]
    have hfl : (0 : ℝ) ≤ ((max floor (2 * w + 3) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h8 : (0 : ℝ) ≤ 8 * (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) := by positivity
    have hQ0 : (0 : ℝ) ≤ (((b * m : ℕ) : ℝ) + 1) ^
        (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) := by positivity
    have hwbm : (0 : ℝ) ≤ ((w * (b * m) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcast : ((80 * (w * (b * m)) : ℕ) : ℝ) = 80 * ((w * (b * m) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast]
    nlinarith
  -- assemble (the abbreviations are made opaque so no tactic unfolds the population)
  clear_value PQ PX E N D P
  rw [hdem]
  refine gdc_cast_max_le ?_ (gdc_cast_max_le ?_ (gdc_cast_max_le ?_ ?_))
  · exact le_trans hcapFloor
      (le_mul_of_one_le_right hcap0 hE1)
  · refine le_trans (gdc_ceil_branch27 NX _ (8 * PX * E) (by positivity) ?_) ?_
    · rw [mul_div_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left hxratio (by norm_num)
    · have hprod : (8 * PX + 1) * E ≤ globalDemandCap27 w b floor m * E :=
        mul_le_mul_of_nonneg_right hcapX hE0
      have hexp : (8 * PX + 1) * E = 8 * PX * E + E := by ring
      have hPXE : (0 : ℝ) ≤ 8 * PX * E :=
        mul_nonneg (mul_nonneg (by norm_num) hPX0) hE0
      linarith
  · have hp0 : (0 : ℝ) ≤ globalPcompMax g (b * m) xi r 0 :=
      globalPcompMax_nonneg27 g xi r 0
    have hnum : (0 : ℝ) ≤ ((80 * (w * (b * m)) : ℕ) : ℝ) * (P.target.card : ℝ) *
        globalPcompMax g (b * m) xi r 0 :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp0
    refine le_trans (gdc_ceil_branch27 NY _
      (((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E)) (div_nonneg hnum (Nat.cast_nonneg _)) ?_) ?_
    · rw [mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hyratio (Nat.cast_nonneg _)
    · have hprod : (((80 * (w * (b * m)) : ℕ) : ℝ) * PQ + 1) * E ≤
          globalDemandCap27 w b floor m * E :=
        mul_le_mul_of_nonneg_right hcapQ hE0
      have hexp : (((80 * (w * (b * m)) : ℕ) : ℝ) * PQ + 1) * E =
          ((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E) + E := by ring
      have hQE : (0 : ℝ) ≤ ((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hPQ0 hE0)
      linarith
  · have hp0 : (0 : ℝ) ≤ globalPcompMax g (b * m) xi r 1 :=
      globalPcompMax_nonneg27 g xi r 1
    have hnum : (0 : ℝ) ≤ ((80 * (w * (b * m)) : ℕ) : ℝ) * (P.target.card : ℝ) *
        globalPcompMax g (b * m) xi r 1 :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp0
    refine le_trans (gdc_ceil_branch27 NZ _
      (((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E)) (div_nonneg hnum (Nat.cast_nonneg _)) ?_) ?_
    · rw [mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hzratio (Nat.cast_nonneg _)
    · have hprod : (((80 * (w * (b * m)) : ℕ) : ℝ) * PQ + 1) * E ≤
          globalDemandCap27 w b floor m * E :=
        mul_le_mul_of_nonneg_right hcapQ hE0
      have hexp : (((80 * (w * (b * m)) : ℕ) : ℝ) * PQ + 1) * E =
          ((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E) + E := by ring
      have hQE : (0 : ℝ) ≤ ((80 * (w * (b * m)) : ℕ) : ℝ) * (PQ * E) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hPQ0 hE0)
      linarith

end
end OmegaBound.ADVXXZGeneral
end
