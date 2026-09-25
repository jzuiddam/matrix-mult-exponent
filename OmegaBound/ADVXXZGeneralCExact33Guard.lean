import OmegaBound.ADVXXZGeneralCExact33Population

set_option autoImplicit false

/-!
# Bridging the two zero-guards

`RegionalCopyBound33` guards on the RATIONAL region mass
`∑ t, n_t · A_{t,r} = 0`; `constituentRegionalReserve33`, `constituentRepairPool33` and
`S_constituent_grid_broken_supply33` guard on the NATURAL population `N_r = 0`.  These are different
predicates; the two lemmas here bridge them,
the second only eventually in `m`, which is all the statements' `∃ M, ∀ m ≥ M` allows and needs.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
open StageCandidateRaw
noncomputable section

/-- Zero rational mass forces an empty population, at EVERY scale. -/
theorem stagePopulation_n_eq_zero_of_mass_zero (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6)
    (hmass : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0) :
    (stagePopulationAt q p d b m r).n = 0 := by
  have hterm : ∀ t : Fin s, (d.A t).prob r = 0 := by
    intro t
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin s)),
        0 ≤ (p.baseN i : ℚ) * (d.A i).prob r :=
      fun i _ => mul_nonneg (by positivity) ((d.A i).prob_nonneg r)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hmass t (Finset.mem_univ t)
    have hb0 : (0:ℚ) < (p.baseN t : ℚ) := by exact_mod_cast p.baseN_pos t
    rcases mul_eq_zero.mp h0 with hcase | hcase
    · linarith
    · exact hcase
  rw [stagePopulation_n_eq]
  refine Finset.sum_eq_zero (fun t _ => ?_)
  have hpc : stageParentCount b m p d r t = 0 := by
    unfold stageParentCount
    refine Finset.sum_eq_zero (fun u _ => ?_)
    have hz : ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u = 0 := by
      rw [hterm t]; ring
    have hfl : stageAlphaCount b m p d r t u
        = ⌊((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u⌋₊ :=
      Int.floor_toNat
        (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)
    rw [hfl, hz, Nat.floor_zero]
  rw [hpc, Nat.zero_mul]

/-- Positive rational mass forces a nonempty population from some scale on. -/
theorem stagePopulation_n_pos_eventually (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6)
    (hmass : 0 < ∑ t, (p.baseN t : ℚ) * (d.A t).prob r) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < (stagePopulationAt q p d b m r).n := by
  obtain ⟨t, ht⟩ : ∃ t : Fin s, 0 < (p.baseN t : ℚ) * (d.A t).prob r := by
    by_contra hcon
    push_neg at hcon
    have hle : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) ≤ 0 :=
      Finset.sum_nonpos (fun t _ => hcon t)
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ChildShape p t, 0 < (d.alpha t r).prob u := by
    by_contra hcon
    push_neg at hcon
    have hle : (∑ u, (d.alpha t r).prob u) ≤ 0 :=
      Finset.sum_nonpos (fun u _ => hcon u)
    rw [(d.alpha t r).sum_prob] at hle
    linarith
  have hbQ : (0:ℚ) < (b:ℚ) := by exact_mod_cast hb
  have hbc : (0:ℚ) < (b:ℚ) * ((p.baseN t : ℚ) * (d.A t).prob r * (d.alpha t r).prob u) :=
    mul_pos hbQ (mul_pos ht hu)
  obtain ⟨M, hM⟩ := exists_nat_gt
    (1/((b:ℚ) * ((p.baseN t : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)))
  refine ⟨M, fun m hm => ?_⟩
  have hmQ : (M:ℚ) ≤ (m:ℚ) := by exact_mod_cast hm
  have hkey : (1:ℚ) ≤ ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u := by
    have hEq : ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u
        = (m:ℚ) * ((b:ℚ) * ((p.baseN t : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)) := by
      push_cast; ring
    rw [hEq]
    have h2 : 1/((b:ℚ) * ((p.baseN t : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)) < (m:ℚ) :=
      lt_of_lt_of_le hM hmQ
    rw [div_lt_iff₀ hbc] at h2
    linarith
  have halpha : 1 ≤ stageAlphaCount b m p d r t u := by
    have hfl : stageAlphaCount b m p d r t u
        = ⌊((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u⌋₊ :=
      Int.floor_toNat
        (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)
    rw [hfl]
    exact Nat.le_floor (by exact_mod_cast hkey)
  have hparent : 1 ≤ stageParentCount b m p d r t := by
    unfold stageParentCount
    exact le_trans halpha
      (Finset.single_le_sum (f := fun v : ChildShape p t => stageAlphaCount b m p d r t v)
        (fun v _ => Nat.zero_le _) (Finset.mem_univ u))
  rw [stagePopulation_n_eq]
  refine lt_of_lt_of_le (show 0 < stageParentCount b m p d r t * 2 by omega) ?_
  exact Finset.single_le_sum
    (f := fun v : Fin s => stageParentCount b m p d r v * 2)
    (fun v _ => Nat.zero_le _) (Finset.mem_univ t)

end
end OmegaBound.ADVXXZGeneral
end
