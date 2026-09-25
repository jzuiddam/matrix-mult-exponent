import OmegaBound.ADVXXZGeneralCExact33ProducerAssembly
import OmegaBound.ADVXXZGeneralCExact33Supply

set_option autoImplicit false

/-!
# From a selected-count bound to the broken-supply statement

Given any inhabitant `P` of the production record `ConstituentGridProduction29` and the
per-region multiplicative count

  `reserve_r · exp(log 2 · E_r · b·m − δ ε · cLength − ell ε m) ≤ #(P.selected r)`,

the regional conclusion of `S_constituent_grid_broken_supply33` follows verbatim.  The
zero-population branch is discharged by the mass guard, which holds beyond one threshold chosen
before `m` and before the grid (`mass_zero_of_population_zero_eventually`).

The count itself is proved in `ADVXXZGeneralCExact41SelectionCount`.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Beyond one threshold, chosen before `m`, an empty region population
forces zero rational regional mass.  This is the converse half of the guard bridge, and it is
what turns the display's `if N = 0 then 1` branch into the zero-mass branch already proved. -/
theorem mass_zero_of_population_zero_eventually (q : ℕ) {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) :
    ∃ M1 : ℕ, ∀ m : ℕ, M1 ≤ m → ∀ r : Fin 6,
      (stagePopulationAt q p d b m r).n = 0 →
        (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 := by
  classical
  have hex : ∀ r : Fin 6, ∃ Mr : ℕ, ∀ m : ℕ, Mr ≤ m →
      ((stagePopulationAt q p d b m r).n = 0 →
        (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0) := by
    intro r
    by_cases hm0 : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0
    · exact ⟨0, fun m _ _ => hm0⟩
    · have hnn : (0:ℚ) ≤ ∑ t, (p.baseN t : ℚ) * (d.A t).prob r :=
        Finset.sum_nonneg fun t _ => mul_nonneg (by positivity) ((d.A t).prob_nonneg r)
      have hpos : 0 < ∑ t, (p.baseN t : ℚ) * (d.A t).prob r :=
        lt_of_le_of_ne hnn (Ne.symm hm0)
      obtain ⟨Mr, hMr⟩ := stagePopulation_n_pos_eventually q p d b hb r hpos
      exact ⟨Mr, fun m hm hz => absurd hz (hMr m hm).ne'⟩
  choose Mf hMf using hex
  refine ⟨Finset.univ.sup Mf, fun m hm r => ?_⟩
  exact hMf r m (le_trans (Finset.le_sup (Finset.mem_univ r)) hm)

/-- The regional conclusion of `S_constituent_grid_broken_supply33`, from
the per-region multiplicative count and the mass guard. -/
theorem constituent_grid_broken_supply_regional33 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hdelta : VanishesWithTolerance delta) (hell : ∀ ε m, 0 ≤ ell ε m)
    (hmass : ∀ r : Fin 6, (stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r).n = 0 →
      (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0)
    (hcount : ∀ r : Fin 6, (stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r).n ≠ 0 →
      (constituentRegionalReserve33 q P r : ℝ) *
        Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
          - delta ε * (cLength p b m : ℝ) - ell ε m)
        ≤ ((P.selected r).card : ℝ)) :
    ∀ r : Fin 6,
      Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
        - delta ε * (cLength p b m : ℝ) - ell ε m) ≤
      (if (stagePopulationAt q (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) b m r).n = 0 then 1 else
        ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)) := by
  intro r
  refine constituent_regional_quotient33 q P r _ (fun hz => ?_) (hcount r)
  exact grid_broken_exponent_nonpos_of_mass_zero p d b r delta ell hdelta hell
    (hmass r hz) ε m

end
end OmegaBound.ADVXXZGeneral
end
