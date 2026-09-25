import OmegaBound.ADVXXZGeneralCExact33Defs
import OmegaBound.ADVXXZGeneralAmend25Ordered

set_option autoImplicit false

/-!
# The population arithmetic the reserve estimates need

Two facts about `stagePopulationAt`, both required by the constituent reserve estimates:

* `stagePopulation_n_le` : the region population is at most `2 * cLength p b m`.  This is what
  makes `constituent_repair_pool_sublinear33` true at all.
* `gridPopulation_n_eq` : the grid parent/spec have the same region population as the original
  parent/spec (the grid only perturbs `beta`).
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

/-- The stage population's size is `2 * ∑_t (parent count)`: two positions (a shape and its
complement) for every level-1 index position. -/
theorem stagePopulation_n_eq (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    (stagePopulationAt q p d b m r).n
      = ∑ t : Fin s, stageParentCount b m p d r t * 2 := by
  classical
  have h1 : (stagePopulationAt q p d b m r).n
      = @Fintype.card (StagePos b m p d r) (Fintype.ofFinite _) := rfl
  have h2 : @Fintype.card (StagePos b m p d r) (Fintype.ofFinite _)
      = @Fintype.card (StagePos b m p d r) inferInstance :=
    @Fintype.card_congr _ _ (Fintype.ofFinite _) inferInstance (Equiv.refl _)
  rw [h1, h2]
  simp [StagePos, Fintype.card_sigma]

/-- Each parent count is at most `b*m*n_t`: the floors of a sub-probability mass. -/
theorem stageParentCount_le {w s : ℕ} (b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (t : Fin s) :
    stageParentCount b m p d r t ≤ b * m * p.baseN t := by
  classical
  have hA1 : (d.A t).prob r ≤ 1 := by
    rw [← (d.A t).sum_prob]
    exact Finset.single_le_sum (fun i _ => (d.A t).prob_nonneg i) (Finset.mem_univ r)
  have hcast : ((stageParentCount b m p d r t : ℕ) : ℚ) ≤ ((b * m * p.baseN t : ℕ) : ℚ) := by
    have hstep : ∀ u : ChildShape p t,
        ((stageAlphaCount b m p d r t u : ℕ) : ℚ) ≤
          ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u := by
      intro u
      have hnn : (0:ℚ) ≤ ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob u :=
        mul_nonneg (mul_nonneg (by positivity) ((d.A t).prob_nonneg r))
          ((d.alpha t r).prob_nonneg u)
      have hfl : stageAlphaCount b m p d r t u
          = ⌊((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u⌋₊ :=
        Int.floor_toNat
          (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u)
      rw [hfl]
      exact Nat.floor_le hnn
    calc ((stageParentCount b m p d r t : ℕ) : ℚ)
        = ∑ u : ChildShape p t, ((stageAlphaCount b m p d r t u : ℕ) : ℚ) := by
          rw [stageParentCount]; push_cast; ring
      _ ≤ ∑ u : ChildShape p t,
            ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u :=
          Finset.sum_le_sum (fun u _ => hstep u)
      _ = ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r := by
          rw [← Finset.mul_sum, (d.alpha t r).sum_prob, mul_one]
      _ ≤ ((b * m * p.baseN t : ℕ) : ℚ) :=
          mul_le_of_le_one_right (by positivity) hA1
  exact_mod_cast hcast

/-- **The population bound.**  `N_r ≤ 2 * cLength p b m` for every region. -/
theorem stagePopulation_n_le (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    (stagePopulationAt q p d b m r).n ≤ 2 * cLength p b m := by
  classical
  rw [stagePopulation_n_eq]
  calc (∑ t : Fin s, stageParentCount b m p d r t * 2)
      ≤ ∑ t : Fin s, (b * m * p.baseN t) * 2 :=
        Finset.sum_le_sum (fun t _ =>
          Nat.mul_le_mul_right 2 (stageParentCount_le b m p d r t))
    _ = 2 * cLength p b m := by
        simp only [cLength, constituentBaseTotal, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring)

/-- The grid parent and grid spec have the same region population as the original data: the
grid perturbs only `beta`, and `stagePopulationAt` reads only `baseN`, `A` and `alpha`. -/
theorem gridPopulation_n_eq (q : ℕ) {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (h : ConstituentExactGrid27 d m) (r : Fin 6) :
    (stagePopulationAt q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b m r).n
      = (stagePopulationAt q p d b m r).n := rfl

end
end OmegaBound.ADVXXZGeneral
end
