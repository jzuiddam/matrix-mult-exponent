import OmegaBound.ADVXXZGeneralCExact36Consumer
import OmegaBound.ADVXXZGeneralCExact33ProducerCount

set_option autoImplicit false
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The selection-count statement, proved as `constituent_grid_selection_count41`.  It differs
from `S_constituent_grid_broken_supply33` only in asking for the multiplicative selected-label
count in each nonempty region; the supplied producer assembly and the regional quotient
lemma perform all structural and zero-population work. -/
def S_constituent_grid_selection_count36 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ ConstituentFiniteLoss29 p b ell ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ h : ConstituentFullGrid27 d m ε,
        (∀ x y z, (constituentGridTensorZ27 q d m h.val).tensor x y z = 0) ∨
        ∃ P : ConstituentGridProduction29 q d hd ε m h.val,
          ∀ r : Fin 6,
            (stagePopulationAt q (constituentGridParent27 d hd m h.val)
              (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 →
            (constituentRegionalReserve33 q P r : ℝ) *
                Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
                  - delta ε * (cLength p b m : ℝ) - ell ε m)
              ≤ ((P.selected r).card : ℝ)

theorem constituent_grid_broken_supply36_of_selection_count
    (hsel : S_constituent_grid_selection_count36) :
    S_constituent_grid_broken_supply33 := by
  intro q w s b hq hw p d hd hb
  obtain ⟨delta, ell, hdelta, hell, hcount⟩ :=
    hsel q w s b hq hw p d hd hb
  refine ⟨delta, ell, hdelta, hell, ?_⟩
  intro ε hε
  obtain ⟨Mcount, hMcount⟩ := hcount ε hε
  obtain ⟨Mmass, hMmass⟩ :=
    mass_zero_of_population_zero_eventually q p d b hb.1
  refine ⟨max Mcount Mmass, fun m hm h => ?_⟩
  rcases hMcount m (le_trans (Nat.le_max_left _ _) hm) h with hzero | ⟨P, hPcount⟩
  · exact Or.inl hzero
  · right
    refine ⟨P, constituent_grid_broken_supply_regional33 q P delta ell hdelta
      hell.1.1 ?_ hPcount⟩
    intro r hz
    exact hMmass m (le_trans (Nat.le_max_right _ _) hm) r hz

#print axioms constituent_grid_broken_supply36_of_selection_count

end OmegaBound.ADVXXZGeneral
