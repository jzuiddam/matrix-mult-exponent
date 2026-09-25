import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorRetainedRate
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalNextLinkBase

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- A child inventory's atom sum is the finite sum over the constituent addresses. -/
theorem childInventory_map_sum32 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) {M : Type*} [AddCommMonoid M] (g : ℚ × AtomKey → M) :
    ((childInventory d).map g).sum =
      ∑ x : ConstituentTerm p, g ((d.outBase x : ℚ),
        ⟨w, x.2.2.1, fun W σ => (d.betaChild W x.1 x.2.1 x.2.2).prob σ⟩) := by
  rw [← Equiv.sum_comp (Fintype.equivFin (ConstituentTerm p)).symm
    (fun x : ConstituentTerm p => g ((d.outBase x : ℚ),
      ⟨w, x.2.2.1, fun W σ => (d.betaChild W x.1 x.2.1 x.2.2).prob σ⟩)),
    Fin.sum_univ_def]
  unfold childInventory
  rw [List.map_map]
  rfl

/-- The inventory rate of any released ordinary stage, as a finite address sum. -/
theorem ordinary_stage_inventory_rate32 (W : Side)
    (l : Stage releasedOrdinaryCertificatePhysical.top)
    (st : Step (wid (l.val - 1)))
    (hs : releasedOrdinaryCertificatePhysical.stage l = some st) :
    ordinaryInventoryRate 5 W (QAt releasedOrdinaryCertificatePhysical l) =
      ∑ x : ConstituentTerm st.input, ordinaryAtomRate 5 W
        ((st.data.outBase x : ℚ),
          ⟨wid (l.val - 1), x.2.2.1,
            fun V σ => (st.data.betaChild V x.1 x.2.1 x.2.2).prob σ⟩) := by
  rw [ordinaryInventoryRate, QAt, hs]
  exact childInventory_map_sum32 st.data (ordinaryAtomRate 5 W)

theorem ordinary_stage3_eq32 :
    releasedOrdinaryCertificatePhysical.stage ordinaryLevel3 = some releasedOrdinaryStep3 := by
  simp [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage, ordinaryLevel3]

theorem ordinary_stage2_eq32 :
    releasedOrdinaryCertificatePhysical.stage ordinaryLevel2 = some releasedOrdinaryStep2 := by
  simp [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage, ordinaryLevel2]

/-- An inventory atom whose shape has all three coordinates positive is inactive for
every direction: the `Q3` boundary census never sees an interior level-two node. -/
theorem ordinary_atom_rate_interior_zero32 (W : Side) (a : ℚ × AtomKey)
    (hx : 0 < coord .X a.2.2.1) (hy : 0 < coord .Y a.2.2.1) (hz : 0 < coord .Z a.2.2.1) :
    ordinaryAtomRate 5 W a = 0 := by
  unfold ordinaryAtomRate
  cases W
  · exact if_neg (fun h => absurd h.1 (by omega))
  · exact if_neg (fun h => absurd h.1 (by omega))
  · exact if_neg (fun h => absurd h.1 (by omega))

end OmegaBound.ADVXXZGeneral
end
