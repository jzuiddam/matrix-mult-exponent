import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceFractions

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

abbrev ReleasedOrdinaryChildFiber (t : Fin 126) (r : Fin 6) :=
  {u : ChildShape releasedParent t //
    0 < releasedConstituentSpec.outBase
      (⟨t, (r, u)⟩ : ConstituentTerm releasedParent) ∧
    0 < coord .X u.1 ∧ 0 < coord .Y u.1 ∧ 0 < coord .Z u.1}

def releasedOrdinaryOccurrenceFiberEquiv :
    ReleasedOrdinaryOccurrence ≃
      (t : Fin 126) × (r : Fin 6) × ReleasedOrdinaryChildFiber t r where
  toFun x := ⟨x.1.1, x.1.2.1, ⟨x.1.2.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1, x.2.2.1⟩, x.2.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def ReleasedOrdinaryCensusBlock (b : Fin 6) : Prop :=
  (∑ j : Fin 21,
      (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv (b, j)).val).length) = 153 ∧
  (∑ j : Fin 21, ∑ r : Fin 6,
      Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv (b, j)) r)) = 184

def ReleasedOrdinaryCensusSlice (b r : Fin 6) (n : Nat) : Prop :=
  (∑ j : Fin 21,
    Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv (b, j)) r)) = n

def ReleasedOrdinaryCensusHeadSlice (b r : Fin 6) (n : Nat) : Prop :=
  (∑ j : Fin 21,
      (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv (b, j)).val).length) = 153 ∧
  ReleasedOrdinaryCensusSlice b r n

noncomputable instance instDecidableReleasedOrdinaryCensusBlock (b : Fin 6) :
    Decidable (ReleasedOrdinaryCensusBlock b) := by
  unfold ReleasedOrdinaryCensusBlock ReleasedOrdinaryChildFiber
  infer_instance

noncomputable instance instDecidableReleasedOrdinaryCensusSlice (b r : Fin 6) (n : Nat) :
    Decidable (ReleasedOrdinaryCensusSlice b r n) := by
  unfold ReleasedOrdinaryCensusSlice ReleasedOrdinaryChildFiber
  infer_instance

noncomputable instance instDecidableReleasedOrdinaryCensusHeadSlice (b r : Fin 6) (n : Nat) :
    Decidable (ReleasedOrdinaryCensusHeadSlice b r n) := by
  unfold ReleasedOrdinaryCensusHeadSlice
  infer_instance

theorem sum_fin_six (f : Fin 6 → ℕ) :
    (∑ r, f r) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem releasedOrdinaryCensusBlock_of_slices (b : Fin 6)
    (n0 n1 n2 n3 n4 n5 : ℕ)
    (h0 : ReleasedOrdinaryCensusHeadSlice b 0 n0)
    (h1 : ReleasedOrdinaryCensusSlice b 1 n1)
    (h2 : ReleasedOrdinaryCensusSlice b 2 n2)
    (h3 : ReleasedOrdinaryCensusSlice b 3 n3)
    (h4 : ReleasedOrdinaryCensusSlice b 4 n4)
    (h5 : ReleasedOrdinaryCensusSlice b 5 n5)
    (hsum : n0 + n1 + n2 + n3 + n4 + n5 = 184) :
    ReleasedOrdinaryCensusBlock b := by
  unfold ReleasedOrdinaryCensusBlock
  constructor
  · exact h0.1
  · rw [Finset.sum_comm, sum_fin_six]
    have h0' := h0.2
    unfold ReleasedOrdinaryCensusSlice at h0' h1 h2 h3 h4 h5
    rw [h0', h1, h2, h3, h4, h5]
    exact hsum

end OmegaBound.ADVXXZGeneral
