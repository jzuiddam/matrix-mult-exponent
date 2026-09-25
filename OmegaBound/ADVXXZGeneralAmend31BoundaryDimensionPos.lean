import OmegaBound.ADVXXZGeneralAmend31BoundaryWordsCard
import OmegaBound.ADVXXZEpsCnt

set_option autoImplicit false
set_option maxRecDepth 10000

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem rat_floor_toNat_nat31_pos (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem boundary_count_cast31_pos (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) (σ : Chunk a.2.1) :
    (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
  have ha := hI a (by simp)
  rcases ha with ⟨_hma, _hbeta_nonneg, _hsum, _hsupport, _hzero, _hreflect,
    ⟨K, hK⟩, hbeta⟩
  rcases hbeta W σ with ⟨C, hC⟩
  have hkmul : a.1 * (((b*m : ℕ) : ℚ)) = ((K*m : ℕ) : ℚ) := by
    calc
      a.1 * (((b*m : ℕ) : ℚ)) = ((b : ℚ) * a.1) * (m : ℚ) := by
        push_cast
        ring
      _ = (K : ℚ) * (m : ℚ) := by rw [hK]
      _ = ((K*m : ℕ) : ℚ) := by push_cast; rfl
  have hk : (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = K*m := by
    rw [hkmul]
    exact rat_floor_toNat_nat31_pos _
  have hcmul : (((K*m : ℕ) : ℚ) * a.2.2.2 W σ) = ((C*m : ℕ) : ℚ) := by
    calc
      ((K*m : ℕ) : ℚ) * a.2.2.2 W σ =
          (m : ℚ) * ((b : ℚ) * a.1 * a.2.2.2 W σ) := by
            push_cast
            rw [hK]
            ring
      _ = (m : ℚ) * (C : ℚ) := by rw [hC]
      _ = ((C*m : ℕ) : ℚ) := by push_cast; ring
  unfold boundaryTypeCounts31
  rw [hk, hcmul, rat_floor_toNat_nat31_pos]

private theorem boundary_type_counts_sum31 (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) :
    ∑ σ, boundaryTypeCounts31 a (b*m) W σ =
      (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat := by
  have ha := hI a (by simp)
  rcases ha with ⟨_hma, _hbeta_nonneg, hsum, _hsupport, _hzero, _hreflect,
    _hmass, _hbeta_integral⟩
  have hq : ((∑ σ, boundaryTypeCounts31 a (b*m) W σ : ℕ) : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by
    rw [Nat.cast_sum]
    calc
      ∑ σ : Chunk a.2.1, (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
          ∑ σ : Chunk a.2.1,
            ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
        apply Finset.sum_congr rfl
        intro σ _hσ
        exact boundary_count_cast31_pos b m a W hI σ
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) *
          ∑ σ : Chunk a.2.1, a.2.2.2 W σ := by rw [Finset.mul_sum]
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by rw [hsum, mul_one]
  exact_mod_cast hq

private theorem boundary_words_pos31 (q b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b) :
    1 ≤ (boundaryWords31 q a (b*m) W).card := by
  have hsum := boundary_type_counts_sum31 b m a W hI
  obtain ⟨s, hs⟩ := ADVXXZEps.exists_typeCnt_eq
    (boundaryTypeCounts31 a (b*m) W) hsum
  have hclass : 0 < Fintype.card
      {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
        ∀ σ, typeCnt x σ = boundaryTypeCounts31 a (b*m) W σ} :=
    Fintype.card_pos_iff.mpr ⟨⟨s, hs⟩⟩
  rw [boundary_words_card31 q b m a W hI]
  exact Nat.mul_pos hclass (Nat.pow_pos hq)

/-- Paper clause: `P/constituent.tex:39`. -/
theorem boundary_dimension_pos31 (q b m : ℕ) (I : Inventory) (W : Side)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
  1 ≤ boundaryDimension31 q I (b*m) W := by
  induction I with
  | nil => rfl
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have htail : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hih := ih htail
      simp only [boundaryDimension31, List.map_cons, List.prod_cons]
      split_ifs with hactive
      · exact Nat.mul_pos (boundary_words_pos31 q b m a (boundaryReadingSide31 W) hq ha) hih
      · simpa using hih

end
end OmegaBound.ADVXXZGeneral
end
