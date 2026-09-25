import OmegaBound.ADVXXZGeneralIterateStagesGlobal
import OmegaBound.ADVXXZGeneralIterateStagesRates

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Concrete normalized data selected from the integral global positive theorem. -/
structure IterateGlobalData (C : Certificate) where
  Q : ℚ → ℕ → ℕ
  V : ℚ → ℕ → ℕ
  Q_one : ∀ ε m, 1 ≤ Q ε m
  Q_sublinear : ∀ ε, 0 < ε →
    Sublinear (outerN C) (fun m => Real.log (Q ε m : ℝ))
  V_lowerRate : LowerRate (outerN C) V (gRate C.global)
  production : ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m →
    ∃ N : ℕ, PolyDegeneratesAt ℤ N
      (copiesZ (Q ε m) (topZ C.q C.width (outerN C m))).tensor
      (copiesZ (V ε m) (inventoryTensorZ C.q (G C) m ε)).tensor

/-- The reconstructed integral global producer supplies normalized data for iteration. -/
theorem iterateGlobalData_nonempty (C : Certificate) (hC : AdmissibleAt C) :
    Nonempty (IterateGlobalData C) := by
  classical
  obtain ⟨Q₀, V, delta, ell, hdelta, hell, hcopy, hsub, hprod⟩ :=
    global_positive_integral_for_iterate C.q C.width (C.D ^ 4) hC.q_pos
      (by rw [hC.width_eq]; simp [wid]) C.global hC.global_ok hC.lattice.1
  let Q : ℚ → ℕ → ℕ := fun ε m => positiveCopyPool (Q₀ ε) m
  refine ⟨
    { Q := Q
      V := V
      Q_one := fun ε m => positiveCopyPool_one_le (Q₀ ε) m
      Q_sublinear := ?_
      V_lowerRate := ?_
      production := ?_ }⟩
  · intro ε hε
    have hn := positiveCopyPool_sublinear (fun m => C.D ^ 4 * m) (Q₀ ε) (hsub ε hε)
    simpa only [outerN] using hn
  · have hn := copyBound_vanishing_loss_lowerRate
      (fun m => C.D ^ 4 * m) (gRate C.global) V delta ell hdelta hell hcopy
    simpa only [outerN] using hn
  · intro ε hε
    obtain ⟨M, hM⟩ := hprod ε hε
    refine ⟨M, fun m hm => ?_⟩
    obtain ⟨hQ₀, -, N, hN⟩ := hM m hm
    have htarget : Restricts
        (copiesZ (V ε m) (inventoryTensorZ C.q (G C) m ε)).tensor
        (copiesZ (V ε m) (globalOutputZ C.q C.global (outerN C m) ε)).tensor :=
      copiesZ_restricts_of_restricts _
        (ordinaryTensorTransport_restricts (globalOutputZ_G_transport C m ε))
    obtain ⟨N₁, h₁⟩ := integral_polyDegeneratesAt_trans hN
      (polyDegeneratesAt_of_restricts htarget)
    refine ⟨N₁, ?_⟩
    change PolyDegeneratesAt ℤ N₁
      (copiesZ (positiveCopyPool (Q₀ ε) m)
        (topZ C.q C.width (outerN C m))).tensor _
    rw [positiveCopyPool_eq_of_one_le (Q₀ ε) hQ₀]
    exact h₁

/-- Select the normalized integral global producer. -/
noncomputable def iterateGlobalData (C : Certificate) (hC : AdmissibleAt C) :
    IterateGlobalData C :=
  Classical.choice (iterateGlobalData_nonempty C hC)

end
end OmegaBound.ADVXXZGeneral
end
