import OmegaBound.ADVXXZGeneralIterateStagesRecursion

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

/-- Total normalized source-copy pool for the global producer followed by every stage. -/
noncomputable def iterateFinalQ (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) (ε : ℚ) (m : ℕ) : ℕ :=
  iterateStageQThrough C hC hpool (C.top + 1) ε m *
    (iterateGlobalData C hC).Q (iterateTolerance C.top ε) m

/-- Total retained-copy count for the global producer followed by every stage. -/
noncomputable def iterateFinalV (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) (ε : ℚ) (m : ℕ) : ℕ :=
  (iterateGlobalData C hC).V (iterateTolerance C.top ε) m *
    iterateStageVThrough C hC hpool (C.top + 1) ε m

private theorem stages_through_two_trivial (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) (ε : ℚ) (m : ℕ) :
    iterateStageQThrough C hC hpool 2 ε m = 1 ∧
      iterateStageVThrough C hC hpool 2 ε m = 1 ∧
      iterateStageBoundaryThrough C 2 = [] := by
  simp [iterateStageQThrough, iterateStageVThrough, iterateStageBoundaryThrough]

set_option maxHeartbeats 1000000 in
-- The two certificate-height branches normalize dependent `Stage` witnesses and copy products.
/-- Integral global-to-terminal production after composing all finite certificate stages. -/
theorem iterate_all_stages_integral
    (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) :
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m → ∃ N : ℕ,
      PolyDegeneratesAt ℤ N
        (copiesZ (iterateFinalQ C hC hpool ε m)
          (topZ C.q C.width (outerN C m))).tensor
        (copiesZ (iterateFinalV C hC hpool ε m)
          (boundaryMatrixZ C.q (accumulatedBoundary27 C) m)).tensor := by
  intro ε hε
  let g := iterateGlobalData C hC
  obtain ⟨Mg, hMg⟩ := g.production (iterateTolerance C.top ε)
    (iterateTolerance_pos _ hε)
  by_cases htop : C.top = 1
  · refine ⟨Mg, fun m hm => ?_⟩
    obtain ⟨Ng, hg⟩ := hMg m hm
    have hw : ∀ a ∈ G C, a.2.1 = 1 := by
      intro a ha
      rw [globalInventory_width_for_iterate C a ha, hC.width_eq, htop]
      rfl
    have hb : boundaryOccurrences27 (G C) = G C :=
      width_one_inventory_boundary (G C) hw
    have hmatrix := boundary_matrix_restrict31 C.q 1 m
      (boundaryOccurrences27 (G C)) (iterateTolerance C.top ε)
      hC.q_pos (globalBoundary_admissible_for_iterate C hC)
      (iterateTolerance_nonnegative _ hε.le)
    rw [Nat.one_mul, hb] at hmatrix
    have hmatrixCopies := copiesZ_restricts_of_restricts
      (g.V (iterateTolerance C.top ε) m) hmatrix
    obtain ⟨N, hN⟩ := integral_polyDegeneratesAt_trans hg
      (polyDegeneratesAt_of_restricts hmatrixCopies)
    refine ⟨N, ?_⟩
    obtain ⟨hQ, hV, hB⟩ := stages_through_two_trivial C hC hpool ε m
    have hQ' : iterateStageQThrough C hC hpool (C.top + 1) ε m = 1 := by
      simpa [htop] using hQ
    have hV' : iterateStageVThrough C hC hpool (C.top + 1) ε m = 1 := by
      simpa [htop] using hV
    have hB' : iterateStageBoundaryThrough C (C.top + 1) = [] := by
      simpa [htop] using hB
    have hacc := global_append_stageBoundaryThrough_top C
    rw [hB', List.append_nil] at hacc
    rw [iterateFinalQ, iterateFinalV, hQ', hV', one_mul, mul_one, ← hacc, hb]
    simpa [g] using hN
  · have htoppos := hC.top_pos
    have htop2 : 2 ≤ C.top := by omega
    obtain ⟨Ms, hMs⟩ := iterate_constituent_stages_integral C hC hpool
      C.top htop2 (le_refl _) ε hε
    refine ⟨max Mg Ms, fun m hm => ?_⟩
    obtain ⟨Ng, hg⟩ := hMg m (le_trans (Nat.le_max_left _ _) hm)
    obtain ⟨Ns, hs⟩ := hMs m (le_trans (Nat.le_max_right _ _) hm)
    let l : Stage C.top := ⟨C.top, htop2, le_refl _⟩
    let B := boundaryMatrixZ C.q (boundaryOccurrences27 (G C)) m
    let Pl := inventoryTensorZ C.q (P C l) m (iterateTolerance C.top ε)
    let S := boundaryMatrixZ C.q (iterateStageBoundaryThrough C (C.top + 1)) m
    have hlink := top_link_boundary_reindex C hC l rfl m
      (iterateTolerance C.top ε)
      (globalInventory_nonnegative_for_iterate C)
      (globalInterior_integral_for_iterate C hC m)
      (parentInventory_integral_for_iterate C l m)
    have hmatrix := boundary_matrix_restrict31 C.q 1 m
      (boundaryOccurrences27 (G C)) (iterateTolerance C.top ε)
      hC.q_pos (globalBoundary_admissible_for_iterate C hC)
      (iterateTolerance_nonnegative _ hε.le)
    rw [Nat.one_mul] at hmatrix
    have hPmatrix : Restricts (tensorProd Pl.tensor B.tensor)
        (tensorProd Pl.tensor
          (inventoryTensorZ C.q (boundaryOccurrences27 (G C)) m
            (iterateTolerance C.top ε)).tensor) :=
      OmegaBound.Restricts.tensorProd_left hmatrix Pl.tensor
    have hcomm : Restricts (tensorProd B.tensor Pl.tensor)
        (tensorProd Pl.tensor B.tensor) := tensorProd_comm_le B.tensor Pl.tensor
    have hprefixRestriction : Restricts (tensorProdZ B Pl).tensor
        (inventoryTensorZ C.q (G C) m (iterateTolerance C.top ε)).tensor :=
      Tensor3.Restricts.trans hcomm (Tensor3.Restricts.trans hPmatrix hlink.1)
    have hprefixCopies := copiesZ_restricts_of_restricts
      (g.V (iterateTolerance C.top ε) m) hprefixRestriction
    obtain ⟨Np, hp⟩ := integral_polyDegeneratesAt_trans hg
      (polyDegeneratesAt_of_restricts hprefixCopies)
    have hs' : PolyDegeneratesAt ℤ Ns
        (copiesZ (iterateStageQThrough C hC hpool (C.top + 1) ε m) Pl).tensor
        (copiesZ (iterateStageVThrough C hC hpool (C.top + 1) ε m) S).tensor := by
      simpa [Pl, S, l] using hs
    obtain ⟨Na, ha⟩ := integral_pool_accounting
      (g.Q (iterateTolerance C.top ε) m)
      (g.V (iterateTolerance C.top ε) m)
      (iterateStageQThrough C hC hpool (C.top + 1) ε m)
      (iterateStageVThrough C hC hpool (C.top + 1) ε m)
      (topZ C.q C.width (outerN C m)) B Pl S ⟨Np, hp⟩ ⟨Ns, hs'⟩
    have happend := (boundaryMatrixZ_append_reindex C.q m
      (boundaryOccurrences27 (G C))
      (iterateStageBoundaryThrough C (C.top + 1))).2
    have happendCopies : Restricts
        (copiesZ (g.V (iterateTolerance C.top ε) m *
          iterateStageVThrough C hC hpool (C.top + 1) ε m)
          (boundaryMatrixZ C.q
            (boundaryOccurrences27 (G C) ++
              iterateStageBoundaryThrough C (C.top + 1)) m)).tensor
        (copiesZ (g.V (iterateTolerance C.top ε) m *
          iterateStageVThrough C hC hpool (C.top + 1) ε m)
          (tensorProdZ B S)).tensor :=
      copiesZ_restricts_of_restricts _ happend
    obtain ⟨N, hN⟩ := integral_polyDegeneratesAt_trans ha
      (polyDegeneratesAt_of_restricts happendCopies)
    refine ⟨N, ?_⟩
    rw [iterateFinalQ, iterateFinalV, ← global_append_stageBoundaryThrough_top]
    simpa [g] using hN

end
end OmegaBound.ADVXXZGeneral
end
