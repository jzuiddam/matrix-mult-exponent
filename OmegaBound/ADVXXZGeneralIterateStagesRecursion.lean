import OmegaBound.ADVXXZGeneralIterateStagesFamilies
import OmegaBound.ADVXXZGeneralIterateInfraPool

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

private theorem stage_two_child_is_boundary (C : Certificate) (l : Stage C.top)
    (hl : l.val = 2) : boundaryOccurrences27 (QAt C l) = QAt C l := by
  apply width_one_inventory_boundary
  intro a ha
  rw [childInventory_width_for_iterate C l a ha, hl]
  rfl

set_option maxHeartbeats 1000000 in
-- The dependent strong induction carries changing inventory tensor index types.
/-- The finite constituent recursion, starting at a parent stage and retaining every physical
boundary occurrence in descending stage order. -/
theorem iterate_constituent_stages_integral
    (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) :
    ∀ (n : ℕ) (hn2 : 2 ≤ n) (hntop : n ≤ C.top), ∀ ε : ℚ, 0 < ε →
      ∃ M : ℕ, ∀ m, M ≤ m → ∃ N : ℕ, PolyDegeneratesAt ℤ N
        (copiesZ (iterateStageQThrough C hC hpool (n + 1) ε m)
          (inventoryTensorZ C.q (P C ⟨n, hn2, hntop⟩) m
            (iterateTolerance n ε))).tensor
        (copiesZ (iterateStageVThrough C hC hpool (n + 1) ε m)
          (boundaryMatrixZ C.q (iterateStageBoundaryThrough C (n + 1)) m)).tensor := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn2 hntop ε hε
    let l : Stage C.top := ⟨n, hn2, hntop⟩
    by_cases hn : n = 2
    · have hl : l.val = 2 := hn
      let d := iterateStageData C hC hpool l
      obtain ⟨M, hM⟩ := d.production (iterateTolerance (n - 1) ε)
        (iterateTolerance_pos _ hε)
      refine ⟨M, fun m hm => ?_⟩
      obtain ⟨N, hN⟩ := hM m hm
      rw [three_mul_iterateTolerance, show n - 1 + 1 = n by omega] at hN
      have hb : boundaryOccurrences27 (QAt C l) = QAt C l :=
        stage_two_child_is_boundary C l hl
      have hmatrix := boundary_matrix_restrict31 C.q 1 m
        (boundaryOccurrences27 (QAt C l)) (iterateTolerance (n - 1) ε)
        hC.q_pos (childBoundary_admissible_for_iterate C hC l)
        (iterateTolerance_nonnegative _ hε.le)
      rw [Nat.one_mul, hb] at hmatrix
      have hmatrixCopies := copiesZ_restricts_of_restricts (d.V
        (iterateTolerance (n - 1) ε) m) hmatrix
      obtain ⟨N', hN'⟩ := integral_polyDegeneratesAt_trans hN
        (polyDegeneratesAt_of_restricts hmatrixCopies)
      refine ⟨N', ?_⟩
      subst n
      have hvalid : 2 ≤ 2 ∧ 2 ≤ C.top := ⟨by omega, hntop⟩
      have hQeq : iterateStageQThrough C hC hpool 3 ε m =
          d.Q (iterateTolerance 1 ε) m := by
        rw [iterateStageQThrough]
        split <;> simp_all [iterateStageQThrough, l, d]
      have hVeq : iterateStageVThrough C hC hpool 3 ε m =
          d.V (iterateTolerance 1 ε) m := by
        rw [iterateStageVThrough]
        split <;> simp_all [iterateStageVThrough, l, d]
      have hBeq : iterateStageBoundaryThrough C 3 =
          boundaryOccurrences27 (QAt C l) := by
        rw [iterateStageBoundaryThrough]
        split <;> simp_all [iterateStageBoundaryThrough, l]
      rw [hQeq, hVeq, hBeq, hb]
      simpa [l, d] using hN'
    · have hn3 : 3 ≤ n := by omega
      have hpred2 : 2 ≤ n - 1 := by omega
      have hpredtop : n - 1 ≤ C.top := by omega
      have hpredlt : n - 1 < n := by omega
      let lo : Stage C.top := ⟨n - 1, hpred2, hpredtop⟩
      let d := iterateStageData C hC hpool l
      obtain ⟨Mc, hMc⟩ := d.production (iterateTolerance (n - 1) ε)
        (iterateTolerance_pos _ hε)
      obtain ⟨Mr, hMr⟩ := ih (n - 1) hpredlt hpred2 hpredtop ε hε
      refine ⟨max Mc Mr, fun m hm => ?_⟩
      obtain ⟨Nc, hc⟩ := hMc m (le_trans (Nat.le_max_left _ _) hm)
      rw [three_mul_iterateTolerance, show n - 1 + 1 = n by omega] at hc
      obtain ⟨Nr, hr⟩ := hMr m (le_trans (Nat.le_max_right _ _) hm)
      let B := boundaryMatrixZ C.q (boundaryOccurrences27 (QAt C l)) m
      let Pl := inventoryTensorZ C.q (P C lo) m (iterateTolerance (n - 1) ε)
      let S := boundaryMatrixZ C.q (iterateStageBoundaryThrough C n) m
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hr
      have hr' : PolyDegeneratesAt ℤ Nr
          (copiesZ (iterateStageQThrough C hC hpool n ε m) Pl).tensor
          (copiesZ (iterateStageVThrough C hC hpool n ε m) S).tensor := by
        simpa [Pl, S, lo] using hr
      have hlink := next_link_boundary_reindex C hC lo l (by
        dsimp [lo, l]
        omega) m
        (iterateTolerance (n - 1) ε)
        (childInventory_nonnegative_for_iterate C l)
        (childInterior_integral_for_iterate C l m)
        (parentInventory_integral_for_iterate C lo m)
      have hmatrix := boundary_matrix_restrict31 C.q 1 m
        (boundaryOccurrences27 (QAt C l)) (iterateTolerance (n - 1) ε)
        hC.q_pos (childBoundary_admissible_for_iterate C hC l)
        (iterateTolerance_nonnegative _ hε.le)
      rw [Nat.one_mul] at hmatrix
      have hPmatrix : Restricts
          (tensorProd Pl.tensor B.tensor)
          (tensorProd Pl.tensor
            (inventoryTensorZ C.q (boundaryOccurrences27 (QAt C l)) m
              (iterateTolerance (n - 1) ε)).tensor) :=
        OmegaBound.Restricts.tensorProd_left hmatrix Pl.tensor
      have hcomm : Restricts (tensorProd B.tensor Pl.tensor)
          (tensorProd Pl.tensor B.tensor) :=
        tensorProd_comm_le B.tensor Pl.tensor
      have hprefixRestriction : Restricts (tensorProdZ B Pl).tensor
          (inventoryTensorZ C.q (QAt C l) m (iterateTolerance (n - 1) ε)).tensor :=
        Tensor3.Restricts.trans hcomm (Tensor3.Restricts.trans hPmatrix hlink.1)
      have hprefixCopies := copiesZ_restricts_of_restricts
        (d.V (iterateTolerance (n - 1) ε) m) hprefixRestriction
      obtain ⟨Np, hp⟩ := integral_polyDegeneratesAt_trans hc
        (polyDegeneratesAt_of_restricts hprefixCopies)
      have hpooled := integral_pool_accounting
        (d.Q (iterateTolerance (n - 1) ε) m)
        (d.V (iterateTolerance (n - 1) ε) m)
        (iterateStageQThrough C hC hpool n ε m)
        (iterateStageVThrough C hC hpool n ε m)
        (inventoryTensorZ C.q (P C l) m (iterateTolerance n ε)) B Pl S
        ⟨Np, hp⟩ ⟨Nr, hr'⟩
      obtain ⟨Na, ha⟩ := hpooled
      have happend := (boundaryMatrixZ_append_reindex C.q m
        (boundaryOccurrences27 (QAt C l))
        (iterateStageBoundaryThrough C n)).2
      have happendCopies : Restricts
          (copiesZ (d.V (iterateTolerance (n - 1) ε) m *
            iterateStageVThrough C hC hpool n ε m)
            (boundaryMatrixZ C.q
              (boundaryOccurrences27 (QAt C l) ++ iterateStageBoundaryThrough C n) m)).tensor
          (copiesZ (d.V (iterateTolerance (n - 1) ε) m *
            iterateStageVThrough C hC hpool n ε m) (tensorProdZ B S)).tensor :=
        copiesZ_restricts_of_restricts _ happend
      obtain ⟨Nf, hf⟩ := integral_polyDegeneratesAt_trans ha
        (polyDegeneratesAt_of_restricts happendCopies)
      refine ⟨Nf, ?_⟩
      have hnvalid : 2 ≤ n ∧ n ≤ C.top := ⟨hn2, hntop⟩
      have hQeq : iterateStageQThrough C hC hpool (n + 1) ε m =
          iterateStageQThrough C hC hpool n ε m *
            d.Q (iterateTolerance (n - 1) ε) m := by
        rw [iterateStageQThrough]
        split <;> simp_all [l, d]
      have hVeq : iterateStageVThrough C hC hpool (n + 1) ε m =
          iterateStageVThrough C hC hpool n ε m *
            d.V (iterateTolerance (n - 1) ε) m := by
        rw [iterateStageVThrough]
        split <;> simp_all [l, d]
      have hBeq : iterateStageBoundaryThrough C (n + 1) =
          boundaryOccurrences27 (QAt C l) ++ iterateStageBoundaryThrough C n := by
        rw [iterateStageBoundaryThrough]
        split <;> simp_all [l]
      rw [hQeq, hVeq, hBeq]
      rw [Nat.mul_comm (d.V (iterateTolerance (n - 1) ε) m)
        (iterateStageVThrough C hC hpool n ε m)] at hf
      exact hf

end
end OmegaBound.ADVXXZGeneral
end
