import OmegaBound.ADVXXZGeneralGlobalExactModulusBranches
import OmegaBound.ADVXXZEpsCnt

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private def globalTargetCoord27 {w : ℕ} (W : Side) (u : Shape w) :
    Fin (2 * w + 1) :=
  match W with
  | .X => u.1.1
  | .Y => u.1.2.1
  | .Z => u.1.2.2

private theorem globalTargetMarginal27 {w n : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (J : Fin (∑ u : Shape w,
      ((n : ℚ) * g.joint.prob (r, u)).floor.toNat) → Shape w)
    (hJ : ∀ u, typeCnt J u = ((n : ℚ) * g.joint.prob (r, u)).floor.toNat)
    (W : Side) (a : Fin (2 * w + 1)) :
    typeCnt (fun i => globalTargetCoord27 W (J i)) a =
      ∑ u : Shape w, if globalTargetCoord27 W u = a
        then ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
  rw [ADVXXZEps.typeCnt_comp_fiber]
  simp_rw [hJ]
  rw [Finset.sum_filter]

/-- Every regional exact-grid population has a literal target label. -/
theorem globalTargetLabel_nonempty27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    Nonempty (GlobalTargetLabel27 g xi r) := by
  let shapeCount := fun u : Shape w =>
    ((n : ℚ) * g.joint.prob (r, u)).floor.toNat
  obtain ⟨J, hJ⟩ := ADVXXZEps.exists_typeCnt_eq shapeCount rfl
  let j : (globalPopulation g n xi r).Label := ⟨J, by
    intro W a
    simpa only [globalTargetCoord27, typeCnt] using
      globalTargetMarginal27 g r J hJ W a⟩
  refine ⟨⟨j, ?_⟩⟩
  simpa only [globalPopulation, Finset.mem_filter, Finset.mem_univ, true_and, j]
    using hJ

set_option maxHeartbeats 1000000 in
-- The dependent equivalence unfolds the large regional population type exactly once.
private def globalTargetTypeWordsEquiv27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    GlobalTargetLabel27 g xi r ≃
      {J : Fin (globalPopulation g n xi r).n → Shape w // ∀ u,
        typeCnt J u = ((n : ℚ) * g.joint.prob (r, u)).floor.toNat} := by
  classical
  refine
    { toFun := fun j => ⟨j.val.val, fun u => by
        simpa only [histogram27] using
          globalTargetHistogram27 g xi r j.val j.property u⟩
      invFun := fun J => ⟨⟨J.val, ?_⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro W a
    simpa only [globalPopulation, globalTargetCoord27, typeCnt] using
      globalTargetMarginal27 g r J.val J.property W a
  · simpa only [globalPopulation, Finset.mem_filter, Finset.mem_univ, true_and]
      using J.property

/-- Exact type-class entropy bounds for the regional target-label family. -/
theorem globalTargetLabel_entropy_bounds27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    let P := globalPopulation g n xi r
    let H := entropyNats (fun u : Shape w =>
      ((((n : ℚ) * g.joint.prob (r, u)).floor.toNat : ℕ) : ℝ) / P.n)
    Real.exp ((P.n : ℝ) * H) / ((P.n : ℝ) + 1) ^ Fintype.card (Shape w) ≤
        (Fintype.card (GlobalTargetLabel27 g xi r) : ℝ) ∧
      (Fintype.card (GlobalTargetLabel27 g xi r) : ℝ) ≤
        Real.exp ((P.n : ℝ) * H) := by
  classical
  dsimp only
  have h := type_class_bounds (globalPopulation g n xi r).n
    (fun u : Shape w => ((n : ℚ) * g.joint.prob (r, u)).floor.toNat) rfl
  dsimp only at h
  have hcard : Fintype.card (GlobalTargetLabel27 g xi r) =
      Fintype.card {J : Fin (globalPopulation g n xi r).n → Shape w // ∀ u,
        typeCnt J u = ((n : ℚ) * g.joint.prob (r, u)).floor.toNat} :=
    Fintype.card_congr (globalTargetTypeWordsEquiv27 g xi r)
  rw [hcard]
  simpa only using h

/-- The simultaneous hash choice can be equipped with literal target and bucket labels in all
    six regions. -/
theorem global_demand_valid_hashes_with_targets27 {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b * m)) :
    ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2 * k r + 1)))
      (j : (r : Fin 6) → GlobalTargetLabel27 g xi r)
      (bucketIndex : (r : Fin 6) → GlobalBucketLabel27 (B r)),
      ValidGlobalHashes g (b * m) xi (fun r => 2 * k r + 1) B ∧
      ∀ r,
        2 * globalDemand g b floor m xi r ≤ 2 * k r + 1 ∧
        2 * k r + 1 ≤ 2 * max (max floor (2 * w + 3))
          (2 * globalDemand g b floor m xi r) ∧
        (B r).card = rothNumberNat (k r) := by
  obtain ⟨k, B, hvalid, hbounds, hB⟩ :=
    global_demand_valid_hashes_with_buckets27 g floor m xi
  let j : (r : Fin 6) → GlobalTargetLabel27 g xi r := fun r =>
    Classical.choice (globalTargetLabel_nonempty27 g xi r)
  let bucketIndex : (r : Fin 6) → GlobalBucketLabel27 (B r) := fun r =>
    Classical.choice (hB r)
  exact ⟨k, B, j, bucketIndex, hvalid, hbounds⟩

end
end OmegaBound.ADVXXZGeneral
end
