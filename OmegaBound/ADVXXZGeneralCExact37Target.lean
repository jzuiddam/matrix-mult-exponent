import OmegaBound.ADVXXZGeneralCExact37Modulus
import OmegaBound.ADVXXZGeneralCounts
import OmegaBound.ADVXXZEntCon

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private def StageAlphaClass37 {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (t : Fin s) :=
  {x : Fin (StageCandidateRaw.stageParentCount b m p d r t) → ChildShape p t //
    ∀ u, typeCnt x u = StageCandidateRaw.stageAlphaCount b m p d r t u}

noncomputable local instance stageAlphaClassFintype37 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (t : Fin s) :
    Fintype (StageAlphaClass37 (b := b) (m := m) p d r t) := Subtype.fintype _

set_option maxHeartbeats 2000000 in
-- Constructing the dependent target label unfolds both its marginal and pair-complement laws.
private noncomputable def stageAlphaClassLabel37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (x : ∀ t, StageAlphaClass37 (b := b) (m := m) p d r t) :
    StageTargetLabel37 q p d b m r := by
  classical
  unfold StageTargetLabel37
  unfold stagePopulationAt
  dsimp only
  refine ⟨⟨fun z => if z.2.2 = 0 then (x z.1).val z.2.1
      else complement p z.1 ((x z.1).val z.2.1), ?_⟩, ?_⟩
  · constructor
    · intro t h W a
      fin_cases h
      · change typeCnt (fun i => Parent25.coordFin W ((x t).val i).val) a = _
        rw [ADVXXZEnt.typeCnt_comp
          (g := fun u : ChildShape p t => Parent25.coordFin W u.val)
          (f := (x t).val)]
        simp [(x t).property, StageCandidateRaw.stageAlphaCount, Parent25.coordFin]
        rfl
      · change typeCnt (fun i =>
          Parent25.coordFin W (complement p t ((x t).val i)).val) a = _
        rw [ADVXXZEnt.typeCnt_comp
          (g := fun u : ChildShape p t =>
            Parent25.coordFin W (complement p t u).val)
          (f := (x t).val)]
        simp [(x t).property, StageCandidateRaw.stageAlphaCount, Parent25.coordFin]
        rfl
    · intro t i
      simp
  · apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_univ]
    intro t u
    change typeCnt (x t).val u = StageCandidateRaw.stageAlphaCount b m p d r t u
    exact (x t).property u

private theorem stageAlphaClassLabel37_zero {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (x : ∀ t, StageAlphaClass37 (b := b) (m := m) p d r t) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    (stageAlphaClassLabel37 q p d r x).val.val ⟨t, (i, 0)⟩ = (x t).val i := by
  unfold stageAlphaClassLabel37
  rfl

private theorem stageAlphaClassLabel37_injective {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    Function.Injective
      (stageAlphaClassLabel37 (b := b) (m := m) q p d r) := by
  intro x y h
  funext t
  apply Subtype.ext
  funext i
  calc
    (x t).val i = (stageAlphaClassLabel37 q p d r x).val.val ⟨t, (i, 0)⟩ :=
      (stageAlphaClassLabel37_zero q p d r x t i).symm
    _ = (stageAlphaClassLabel37 q p d r y).val.val ⟨t, (i, 0)⟩ := by rw [h]
    _ = (y t).val i := stageAlphaClassLabel37_zero q p d r y t i

/-- The exact target family contains the product of the parentwise alpha type classes. -/
private theorem stageTargetLabel_card_product_lower37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    ∏ t, Fintype.card (StageAlphaClass37 (b := b) (m := m) p d r t) ≤
      Fintype.card (StageTargetLabel37 q p d b m r) := by
  rw [← Fintype.card_pi]
  exact Fintype.card_le_of_injective
    (stageAlphaClassLabel37 (b := b) (m := m) q p d r)
    (stageAlphaClassLabel37_injective (b := b) (m := m) q p d r)

set_option maxHeartbeats 2000000 in
-- The product-cardinality coercion makes normalization substantially more expensive.
/-- Product type-class lower bound for the actual constituent target family. -/
theorem stageTargetLabel_typeClass_lower37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    (∏ t : Fin s,
      Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        entropyNats (fun u : ChildShape p t =>
          (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
            StageCandidateRaw.stageParentCount b m p d r t)) /
        ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
          Fintype.card (ChildShape p t)) ≤
      (Fintype.card (StageTargetLabel37 q p d b m r) : ℝ) := by
  have ht : ∀ t : Fin s,
      Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        entropyNats (fun u : ChildShape p t =>
          (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
            StageCandidateRaw.stageParentCount b m p d r t)) /
        ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
          Fintype.card (ChildShape p t) ≤
        (Fintype.card (StageAlphaClass37 (b := b) (m := m) p d r t) : ℝ) := by
    intro t
    exact (type_class_bounds
      (StageCandidateRaw.stageParentCount b m p d r t)
      (StageCandidateRaw.stageAlphaCount b m p d r t)
      (by rfl)).1
  calc
    (∏ t : Fin s,
      Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        entropyNats (fun u : ChildShape p t =>
          (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
            StageCandidateRaw.stageParentCount b m p d r t)) /
        ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
          Fintype.card (ChildShape p t)) ≤
        ∏ t : Fin s,
          (Fintype.card (StageAlphaClass37 (b := b) (m := m) p d r t) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun t _ => ht t)
    _ = ((∏ t : Fin s,
      Fintype.card (StageAlphaClass37 (b := b) (m := m) p d r t) : ℕ) : ℝ) := by
      simp
    _ ≤ (Fintype.card (StageTargetLabel37 q p d b m r) : ℝ) := by
      exact_mod_cast stageTargetLabel_card_product_lower37 q p d r

/-- Every paired-parent stage population has a literal target label. -/
theorem stageTargetLabel_nonempty37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    Nonempty (StageTargetLabel37 q p d b m r) := by
  have hlower := stageTargetLabel_typeClass_lower37 (b := b) (m := m) q p d r
  have hpos : 0 < (∏ t : Fin s,
      Real.exp ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        entropyNats (fun u : ChildShape p t =>
          (StageCandidateRaw.stageAlphaCount b m p d r t u : ℝ) /
            StageCandidateRaw.stageParentCount b m p d r t)) /
        ((StageCandidateRaw.stageParentCount b m p d r t : ℝ) + 1) ^
          Fintype.card (ChildShape p t)) := by
    apply Finset.prod_pos
    intro t _
    positivity
  have hcard : 0 < Fintype.card (StageTargetLabel37 q p d b m r) := by
    exact_mod_cast lt_of_lt_of_le hpos hlower
  exact Fintype.card_pos_iff.mp hcard

/-- The simultaneous stage modulus choice, equipped with concrete target and bucket labels. -/
theorem stage_demand_valid_hashes_with_targets37 {w s b : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (floor : ℕ) (ε : ℚ) (m : ℕ) :
    ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2 * k r + 1)))
      (j : (r : Fin 6) → StageTargetLabel37 q p d b m r)
      (bucketIndex : (r : Fin 6) → StageBucketLabel37 (B r)),
      ValidStageHashes p d b m (fun r => 2 * k r + 1) B ∧
      ∀ r,
        2 * stageDemand25 p d b floor ε m r ≤ 2 * k r + 1 ∧
        2 * k r + 1 ≤ 2 * max (max floor (2 * (w + w) + 3))
          (2 * stageDemand25 p d b floor ε m r) ∧
        (B r).card = rothNumberNat (k r) := by
  classical
  obtain ⟨k, B, hvalid, hbounds⟩ := stage_demand_valid_hashes37 p d floor ε m
  have hB : ∀ r, Nonempty (StageBucketLabel37 (B r)) := by
    intro r
    apply Finset.nonempty_coe_sort.mpr
    exact stage_roth_bucket_nonempty37 (B r) (hbounds r).2.2 (hvalid r).2.1
  let j : (r : Fin 6) → StageTargetLabel37 q p d b m r := fun r =>
    Classical.choice (stageTargetLabel_nonempty37 q p d r)
  let bucketIndex : (r : Fin 6) → StageBucketLabel37 (B r) := fun r =>
    Classical.choice (hB r)
  exact ⟨k, B, j, bucketIndex, hvalid, hbounds⟩

end
end OmegaBound.ADVXXZGeneral
