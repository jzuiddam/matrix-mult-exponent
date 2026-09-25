import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalYZSemantic

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

/-! These are the nats penalty definitions `globalEtaNats` and `globalLambdaNats`, repeated at
width 4 under Y/Z-local names. -/

noncomputable def releasedGlobalEtaNatsYZ (d : GlobalData 4) (r : Fin 6)
    (_xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord zSide u = 0 then
      d.alpha r u * Entropy.H Finset.univ (d.beta ySide r u).probR else 0) +
  ∑ a : Fin (2 * 4 + 1),
    let mass := ∑ u, if coord ySide u = a ∧ 0 < coord zSide u then d.alpha r u else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (d.alpha r) (d.beta ySide r)
        (fun u => coord ySide u = a ∧ 0 < coord zSide u))

noncomputable def releasedGlobalLambdaNatsYZ (d : GlobalData 4) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord xSide u = 0 ∨ coord ySide u = 0 then
      d.alpha r u * Entropy.H Finset.univ (d.beta zSide r u).probR else 0) +
  ∑ a : Fin (2 * 4 + 1),
    let mass := ∑ u, if 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a
      then d.alpha r u else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (d.alpha r) (d.beta zSide r)
        (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a))

/-- The physical shape law read on the logical released row index. -/
noncomputable def releasedLogicalAlphaYZ (r : Fin 6) (n : Fin 45) : ℝ :=
  (OmegaBound.ADVXXZG1.aw r n : ℝ) / 116056878683004400771792896

/-- The complete-split law read on the logical released row index. -/
def releasedLogicalBetaYZ (r : Fin 6) (W : Side) (n : Fin 45) : SplitDist 4 :=
  OmegaBound.ADVXXZG1.betaIdx r W n

/-- Logical rows are equivalent to physical global shapes after applying `physRow`. -/
def releasedLogicalShapeEquivYZ (r : Fin 6) : Fin 45 ≃ Shape 4 :=
  (releasedPhysRowEquivK r).trans releasedPhysicalShapeEquivYZ

theorem released_logical_shape_alpha_yz (r : Fin 6) (n : Fin 45) :
    physicalGlobalSpec.toPaper.alpha r (releasedLogicalShapeEquivYZ r n) =
      releasedLogicalAlphaYZ r n := by
  change physicalGlobalSpec.toPaper.alpha r
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) = _
  exact released_physical_alpha_logical_index r n

theorem released_logical_shape_beta_yz (r : Fin 6) (W : Side) (n : Fin 45) :
    physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r W) r
        (releasedLogicalShapeEquivYZ r n) = releasedLogicalBetaYZ r W n := by
  change physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r W) r
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) = _
  exact released_physical_beta_logical_index r W n

theorem released_logical_shape_coord_yz (r : Fin 6) (W : Side) (n : Fin 45) :
    coord (physicalGlobalSpec.toPaper.perm r W) (releasedLogicalShapeEquivYZ r n) =
      OmegaBound.ADVXXZG1.rowLvl W n := by
  change coord (physicalGlobalSpec.toPaper.perm r W)
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) = _
  exact released_physical_coord_logical_index r W n

private theorem released_shape_sum_logical_yz (r : Fin 6) (f : Shape 4 → ℝ) :
    (∑ u : Shape 4, f u) = ∑ n : Fin 45, f (releasedLogicalShapeEquivYZ r n) := by
  exact (Equiv.sum_comp (releasedLogicalShapeEquivYZ r) f).symm

/-- Reindex a physical weighted split by the transported logical released rows. -/
theorem released_weightedSplit_logical_yz (r : Fin 6) (W : Side)
    (selected : Shape 4 → Prop) [DecidablePred selected] :
    weightedSplit (physicalGlobalSpec.toPaper.alpha r)
        (physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r W) r)
        selected =
      weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r W)
        (fun n => selected (releasedLogicalShapeEquivYZ r n)) := by
  funext c
  unfold weightedSplit
  apply congrArg₂ (· / ·)
  · rw [released_shape_sum_logical_yz r]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [released_logical_shape_alpha_yz, released_logical_shape_beta_yz]
    · rfl
  · rw [released_shape_sum_logical_yz r]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [released_logical_shape_alpha_yz]
    · rfl

private theorem released_weightedSplit_selected_congr_yz (r : Fin 6) (W : Side)
    (P Q : Fin 45 → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ n, P n ↔ Q n) :
    weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r W) P =
      weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r W) Q := by
  funext c
  unfold weightedSplit
  apply congrArg₂ (· / ·)
  · apply Finset.sum_congr rfl
    intro n _
    exact if_congr (h n) rfl rfl
  · apply Finset.sum_congr rfl
    intro n _
    exact if_congr (h n) rfl rfl

theorem released_weightedSplit_y_logical (r : Fin 6) (a : Fin (2 * 4 + 1)) :
    weightedSplit (physicalGlobalSpec.toPaper.alpha r)
        (physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r .Y) r)
        (fun u => coord (physicalGlobalSpec.toPaper.perm r .Y) u = a ∧
          0 < coord (physicalGlobalSpec.toPaper.perm r .Z) u) =
      weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r .Y)
        (fun n => OmegaBound.ADVXXZG1.rowLvl .Y n = a ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Z n) := by
  rw [released_weightedSplit_logical_yz]
  apply released_weightedSplit_selected_congr_yz
  intro n
  rw [released_logical_shape_coord_yz, released_logical_shape_coord_yz]

theorem released_weightedSplit_z_logical (r : Fin 6) (a : Fin (2 * 4 + 1)) :
    weightedSplit (physicalGlobalSpec.toPaper.alpha r)
        (physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r .Z) r)
        (fun u => 0 < coord (physicalGlobalSpec.toPaper.perm r .X) u ∧
          0 < coord (physicalGlobalSpec.toPaper.perm r .Y) u ∧
            coord (physicalGlobalSpec.toPaper.perm r .Z) u = a) =
      weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r .Z)
        (fun n => 0 < OmegaBound.ADVXXZG1.rowLvl .X n ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Y n ∧
            OmegaBound.ADVXXZG1.rowLvl .Z n = a) := by
  rw [released_weightedSplit_logical_yz]
  apply released_weightedSplit_selected_congr_yz
  intro n
  rw [released_logical_shape_coord_yz, released_logical_shape_coord_yz,
    released_logical_shape_coord_yz]

noncomputable def releasedGlobalEtaRows (r : Fin 6) : ℝ :=
  (∑ n : Fin 45, if OmegaBound.ADVXXZG1.rowLvl .Z n = 0 then
      releasedLogicalAlphaYZ r n *
        Entropy.H Finset.univ (releasedLogicalBetaYZ r .Y n).probR else 0) +
  ∑ a : Fin (2 * 4 + 1),
    let mass := ∑ n : Fin 45,
      if OmegaBound.ADVXXZG1.rowLvl .Y n = a ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Z n then
        releasedLogicalAlphaYZ r n else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r .Y)
        (fun n => OmegaBound.ADVXXZG1.rowLvl .Y n = a ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Z n))

noncomputable def releasedGlobalLambdaRows (r : Fin 6) : ℝ :=
  (∑ n : Fin 45,
    if OmegaBound.ADVXXZG1.rowLvl .X n = 0 ∨
        OmegaBound.ADVXXZG1.rowLvl .Y n = 0 then
      releasedLogicalAlphaYZ r n *
        Entropy.H Finset.univ (releasedLogicalBetaYZ r .Z n).probR else 0) +
  ∑ a : Fin (2 * 4 + 1),
    let mass := ∑ n : Fin 45,
      if 0 < OmegaBound.ADVXXZG1.rowLvl .X n ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Y n ∧
            OmegaBound.ADVXXZG1.rowLvl .Z n = a then
        releasedLogicalAlphaYZ r n else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (releasedLogicalAlphaYZ r) (releasedLogicalBetaYZ r .Z)
        (fun n => 0 < OmegaBound.ADVXXZG1.rowLvl .X n ∧
          0 < OmegaBound.ADVXXZG1.rowLvl .Y n ∧
            OmegaBound.ADVXXZG1.rowLvl .Z n = a))

theorem released_globalEtaNats_rows (r : Fin 6) :
    releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r .X)
        (physicalGlobalSpec.toPaper.perm r .Y)
        (physicalGlobalSpec.toPaper.perm r .Z) = releasedGlobalEtaRows r := by
  classical
  unfold releasedGlobalEtaNatsYZ releasedGlobalEtaRows
  apply congrArg₂ (· + ·)
  · rw [released_shape_sum_logical_yz r]
    apply Finset.sum_congr rfl
    intro n _
    rw [released_logical_shape_coord_yz]
    split_ifs
    · rw [released_logical_shape_alpha_yz, released_logical_shape_beta_yz]
    · rfl
  · apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [released_shape_sum_logical_yz r]
    simp_rw [released_logical_shape_coord_yz, released_logical_shape_alpha_yz]
    rw [released_weightedSplit_y_logical]

theorem released_globalLambdaNats_rows (r : Fin 6) :
    releasedGlobalLambdaNatsYZ physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r .X)
        (physicalGlobalSpec.toPaper.perm r .Y)
        (physicalGlobalSpec.toPaper.perm r .Z) = releasedGlobalLambdaRows r := by
  classical
  unfold releasedGlobalLambdaNatsYZ releasedGlobalLambdaRows
  apply congrArg₂ (· + ·)
  · rw [released_shape_sum_logical_yz r]
    apply Finset.sum_congr rfl
    intro n _
    rw [released_logical_shape_coord_yz, released_logical_shape_coord_yz]
    split_ifs
    · rw [released_logical_shape_alpha_yz, released_logical_shape_beta_yz]
    · rfl
  · apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [released_shape_sum_logical_yz r]
    simp_rw [released_logical_shape_coord_yz, released_logical_shape_alpha_yz]
    rw [released_weightedSplit_z_logical]

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_weightedSplit_logical_yz
#print axioms OmegaBound.ADVXXZGeneral.released_weightedSplit_y_logical
#print axioms OmegaBound.ADVXXZGeneral.released_weightedSplit_z_logical
#print axioms OmegaBound.ADVXXZGeneral.released_globalEtaNats_rows
#print axioms OmegaBound.ADVXXZGeneral.released_globalLambdaNats_rows
