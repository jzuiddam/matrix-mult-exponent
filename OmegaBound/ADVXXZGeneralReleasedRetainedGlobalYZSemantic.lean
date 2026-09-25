import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalYZCore

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

private theorem released_global_shape_sum_yz (f : Shape 4 → ℝ) :
    (∑ u : Shape 4, f u) = ∑ c : Fin 45, f (releasedPhysicalShapeAtYZ c) := by
  exact (Equiv.sum_comp releasedPhysicalShapeEquivYZ f).symm

theorem released_globalAverage_row_sum (r : Fin 6) (W : Side) (c : Chunk 4) :
    globalAverage physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r W) c =
      ∑ n : Fin 45,
        ((OmegaBound.ADVXXZG1.aw r n : ℝ) /
            116056878683004400771792896) *
          (OmegaBound.ADVXXZG1.betaIdx r W n).probR c := by
  unfold globalAverage
  rw [released_global_shape_sum_yz]
  rw [(Equiv.sum_comp (releasedPhysRowEquivK r)
    (fun n : Fin 45 =>
      physicalGlobalSpec.toPaper.alpha r (releasedPhysicalShapeAtYZ n) *
        (physicalGlobalSpec.toPaper.beta
          (physicalGlobalSpec.toPaper.perm r W) r (releasedPhysicalShapeAtYZ n)).probR c)).symm]
  apply Finset.sum_congr rfl
  intro n _
  change physicalGlobalSpec.toPaper.alpha r
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) *
        (physicalGlobalSpec.toPaper.beta
          (physicalGlobalSpec.toPaper.perm r W) r
          (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n))).probR c = _
  rw [released_physical_alpha_logical_index,
    released_physical_beta_logical_index]

private theorem released_probR_eq_cast_prob_k {ι : Type*} [Fintype ι]
    (P : RatDist ι) (a : ι) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem released_row_support_sum (r : Fin 6) (S : Side) (c : Chunk 4)
    (hsupport : ∀ (n : Fin 45) (c : Chunk 4),
      (OmegaBound.ADVXXZG1.betaIdx r S n).num c ≠ 0 ↔
        chunkLvl c = OmegaBound.ADVXXZG1.rowLvl S n) :
    (∑ n : Fin 45,
        ((OmegaBound.ADVXXZG1.aw r n : ℝ) /
            116056878683004400771792896) *
          (OmegaBound.ADVXXZG1.betaIdx r S n).probR c) =
      ∑ n ∈ OmegaBound.ADVXXZG1.grp S
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)),
        ((OmegaBound.ADVXXZG1.aw r n : ℝ) /
            116056878683004400771792896) *
          (OmegaBound.ADVXXZG1.betaIdx r S n).probR c := by
  classical
  symm
  apply Finset.sum_subset (OmegaBound.ADVXXZG1.grp S
    (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1))).subset_univ
  intro n _ hn
  simp only [OmegaBound.ADVXXZG1.grp, Finset.mem_filter, Finset.mem_univ,
    true_and] at hn
  have hnum : (OmegaBound.ADVXXZG1.betaIdx r S n).num c = 0 := by
    by_contra hne
    exact hn ((hsupport n c).mp hne).symm
  simp [RatDist.probR, hnum]

private theorem released_parent_mixture_real
    (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4)
    (hA : 0 < OmegaBound.ADVXXZG1.Atot r S l)
    (hparent : OmegaBound.ADVXXZG1.ParentOK avg S r l c) :
    ((avg r l c : ℚ) : ℝ) =
      (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
          (OmegaBound.ADVXXZG1.aw r n : ℝ) *
            (OmegaBound.ADVXXZG1.betaIdx r S n).probR c) /
        (OmegaBound.ADVXXZG1.Atot r S l : ℝ) := by
  have hq := released_prob_parent_mixture_k avg S r l c hA hparent
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
  simpa only [Rat.cast_div, Rat.cast_sum, Rat.cast_mul,
    released_probR_eq_cast_prob_k] using hr

private theorem released_scaled_parent_mixture
    (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4)
    (hA : 0 < OmegaBound.ADVXXZG1.Atot r S l)
    (hparent : OmegaBound.ADVXXZG1.ParentOK avg S r l c) :
    (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
        ((OmegaBound.ADVXXZG1.aw r n : ℝ) /
            116056878683004400771792896) *
          (OmegaBound.ADVXXZG1.betaIdx r S n).probR c) =
      ((OmegaBound.ADVXXZG1.Atot r S l : ℝ) /
          116056878683004400771792896) * ((avg r l c : ℚ) : ℝ) := by
  have hmix := released_parent_mixture_real avg S r l c hA hparent
  have hAr : (OmegaBound.ADVXXZG1.Atot r S l : ℝ) ≠ 0 := by
    exact_mod_cast hA.ne'
  calc
    (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
        ((OmegaBound.ADVXXZG1.aw r n : ℝ) /
            116056878683004400771792896) *
          (OmegaBound.ADVXXZG1.betaIdx r S n).probR c) =
        (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
          (OmegaBound.ADVXXZG1.aw r n : ℝ) *
            (OmegaBound.ADVXXZG1.betaIdx r S n).probR c) /
          116056878683004400771792896 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ((OmegaBound.ADVXXZG1.Atot r S l : ℝ) /
          116056878683004400771792896) * ((avg r l c : ℚ) : ℝ) := by
      rw [hmix]
      field_simp

/-- Parent mixture plus level support collapses the physical global average to one released
conditioned average row. -/
theorem released_globalAverage_eq_parent
    (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (c : Chunk 4)
    (hparent : ∀ (l : Fin (2 * 4 + 1)) (c : Chunk 4),
      OmegaBound.ADVXXZG1.ParentOK avg S r l c)
    (hA : ∀ l : Fin (2 * 4 + 1), 0 < OmegaBound.ADVXXZG1.Atot r S l)
    (hsupport : ∀ (n : Fin 45) (c : Chunk 4),
      (OmegaBound.ADVXXZG1.betaIdx r S n).num c ≠ 0 ↔
        chunkLvl c = OmegaBound.ADVXXZG1.rowLvl S n) :
    globalAverage physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r S) c =
      ((OmegaBound.ADVXXZG1.Atot r S
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) : ℕ) : ℝ) /
          116056878683004400771792896 *
        ((avg r
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) c : ℚ) : ℝ) := by
  rw [released_globalAverage_row_sum,
    released_row_support_sum r S c hsupport]
  exact released_scaled_parent_mixture avg S r _ c (hA _) (hparent _ c)

private theorem released_parentY_all_k (r : Fin 6) :
    ∀ (l : Fin (2 * 4 + 1)) (c : Chunk 4),
      OmegaBound.ADVXXZG1.ParentOK
        OmegaBound.ADVXXZCertRegionalSemantic.avgY .Y r l c := by
  fin_cases r
  · exact released_parentY_k_r0
  · exact released_parentY_k_r1
  · exact released_parentY_k_r2
  · exact released_parentY_k_r3
  · exact released_parentY_k_r4
  · exact released_parentY_k_r5

private theorem released_parentZ_all_k (r : Fin 6) :
    ∀ (l : Fin (2 * 4 + 1)) (c : Chunk 4),
      OmegaBound.ADVXXZG1.ParentOK
        OmegaBound.ADVXXZCertRegionalSemantic.avgZ .Z r l c := by
  fin_cases r
  · exact released_parentZ_k_r0
  · exact released_parentZ_k_r1
  · exact released_parentZ_k_r2
  · exact released_parentZ_k_r3
  · exact released_parentZ_k_r4
  · exact released_parentZ_k_r5

private theorem released_AtotY_pos_all_k (r : Fin 6) :
    ∀ l : Fin (2 * 4 + 1), 0 < OmegaBound.ADVXXZG1.Atot r .Y l := by
  fin_cases r
  · exact released_AtotY_pos_k_r0
  · exact released_AtotY_pos_k_r1
  · exact released_AtotY_pos_k_r2
  · exact released_AtotY_pos_k_r3
  · exact released_AtotY_pos_k_r4
  · exact released_AtotY_pos_k_r5

private theorem released_AtotZ_pos_all_k (r : Fin 6) :
    ∀ l : Fin (2 * 4 + 1), 0 < OmegaBound.ADVXXZG1.Atot r .Z l := by
  fin_cases r
  · exact released_AtotZ_pos_k_r0
  · exact released_AtotZ_pos_k_r1
  · exact released_AtotZ_pos_k_r2
  · exact released_AtotZ_pos_k_r3
  · exact released_AtotZ_pos_k_r4
  · exact released_AtotZ_pos_k_r5

private theorem released_betaY_support_all_k (r : Fin 6) :
    ∀ (n : Fin 45) (c : Chunk 4),
      (OmegaBound.ADVXXZG1.betaIdx r .Y n).num c ≠ 0 ↔
        chunkLvl c = OmegaBound.ADVXXZG1.rowLvl .Y n := by
  fin_cases r
  · exact released_betaY_support_k_r0
  · exact released_betaY_support_k_r1
  · exact released_betaY_support_k_r2
  · exact released_betaY_support_k_r3
  · exact released_betaY_support_k_r4
  · exact released_betaY_support_k_r5

private theorem released_betaZ_support_all_k (r : Fin 6) :
    ∀ (n : Fin 45) (c : Chunk 4),
      (OmegaBound.ADVXXZG1.betaIdx r .Z n).num c ≠ 0 ↔
        chunkLvl c = OmegaBound.ADVXXZG1.rowLvl .Z n := by
  fin_cases r
  · exact released_betaZ_support_k_r0
  · exact released_betaZ_support_k_r1
  · exact released_betaZ_support_k_r2
  · exact released_betaZ_support_k_r3
  · exact released_betaZ_support_k_r4
  · exact released_betaZ_support_k_r5

theorem released_globalAverageY_semantic (r : Fin 6) (c : Chunk 4) :
    globalAverage physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r .Y) c =
      ((OmegaBound.ADVXXZG1.Atot r .Y
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) : ℕ) : ℝ) /
          116056878683004400771792896 *
        ((OmegaBound.ADVXXZCertRegionalSemantic.avgY r
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) c : ℚ) : ℝ) := by
  exact released_globalAverage_eq_parent _ .Y r c
    (released_parentY_all_k r) (released_AtotY_pos_all_k r)
    (released_betaY_support_all_k r)

theorem released_globalAverageZ_semantic (r : Fin 6) (c : Chunk 4) :
    globalAverage physicalGlobalSpec.toPaper r
        (physicalGlobalSpec.toPaper.perm r .Z) c =
      ((OmegaBound.ADVXXZG1.Atot r .Z
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) : ℕ) : ℝ) /
          116056878683004400771792896 *
        ((OmegaBound.ADVXXZCertRegionalSemantic.avgZ r
          (⟨chunkLvl c, by have := chunkLvl_le c; omega⟩ : Fin (2 * 4 + 1)) c : ℚ) : ℝ) := by
  exact released_globalAverage_eq_parent _ .Z r c
    (released_parentZ_all_k r) (released_AtotZ_pos_all_k r)
    (released_betaZ_support_all_k r)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_globalAverage_row_sum
#print axioms OmegaBound.ADVXXZGeneral.released_globalAverage_eq_parent
#print axioms OmegaBound.ADVXXZGeneral.released_globalAverageY_semantic
#print axioms OmegaBound.ADVXXZGeneral.released_globalAverageZ_semantic
