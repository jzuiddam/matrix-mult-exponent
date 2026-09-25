import OmegaBound.ADVXXZGeneralGridInput29TwinInputStageCenters
import OmegaBound.ADVXXZGeneralPProjectionParent25

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral.Grid29
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The number of actual parent positions carrying a prescribed paired chunk. -/
noncomputable def inputStagePairCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (sigma : Chunk (w+w)) : ℕ :=
  OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a.val t i) sigma

private theorem inputPhysical_paired_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (W : Side)
    (a : (stagePopulationAt 0 p d b m r).Part W) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t))
    (sigma : Chunk (w+w)) :
    Parent25.paired a t i = sigma ↔
      a ⟨t,i,0⟩ = leftHalf sigma ∧ a ⟨t,i,1⟩ = rightHalf sigma := by
  constructor
  · intro h
    constructor
    · rw [← parent25_leftHalf_paired a t i, h]
    · rw [← parent25_rightHalf_paired a t i, h]
  · rintro ⟨hleft,hright⟩
    funext c
    unfold Parent25.paired
    split_ifs with hc
    · have h := congrFun hleft ⟨c.val,hc⟩
      simpa only [leftHalf] using h
    · have hc' : w ≤ c.val := Nat.le_of_not_gt hc
      have hlt : c.val - w < w := by
        have := c.isLt
        omega
      have h := congrFun hright ⟨c.val-w,hlt⟩
      simpa only [rightHalf, Nat.add_sub_of_le hc'] using h

private theorem inputPhysical_cellCount_eq_filter {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (sigma : Chunk (w+w)) :
    inputStageSelfPhysicalCount p d r j W a t u
        (leftHalf sigma) (rightHalf sigma) =
      (Finset.univ.filter fun i :
        Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          stageColour27 0 b m p d r j t (i,0) = u ∧
            Parent25.paired a.val t i = sigma).card := by
  let e := Finite.equivFin (InputStageCellPos p d r j t u)
  unfold inputStageSelfPhysicalCount
  refine Finset.card_bij (fun q _ => (e.symm q).val.1) ?_ ?_ ?_
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hhalf : (e.symm q).val.2 = 0 := by
      simpa only [inputStageFirstPositions, Finset.mem_filter,
        Finset.mem_univ, true_and, e] using hq'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hz : (e.symm q).val = ((e.symm q).val.1,0) := Prod.ext rfl hhalf
      rw [← hz]
      exact (e.symm q).property
    · rw [inputPhysical_paired_iff p d r W a.val t]
      constructor
      · have hz : (e.symm q).val = ((e.symm q).val.1,0) := Prod.ext rfl hhalf
        rw [← hz]
        exact hq'.2.1
      · have hswap :
            (inputStageCellSwap p d r j t u (e.symm q)).val =
              ((e.symm q).val.1,1) := by
          simp only [inputStageCellSwap, Equiv.subtypeEquiv_apply,
            Equiv.prodCongr_apply, Equiv.refl_apply]
          have hz : (e.symm q).val = ((e.symm q).val.1,0) :=
            Prod.ext rfl hhalf
          rw [hz]
          rfl
        rw [← hswap]
        exact hq'.2.2
  · intro q₁ hq₁ q₂ hq₂ heq
    apply e.symm.injective
    apply Subtype.ext
    apply Prod.ext heq
    have h₁ : (e.symm q₁).val.2 = 0 := by
      simpa only [inputStageFirstPositions, Finset.mem_filter,
        Finset.mem_univ, true_and, e] using (Finset.mem_filter.mp hq₁).1
    have h₂ : (e.symm q₂).val.2 = 0 := by
      simpa only [inputStageFirstPositions, Finset.mem_filter,
        Finset.mem_univ, true_and, e] using (Finset.mem_filter.mp hq₂).1
    exact h₁.trans h₂.symm
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    let z : InputStageCellPos p d r j t u := ⟨(i,0),hi'.1⟩
    refine ⟨e z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · simp only [inputStageFirstPositions, Finset.mem_filter,
          Finset.mem_univ, true_and, e, Equiv.symm_apply_apply]
        rfl
      · rw [inputPhysical_paired_iff p d r W a.val t] at hi'
        simpa only [e, Equiv.symm_apply_apply, z] using hi'.2
    · simp only [e, Equiv.symm_apply_apply, z]

/-- The parent paired-chunk count is the sum of the actual oriented counts in all
child cells. -/
theorem inputStagePairCount_eq_sum {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (sigma : Chunk (w+w)) :
    inputStagePairCount p d r j W a t sigma =
      ∑ u : ChildShape p t,
        inputStageSelfPhysicalCount p d r j W a t u
          (leftHalf sigma) (rightHalf sigma) := by
  simp_rw [inputPhysical_cellCount_eq_filter p d r j W a t]
  unfold inputStagePairCount OmegaBound.ADVXXZ.typeCnt
  change (Finset.univ.filter fun i :
      Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
        Parent25.paired a.val t i = sigma).card = _
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      stageColour27 0 b m p d r j t (i,0))
    (s := Finset.univ.filter fun i => Parent25.paired a.val t i = sigma)
    (t := Finset.univ)]
  · apply Finset.sum_congr rfl
    intro u _
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · intro i _
    exact Finset.mem_univ _

private theorem inputPhysical_child_num_ne {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (z : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :
    (d.betaChild W t r (stageColour27 0 b m p d r j t z)).num
        (a.val ⟨t,z⟩) ≠ 0 := by
  let u := stageColour27 0 b m p d r j t z
  let tau := a.val ⟨t,z⟩
  have hpart := (stageExact_iff_partition27 0 b m p d r j W a.val).mp a.property
  have hhist : 0 < histogram27
      (fun i => (stageColour27 0 b m p d r j t i, a.val ⟨t,i⟩))
      (u,tau) := by
    unfold histogram27
    apply Finset.card_pos.mpr
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hcount : 0 < stageCounts27 m p d r W t u tau := by
    rw [← hpart.2 t u tau]
    exact hhist
  intro hzero
  have hzero' : (d.betaChild W t r u).num tau = 0 := hzero
  have hz : stageCounts27 m p d r W t u tau = 0 := by
    unfold stageCounts27
    rw [show (d.betaChild W t r u).prob tau = 0 by
      unfold RatDist.prob
      rw [hzero']
      norm_num]
    simp only [mul_zero]
    change ((((0 : ℤ) : ℚ).floor).toNat) = 0
    rw [Rat.floor_intCast]
    exact Int.toNat_zero
  omega

private theorem inputPhysical_alpha_num_ne {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    (d.alpha t r).num (stageColour27 0 b m p d r J.val t (i,0)) ≠ 0 := by
  let u := stageColour27 0 b m p d r J.val t (i,0)
  let z : InputStageCellPos p d r J.val t u := ⟨(i,0),rfl⟩
  let q := Finite.equivFin (InputStageCellPos p d r J.val t u) z
  have hq : q ∈ inputStageFirstPositions p d r J.val t u := by
    simp only [inputStageFirstPositions, Finset.mem_filter,
      Finset.mem_univ, true_and, q, Equiv.symm_apply_apply, z]
  have hpos : 0 < StageCandidateRaw.stageAlphaCount b m p d r t u := by
    rw [← inputStageFirstPositions_card p d r J t u]
    exact Finset.card_pos.mpr ⟨q,hq⟩
  intro hzero
  have hzero' : (d.alpha t r).num u = 0 := hzero
  have hz : StageCandidateRaw.stageAlphaCount b m p d r t u = 0 := by
    unfold StageCandidateRaw.stageAlphaCount
    rw [show (d.alpha t r).prob u = 0 by
      unfold RatDist.prob
      rw [hzero']
      norm_num]
    simp only [mul_zero]
    change ((((0 : ℤ) : ℚ).floor).toNat) = 0
    rw [Rat.floor_intCast]
    exact Int.toNat_zero
  omega

private theorem inputPhysical_prob_pos {alpha : Type*} [Fintype alpha]
    (P : RatDist alpha) (a : alpha) (h : P.num a ≠ 0) : 0 < P.prob a := by
  unfold RatDist.prob
  apply div_pos
  · exact_mod_cast Nat.pos_of_ne_zero h
  · exact_mod_cast P.den_pos

/-- Every paired parent chunk occurring in an exact physical part lies in the
regional split support. -/
theorem inputExactPart_region_num_ne {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (a : StageExactPart27 0 b m p d r J.val W) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    (d.betaRegion W t r).num (Parent25.paired a.val t i) ≠ 0 := by
  let u := stageColour27 0 b m p d r J.val t (i,0)
  have hu := inputPhysical_alpha_num_ne p d r J t i
  have hleft := inputPhysical_child_num_ne p d hd r J.val W a t (i,0)
  have hright := inputPhysical_child_num_ne p d hd r J.val W a t (i,1)
  have hcomp : stageColour27 0 b m p d r J.val t (i,1) = complement p t u :=
    J.val.property.2 t i
  have hterm : 0 < (d.alpha t r).prob u *
      (d.betaChild W t r u).prob (leftHalf (Parent25.paired a.val t i)) *
      (d.betaChild W t r (complement p t u)).prob
        (rightHalf (Parent25.paired a.val t i)) := by
    rw [parent25_leftHalf_paired, parent25_rightHalf_paired]
    apply mul_pos
    · exact mul_pos (inputPhysical_prob_pos _ _ hu)
        (inputPhysical_prob_pos _ _ hleft)
    · apply inputPhysical_prob_pos
      simpa only [hcomp] using hright
  have hle : (d.alpha t r).prob u *
      (d.betaChild W t r u).prob (leftHalf (Parent25.paired a.val t i)) *
      (d.betaChild W t r (complement p t u)).prob
        (rightHalf (Parent25.paired a.val t i)) ≤
      ∑ v, (d.alpha t r).prob v *
        (d.betaChild W t r v).prob (leftHalf (Parent25.paired a.val t i)) *
        (d.betaChild W t r (complement p t v)).prob
          (rightHalf (Parent25.paired a.val t i)) := by
    simpa only using (Finset.single_le_sum
      (s := (Finset.univ : Finset (ChildShape p t)))
      (f := fun v => (d.alpha t r).prob v *
        (d.betaChild W t r v).prob (leftHalf (Parent25.paired a.val t i)) *
        (d.betaChild W t r (complement p t v)).prob
          (rightHalf (Parent25.paired a.val t i)))
      (fun v _ => mul_nonneg
        (mul_nonneg ((d.alpha t r).prob_nonneg v)
          ((d.betaChild W t r v).prob_nonneg _))
        ((d.betaChild W t r (complement p t v)).prob_nonneg _))
      (Finset.mem_univ u))
  have hregion : 0 < (d.betaRegion W t r).prob
      (Parent25.paired a.val t i) := by
    rw [hd.pair_mixture W t r]
    exact hterm.trans_le hle
  intro hzero
  rw [show (d.betaRegion W t r).prob (Parent25.paired a.val t i) = 0 by
    simp [RatDist.prob,hzero]] at hregion
  exact lt_irrefl 0 hregion

/-- The regional support law supplies the parent grade clause on every exact
physical part. -/
theorem inputExactPart_region_grade {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (a : StageExactPart27 0 b m p d r J.val W) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    chunkLvl (Parent25.paired a.val t i) =
      match W with | .X => p.i t | .Y => p.j t | .Z => p.k t :=
  by
    cases W <;> simpa using hd.regional_support _ t r _
      (inputExactPart_region_num_ne p d hd r J _ a t i)

end
end OmegaBound.ADVXXZGeneral.Grid29
end

