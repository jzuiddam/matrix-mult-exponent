import OmegaBound.ADVXXZGeneralGridInput29TwinInputParentMoment

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

set_option maxHeartbeats 1000000 in
/-- The abstract parent-cell moment specializes to the actual equal-cardinality
exact-part fibre, with the paired statistic rewritten pointwise. -/
theorem inputExactPart_parent_fourth_moment {w : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {s b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m)
      (hm : 2 ≤ m) (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
      (t : Fin s) (sigma : Chunk (w + w)),
      avg (fun a : StageExactPart27 0 b m p d r J.val W =>
        ((inputStagePairCount p d r J.val W a t sigma : ℝ) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
            ((d.betaRegion W t r).prob sigma : ℝ))^4) ≤
        C * (StageCandidateRaw.stageParentCount b m p d r t : ℝ)^2 := by
  obtain ⟨C,hC,hparent⟩ :=
    (inputConditionedParent_fourth_moment (w := w))
  refine ⟨C,hC,?_⟩
  intro s b m p d hd hb hm r J W t sigma
  let Ω := StageExactPart27 0 b m p d r J.val W
  let e := inputExactPartFibreEquiv p d hd r J.val W
  have hΩ : Nonempty Ω :=
    stageExactPart_nonempty27 0 m p d hd hb r J.val J.property W
  have h := hparent p d hd hb hm r J W Ω hΩ e t sigma
  have hpoint : ∀ a : Ω,
      (∑ u : ChildShape p t,
        (inputProductCellCount p d r J.val W (e a) t u
          (leftHalf sigma) (rightHalf sigma) : ℝ)) =
        inputStagePairCount p d r J.val W a t sigma := by
    intro a
    rw [inputStagePairCount_eq_sum p d r J.val W a t sigma]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact_mod_cast inputProductCellCount_on_exact p d hd r J.val W a t u
      (leftHalf sigma) (rightHalf sigma)
  have hfun : (fun a : Ω =>
      ((∑ u : ChildShape p t,
          (inputProductCellCount p d r J.val W (e a) t u
            (leftHalf sigma) (rightHalf sigma) : ℝ)) -
        (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
          ((d.betaRegion W t r).prob sigma : ℝ))^4) =
      fun a : Ω =>
        ((inputStagePairCount p d r J.val W a t sigma : ℝ) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
            ((d.betaRegion W t r).prob sigma : ℝ))^4 := by
    funext a
    rw [hpoint a]
  rw [hfun] at h
  exact h

end
end OmegaBound.ADVXXZGeneral.Grid29
end

