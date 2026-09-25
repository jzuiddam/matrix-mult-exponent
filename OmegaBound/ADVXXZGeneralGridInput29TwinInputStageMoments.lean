import OmegaBound.ADVXXZGeneralGridInput29TwinInputPhysicalPairs

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

private theorem inputMoments_typeCnt_reindex {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha] {n k : ℕ}
    (e : Fin n ≃ Fin k) (x : Fin k → alpha) (a : alpha) :
    typeCnt (fun i => x (e i)) a = typeCnt x a := by
  unfold typeCnt
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      e.apply_symm_apply] using hj

/-- Reindex the complementary physical-cell word through the actual half swap. -/
noncomputable def inputStageComplementWord {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (t : Fin s) (u : ChildShape p t) :
    Words (Nat.card (InputStageCellPos p d r j t (complement p t u)))
        (stageCounts27 m p d r W t (complement p t u)) ≃
      Words (Nat.card (InputStageCellPos p d r j t u))
        (stageCounts27 m p d r W t (complement p t u)) where
  toFun x := ⟨fun i => x.val (inputStageCellSwapIndex p d r j t u i),
    fun a => (inputMoments_typeCnt_reindex
      (inputStageCellSwapIndex p d r j t u) x.val a).trans (x.property a)⟩
  invFun x := ⟨fun i => x.val ((inputStageCellSwapIndex p d r j t u).symm i),
    fun a => (inputMoments_typeCnt_reindex
      (inputStageCellSwapIndex p d r j t u).symm x.val a).trans (x.property a)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

private theorem inputMoments_avg_equiv {A B : Type*}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The corrected self-cell moment remains valid after an arbitrary finite
conditioning fibre is identified with the nested product of cell words. -/
theorem inputConditionedSelfCell_fourth_moment {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (Ω : Type*) [Fintype Ω] (hΩ : Nonempty Ω)
    (e : Ω ≃ ((t : Fin s) → (u : ChildShape p t) →
      Words (Nat.card (InputStageCellPos p d r J.val t u))
        (stageCounts27 m p d r W t u)))
    (t : Fin s) (u : ChildShape p t) (hu : complement p t u = u)
    (hn : 0 < Nat.card (InputStageCellPos p d r J.val t u))
    (sigma tau : Chunk w) :
    avg (fun x : Ω =>
      ((selfPairCount (inputStageFirstPositions p d r J.val t u)
          (inputStageSelfPairPerm p d r J.val t u hu) sigma tau
          (e x t u).val : ℝ) -
        ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
          (stageCounts27 m p d r W t u sigma : ℝ) *
          ((stageCounts27 m p d r W t u tau : ℝ) -
            if sigma = tau then 1 else 0) /
          ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ) *
            ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ)-1)))^4) ≤
      (2479446 * 8^14 : ℝ) *
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 := by
  have hA : ∀ t u, Nonempty
      (Words (Nat.card (InputStageCellPos p d r J.val t u))
        (stageCounts27 m p d r W t u)) := fun t u =>
    ⟨e (Classical.choice hΩ) t u⟩
  let f : Words (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u) → ℝ := fun x =>
    ((selfPairCount (inputStageFirstPositions p d r J.val t u)
        (inputStageSelfPairPerm p d r J.val t u hu) sigma tau x.val : ℝ) -
      ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u sigma : ℝ) *
        ((stageCounts27 m p d r W t u tau : ℝ) -
          if sigma = tau then 1 else 0) /
        ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ) *
          ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ)-1)))^4
  change avg (fun x : Ω => f (e x t u)) ≤ _
  rw [avg_conditioned_pi_pi_apply (fun t : Fin s => ChildShape p t)
    (fun t u => Words (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)) hA e t u f]
  exact inputStageSelfCell_fourth_moment p d hd hb r J W t u hu hn sigma tau

/-- A single constant controls every distinct complementary-cell moment after an
arbitrary finite conditioning fibre is identified with the nested word product. -/
theorem inputConditionedDistinctCell_fourth_moment {w : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {s b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m)
      (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
      (Ω : Type*) [Fintype Ω] (hΩ : Nonempty Ω)
      (e : Ω ≃ ((t : Fin s) → (u : ChildShape p t) →
        Words (Nat.card (InputStageCellPos p d r J.val t u))
          (stageCounts27 m p d r W t u)))
      (t : Fin s) (u : ChildShape p t) (hu : u ≠ complement p t u)
      (hn : 0 < Nat.card (InputStageCellPos p d r J.val t u))
      (sigma tau : Chunk w),
      avg (fun x : Ω =>
        ((restrictedPairCount (inputStageFirstPositions p d r J.val t u)
            (Equiv.refl _) sigma tau
            ((e x t u).val,
              (inputStageComplementWord p d r J.val W t u
                (e x t (complement p t u))).val) : ℝ) -
          ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
            (stageCounts27 m p d r W t u sigma : ℝ) *
            (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
            (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2)^4) ≤
        C * (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 := by
  obtain ⟨C,hC,hmoment⟩ :=
    (restricted_matching_fourth_moment (α := Chunk w) (β := Chunk w))
  refine ⟨C,hC,?_⟩
  intro s b m p d hd hb r J W Ω _ hΩ e t u hu hn sigma tau
  have hA : ∀ t u, Nonempty
      (Words (Nat.card (InputStageCellPos p d r J.val t u))
        (stageCounts27 m p d r W t u)) := fun t u =>
    ⟨e (Classical.choice hΩ) t u⟩
  let g : Words (Nat.card (InputStageCellPos p d r J.val t u))
        (stageCounts27 m p d r W t u) →
      Words (Nat.card (InputStageCellPos p d r J.val t (complement p t u)))
        (stageCounts27 m p d r W t (complement p t u)) → ℝ := fun x y =>
    ((restrictedPairCount (inputStageFirstPositions p d r J.val t u)
        (Equiv.refl _) sigma tau
        (x.val,(inputStageComplementWord p d r J.val W t u y).val) : ℝ) -
      ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u sigma : ℝ) *
        (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2)^4
  change avg (fun x : Ω => g (e x t u) (e x t (complement p t u))) ≤ _
  rw [avg_conditioned_pi_pi_apply₂ (fun t : Fin s => ChildShape p t)
    (fun t u => Words (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)) hA e t u
    (complement p t u) hu g]
  let E := Equiv.prodCongr
    (Equiv.refl (Words (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)))
    (inputStageComplementWord p d r J.val W t u)
  let f : PairWords (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)
      (stageCounts27 m p d r W t (complement p t u)) → ℝ := fun z =>
    ((restrictedPairCount (inputStageFirstPositions p d r J.val t u)
        (Equiv.refl _) sigma tau (z.1.val,z.2.val) : ℝ) -
      ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u sigma : ℝ) *
        (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2)^4
  change avg (fun z => f (E z)) ≤
    C * (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2
  rw [inputMoments_avg_equiv E f]
  apply hmoment _ hn _ _
  · exact inputStageCellCounts_sum p d hd hb r J W t u
  · have hs := inputStageCellCounts_sum p d hd hb r J W t
      (complement p t u)
    exact hs.trans (Nat.card_congr (inputStageCellSwap p d r J.val t u).symm)

end
end OmegaBound.ADVXXZGeneral.Grid29
end

