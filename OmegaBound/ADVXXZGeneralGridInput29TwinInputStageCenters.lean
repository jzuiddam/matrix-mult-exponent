import OmegaBound.ADVXXZGeneralInputCellAggregation
import OmegaBound.ADVXXZGeneralGridInput29TwinInputCellGeometry

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

private theorem inputCenters_floor_nat (n : ℕ) :
    ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem inputCenters_alphaCount_cast_q {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : InputInt29 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (StageCandidateRaw.stageAlphaCount b m p d r t v : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob v := by
  rcases hb.alphaIntegral t r v with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) *
          (d.A t).prob r * (d.alpha t r).prob v = (m * n : ℕ) := by
    calc
      _ = (m : ℚ) * ((b : ℚ) * p.baseN t *
          (d.A t).prob r * (d.alpha t r).prob v) := by
        push_cast
        ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = (m * n : ℕ) := by norm_cast
  unfold StageCandidateRaw.stageAlphaCount
  rw [hscaled, inputCenters_floor_nat]

private theorem inputCenters_stageCount_cast_q {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : InputInt29 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) (sigma : Chunk w) :
    (stageCounts27 m p d r W t u sigma : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ *
        (d.betaChild W t r u).prob sigma := by
  exact hb.countsExact r W t u sigma

/-- The canonical first-half coordinates in a target cell have exactly the
prescribed alpha multiplicity. -/
theorem inputStageFirstPositions_card {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    (inputStageFirstPositions p d r J.val t u).card =
      StageCandidateRaw.stageAlphaCount b m p d r t u := by
  let e := Finite.equivFin (InputStageCellPos p d r J.val t u)
  have hcard : (inputStageFirstPositions p d r J.val t u).card =
      (Finset.univ.filter fun i :
        Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          stageColour27 0 b m p d r J.val t (i, 0) = u).card := by
    refine Finset.card_bij (fun q _ => (e.symm q).val.1) ?_ ?_ ?_
    · intro q hq
      have hh : (e.symm q).val.2 = 0 := by
        simpa only [inputStageFirstPositions, Finset.mem_filter,
          Finset.mem_univ, true_and, e] using hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hz : (e.symm q).val = ((e.symm q).val.1, 0) :=
        Prod.ext rfl hh
      rw [← hz]
      exact (e.symm q).property
    · intro q₁ hq₁ q₂ hq₂ heq
      apply e.symm.injective
      apply Subtype.ext
      apply Prod.ext heq
      have h₁ : (e.symm q₁).val.2 = 0 := by
        simpa only [inputStageFirstPositions, Finset.mem_filter,
          Finset.mem_univ, true_and, e] using hq₁
      have h₂ : (e.symm q₂).val.2 = 0 := by
        simpa only [inputStageFirstPositions, Finset.mem_filter,
          Finset.mem_univ, true_and, e] using hq₂
      exact h₁.trans h₂.symm
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      let z : InputStageCellPos p d r J.val t u := ⟨(i,0),hi'⟩
      refine ⟨e z, ?_, ?_⟩
      · simp only [inputStageFirstPositions, Finset.mem_filter,
          Finset.mem_univ, true_and, e, Equiv.symm_apply_apply]
        rfl
      · simp only [e, Equiv.symm_apply_apply, z]
  rw [hcard]
  exact (Finset.mem_filter.mp J.property).2 t u

/-- The cardinality of an actual child cell is its natural output multiplicity. -/
theorem inputStageCell_card {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) :
    Nat.card (InputStageCellPos p d r J.val t u) =
      m * d.outBase ⟨t,r,u⟩ := by
  rw [← inputStageCellCounts_sum p d hd hb r J W t u]
  exact stageCounts27_sum p d hb r W t u

/-- Every exact child-symbol count is its cell cardinality times the fixed child
probability. -/
theorem inputStageCount_cast {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma : Chunk w) :
    (stageCounts27 m p d r W t u sigma : ℝ) =
      (Nat.card (InputStageCellPos p d r J.val t u) : ℝ) *
        ((d.betaChild W t r u).prob sigma : ℝ) := by
  have hq := inputCenters_stageCount_cast_q p d m hb r W t u sigma
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  rw [inputStageCell_card p d hd hb r J W t u]
  simpa only [Rat.cast_mul, Rat.cast_natCast, Nat.cast_mul] using hr

/-- A first-half cell multiplicity is the parent count times its alpha mass. -/
theorem inputStageFirstPositions_cast {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : InputInt29 d b m) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    ((inputStageFirstPositions p d r J.val t u).card : ℝ) =
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        ((d.alpha t r).prob u : ℝ) := by
  have halpha := inputCenters_alphaCount_cast_q p d m hb r t u
  have hparent :
      (StageCandidateRaw.stageParentCount b m p d r t : ℚ) =
        ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r := by
    unfold StageCandidateRaw.stageParentCount
    rw [Nat.cast_sum]
    simp_rw [inputCenters_alphaCount_cast_q p d m hb r t]
    rw [← Finset.mul_sum, RatDist.sum_prob]
    ring
  rw [inputStageFirstPositions_card p d r J t u]
  have halphaR := congrArg (fun x : ℚ => (x : ℝ)) halpha
  have hparentR := congrArg (fun x : ℚ => (x : ℝ)) hparent
  simp only [Rat.cast_mul, Rat.cast_natCast] at halphaR hparentR ⊢
  rw [halphaR, hparentR]

/-- Every alpha-cell multiplicity scales exactly by the supplied multiplier. -/
theorem inputStageAlphaCount_multiple {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : InputInt29 d b m) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) :
    ∃ c : ℕ, StageCandidateRaw.stageAlphaCount b m p d r t u = m*c := by
  rcases hb.alphaIntegral t r u with ⟨c,hc⟩
  refine ⟨c,?_⟩
  apply Nat.cast_injective (R := ℚ)
  rw [inputCenters_alphaCount_cast_q p d m hb r t u, Nat.cast_mul]
  push_cast
  calc
    (b : ℚ) * m * p.baseN t * (d.A t).prob r *
        (d.alpha t r).prob u =
        (m : ℚ) * ((b : ℚ) * p.baseN t * (d.A t).prob r *
          (d.alpha t r).prob u) := by ring
    _ = (m : ℚ) * c := by rw [hc]

/-- Every parent-cell length is an exact multiple of the supplied multiplier. -/
theorem inputStageParentCount_multiple {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : InputInt29 d b m) (r : Fin 6) (t : Fin s) :
    ∃ c : ℕ, StageCandidateRaw.stageParentCount b m p d r t = m*c := by
  classical
  choose c hc using fun u : ChildShape p t =>
    inputStageAlphaCount_multiple p d m hb r t u
  refine ⟨∑ u, c u,?_⟩
  unfold StageCandidateRaw.stageParentCount
  simp_rw [hc]
  exact (Finset.mul_sum (s := Finset.univ) (f := c) m).symm

/-- The product-frequency centre of one oriented physical cell is the alpha-weighted
child product appearing in the constituent pair-mixture law. -/
theorem inputStageProductCenter_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma tau : Chunk w) :
    ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u sigma : ℝ) *
        (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 =
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        ((d.alpha t r).prob u : ℝ) *
        ((d.betaChild W t r u).prob sigma : ℝ) *
        ((d.betaChild W t r (complement p t u)).prob tau : ℝ) := by
  have hswap : Nat.card
      (InputStageCellPos p d r J.val t (complement p t u)) =
        Nat.card (InputStageCellPos p d r J.val t u) :=
    Nat.card_congr (inputStageCellSwap p d r J.val t u).symm
  rw [inputStageCount_cast p d hd hb r J W t u sigma,
    inputStageCount_cast p d hd hb r J W t (complement p t u) tau,
    hswap, inputStageFirstPositions_cast p d hb r J t u]
  by_cases hN :
      (Nat.card (InputStageCellPos p d r J.val t u) : ℝ) = 0
  · have hS :
        (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
          ((d.alpha t r).prob u : ℝ) = 0 := by
      rw [← inputStageFirstPositions_cast p d hb r J t u]
      have hc : (inputStageFirstPositions p d r J.val t u).card ≤
          Nat.card (InputStageCellPos p d r J.val t u) := by
        simpa only [Fintype.card_fin] using
          (inputStageFirstPositions p d r J.val t u).card_le_univ
      have hNnat : Nat.card (InputStageCellPos p d r J.val t u) = 0 := by
        exact_mod_cast hN
      have : (inputStageFirstPositions p d r J.val t u).card = 0 := by omega
      simp [this]
    rw [hN]
    norm_num [hS]
  · field_simp [hN]

/-- Summing the oriented cell product centres gives exactly the prescribed regional
parent frequency. -/
theorem inputStageProductCenters_sum {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (sigma : Chunk (w+w)) :
    (∑ u : ChildShape p t,
      ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u (leftHalf sigma) : ℝ) *
        (stageCounts27 m p d r W t (complement p t u) (rightHalf sigma) : ℝ) /
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2) =
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        ((d.betaRegion W t r).prob sigma : ℝ) := by
  simp_rw [inputStageProductCenter_eq p d hd hb r J W t]
  rw [show (∑ u : ChildShape p t,
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        ((d.alpha t r).prob u : ℝ) *
        ((d.betaChild W t r u).prob (leftHalf sigma) : ℝ) *
        ((d.betaChild W t r (complement p t u)).prob (rightHalf sigma) : ℝ)) =
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
        ∑ u : ChildShape p t,
          ((d.alpha t r).prob u : ℝ) *
          ((d.betaChild W t r u).prob (leftHalf sigma) : ℝ) *
          ((d.betaChild W t r (complement p t u)).prob (rightHalf sigma) : ℝ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring]
  have hp := congrArg (fun x : ℚ => (x : ℝ)) (hd.pair_mixture W t r sigma)
  simpa only [Rat.cast_mul, Rat.cast_sum] using
    (congrArg (fun x : ℝ =>
      (StageCandidateRaw.stageParentCount b m p d r t : ℝ) * x) hp).symm

end
end OmegaBound.ADVXXZGeneral.Grid29
end

