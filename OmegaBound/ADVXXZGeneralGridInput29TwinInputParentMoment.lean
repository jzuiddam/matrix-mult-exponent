import OmegaBound.ADVXXZGeneralGridInput29TwinInputCellMoment

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
/-- A physical child cell contains at most the two coordinates belonging to
each parent position. -/
theorem inputStageCell_card_le_two_parent {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    Nat.card (InputStageCellPos p d r J.val t u) ≤
      2 * StageCandidateRaw.stageParentCount b m p d r t := by
  calc
    Nat.card (InputStageCellPos p d r J.val t u) ≤
        Nat.card (Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :=
      Nat.card_le_card_of_injective (fun z => z.val)
        (fun x y h => Subtype.ext h)
    _ = StageCandidateRaw.stageParentCount b m p d r t * 2 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_fin]
    _ = 2 * StageCandidateRaw.stageParentCount b m p d r t := by omega

private theorem inputParentMoment_parent_ge_multiplier {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : InputInt29 d b m) (r : Fin 6) (t : Fin s)
    (hm : 2 ≤ m)
    (hP : 0 < StageCandidateRaw.stageParentCount b m p d r t) :
    m ≤ StageCandidateRaw.stageParentCount b m p d r t := by
  obtain ⟨c,hc⟩ := inputStageParentCount_multiple p d m hb r t
  have hcpos : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    rw [hc, this] at hP
    simp at hP
  calc
    m = m*1 := by omega
    _ ≤ m*c := Nat.mul_le_mul_left m hcpos
    _ = _ := hc.symm

set_option maxHeartbeats 2000000 in
/-- The fourth moment of every paired-chunk count in one parent cell is bounded
uniformly over roles, exact alpha labels, physical sides, and conditioning fibres.
Its centre is the product frequency prescribed by `betaRegion`. -/
theorem inputConditionedParent_fourth_moment {w : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {s b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m)
      (hm : 2 ≤ m) (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
      (Ω : Type*) [Fintype Ω] (hΩ : Nonempty Ω)
      (e : Ω ≃ ((t : Fin s) → (u : ChildShape p t) →
        Words (Nat.card (InputStageCellPos p d r J.val t u))
          (stageCounts27 m p d r W t u)))
      (t : Fin s) (sigma : Chunk (w + w)),
      avg (fun x : Ω =>
        ((∑ u : ChildShape p t,
            (inputProductCellCount p d r J.val W (e x) t u
              (leftHalf sigma) (rightHalf sigma) : ℝ)) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
            ((d.betaRegion W t r).prob sigma : ℝ))^4) ≤
        C * (StageCandidateRaw.stageParentCount b m p d r t : ℝ)^2 := by
  obtain ⟨Ccell,hCcell,hcell⟩ :=
    (inputConditionedCell_fourth_moment (w := w))
  let L : ℝ := Fintype.card (Shape w)
  let C : ℝ := 1 + 8 * L^4 * (4*Ccell + 16)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s b m p d hd hb hm r J W Ω _ hΩ e t sigma
  let P : ℕ := StageCandidateRaw.stageParentCount b m p d r t
  let N : ChildShape p t → ℕ := fun u =>
    Nat.card (InputStageCellPos p d r J.val t u)
  let X : ChildShape p t → Ω → ℝ := fun u x =>
    inputProductCellCount p d r J.val W (e x) t u
      (leftHalf sigma) (rightHalf sigma)
  let mu : ChildShape p t → ℝ := fun u =>
    inputProductCellMean p d r J.val W t u
      (leftHalf sigma) (rightHalf sigma)
  let nu : ChildShape p t → ℝ := fun u =>
    inputProductCellTarget p d r J.val W t u
      (leftHalf sigma) (rightHalf sigma)
  let D : ChildShape p t → ℝ := fun u => if N u = 0 then 0 else 2
  have hΩcard : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr hΩ
  have hmoment : ∀ u, avg (fun x => (X u x - mu u)^4) ≤
      Ccell * (N u : ℝ)^2 := by
    intro u
    exact hcell p d hd hb r J W Ω hΩ e t u
      (leftHalf sigma) (rightHalf sigma)
  have hcenter : ∀ u, |mu u - nu u| ≤ D u := by
    intro u
    by_cases hzero : N u = 0
    · have hz := inputProductCellMean_eq_target_of_card_zero p d r J W t u
        hzero (leftHalf sigma) (rightHalf sigma)
      have hmuz : mu u = nu u := hz
      rw [hmuz]
      simp [D, hzero]
    · simpa only [D, if_neg hzero] using
        (inputProductCellMean_sub_target_abs_le_two_all p d hd hb hm r J W t u
          (leftHalf sigma) (rightHalf sigma))
  have hagg := avg_sum_fourth_moment_of_local hΩcard X mu nu
    (fun u => Ccell * (N u : ℝ)^2) D hmoment hcenter
  have hcenters : (∑ u : ChildShape p t, nu u) =
      (P : ℝ) * ((d.betaRegion W t r).prob sigma : ℝ) := by
    exact inputStageProductCenters_sum p d hd hb r J W t sigma
  rw [hcenters] at hagg
  change avg (fun x : Ω =>
      ((∑ u : ChildShape p t, X u x) -
        (P : ℝ) * ((d.betaRegion W t r).prob sigma : ℝ))^4) ≤
    C * (P : ℝ)^2
  apply hagg.trans
  by_cases hPzero : P = 0
  · have hNzero : ∀ u, N u = 0 := by
      intro u
      have hle := inputStageCell_card_le_two_parent p d r J t u
      dsimp [N, P] at hle ⊢
      omega
    have hDzero : ∀ u, D u = 0 := by
      intro u
      simp [D,hNzero u]
    simp only [P, hPzero, Nat.cast_zero]
    simp_rw [hNzero,hDzero]
    norm_num
  · have hP : 0 < P := Nat.pos_of_ne_zero hPzero
    have hPone : (1 : ℝ) ≤ (P : ℝ)^2 := by
      have : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
      nlinarith [sq_nonneg (P : ℝ)]
    have hI : (Fintype.card (ChildShape p t) : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast (Fintype.card_subtype_le
        (p := fun u : Shape w =>
          coord .X u ≤ p.i t ∧ coord .Y u ≤ p.j t ∧ coord .Z u ≤ p.k t))
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hIPow : (Fintype.card (ChildShape p t) : ℝ)^3 ≤ L^3 := by
      exact pow_le_pow_left₀ (by positivity) hI 3
    have hNbound : ∀ u, (N u : ℝ)^2 ≤ (2*(P : ℝ))^2 := by
      intro u
      have hle := inputStageCell_card_le_two_parent p d r J t u
      have hleR : (N u : ℝ) ≤ 2*(P : ℝ) := by
        dsimp [N,P]
        exact_mod_cast hle
      exact pow_le_pow_left₀ (by positivity) hleR 2
    calc
      (Fintype.card (ChildShape p t) : ℝ)^3 *
          ∑ u : ChildShape p t, 8 *
            (Ccell * (N u : ℝ)^2 + (D u)^4) ≤
        (Fintype.card (ChildShape p t) : ℝ)^3 *
          ∑ _u : ChildShape p t, 8 *
            (Ccell * (2*(P : ℝ))^2 + 16) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hNbound u) hCcell.le
          · dsimp [D]
            split_ifs <;> norm_num
      _ = (Fintype.card (ChildShape p t) : ℝ)^4 *
          8 * (4*Ccell*(P : ℝ)^2 + 16) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ ≤ L^4 * 8 * (4*Ccell*(P : ℝ)^2 + 16) := by
          have hI4 : (Fintype.card (ChildShape p t) : ℝ)^4 ≤ L^4 :=
            pow_le_pow_left₀ (by positivity) hI 4
          gcongr
      _ ≤ C * (P : ℝ)^2 := by
          dsimp [C]
          have hC0 : 0 ≤ Ccell := hCcell.le
          nlinarith [sq_nonneg (L^2), sq_nonneg (P : ℝ)]

end
end OmegaBound.ADVXXZGeneral.Grid29
end

