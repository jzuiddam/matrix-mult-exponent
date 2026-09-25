import OmegaBound.ADVXXZGeneralGridInput29TwinInputExactParentMoment

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

private theorem inputParentMarkov_bad_event {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (hP : 0 < StageCandidateRaw.stageParentCount b m p d r t)
    (ε : ℚ) (hε : 0 < ε)
    (a : StageExactPart27 0 b m p d r J.val W)
    (ha : ¬ ApproxConsistent ε (d.betaRegion W t r)
      (fun i => Parent25.paired a.val t i)) :
    ∃ sigma : Chunk (w + w),
      ((ε : ℝ) * StageCandidateRaw.stageParentCount b m p d r t) ≤
        |(inputStagePairCount p d r J.val W a t sigma : ℝ) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℝ) *
            ((d.betaRegion W t r).prob sigma : ℝ)| := by
  simp only [ApproxConsistent] at ha
  push_neg at ha
  obtain ⟨sigma,hsigma⟩ := ha
  refine ⟨sigma,?_⟩
  have hPq : (0 : ℚ) < StageCandidateRaw.stageParentCount b m p d r t := by
    exact_mod_cast hP
  have hdev : ε <
      |(inputStagePairCount p d r J.val W a t sigma : ℚ) /
          StageCandidateRaw.stageParentCount b m p d r t -
        (d.betaRegion W t r).prob sigma| := by
    simpa only [emp, inputStagePairCount, lt_iff_not_ge] using hsigma
  have heq :
      |(inputStagePairCount p d r J.val W a t sigma : ℚ) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℚ) *
            (d.betaRegion W t r).prob sigma| =
        (StageCandidateRaw.stageParentCount b m p d r t : ℚ) *
          |(inputStagePairCount p d r J.val W a t sigma : ℚ) /
              StageCandidateRaw.stageParentCount b m p d r t -
            (d.betaRegion W t r).prob sigma| := by
    calc
      |(inputStagePairCount p d r J.val W a t sigma : ℚ) -
          (StageCandidateRaw.stageParentCount b m p d r t : ℚ) *
            (d.betaRegion W t r).prob sigma| =
        |(StageCandidateRaw.stageParentCount b m p d r t : ℚ) *
          ((inputStagePairCount p d r J.val W a t sigma : ℚ) /
              StageCandidateRaw.stageParentCount b m p d r t -
            (d.betaRegion W t r).prob sigma)| := by
              congr 1
              field_simp
      _ = |(StageCandidateRaw.stageParentCount b m p d r t : ℚ)| *
          |(inputStagePairCount p d r J.val W a t sigma : ℚ) /
              StageCandidateRaw.stageParentCount b m p d r t -
            (d.betaRegion W t r).prob sigma| := abs_mul _ _
      _ = _ := by rw [abs_of_pos hPq]
  have hdev' : ε * (StageCandidateRaw.stageParentCount b m p d r t : ℚ) <
      |(inputStagePairCount p d r J.val W a t sigma : ℚ) -
        (StageCandidateRaw.stageParentCount b m p d r t : ℚ) *
          (d.betaRegion W t r).prob sigma| := by
    rw [heq]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hdev hPq
  exact_mod_cast hdev'.le

/-- Fourth-moment Markov followed by the finite union over paired chunks gives a
uniform bad proportion for approximate consistency in one positive parent cell. -/
theorem inputExactPart_parent_inconsistent_bound {w : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {s b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m)
      (hm : 2 ≤ m) (ε : ℚ) (hε : 0 < ε)
      (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side) (t : Fin s)
      (hP : 0 < StageCandidateRaw.stageParentCount b m p d r t),
      ((Finset.univ.filter fun a : StageExactPart27 0 b m p d r J.val W =>
        ¬ ApproxConsistent ε (d.betaRegion W t r)
          (fun i => Parent25.paired a.val t i)).card : ℝ) /
        Fintype.card (StageExactPart27 0 b m p d r J.val W) ≤
      C / ((ε : ℝ)^4 *
        (StageCandidateRaw.stageParentCount b m p d r t : ℝ)^2) := by
  obtain ⟨Cmoment,hCmoment,hmoment⟩ :=
    (inputExactPart_parent_fourth_moment (w := w))
  let C : ℝ := Fintype.card (Chunk (w + w)) * Cmoment
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s b m p d hd hb hm ε hε r J W t hP
  let Ω := StageExactPart27 0 b m p d r J.val W
  let P : ℕ := StageCandidateRaw.stageParentCount b m p d r t
  let bad : Chunk (w + w) → Finset Ω := fun sigma =>
    Finset.univ.filter fun a =>
      (ε : ℝ) * P ≤ |(inputStagePairCount p d r J.val W a t sigma : ℝ) -
        (P : ℝ) * ((d.betaRegion W t r).prob sigma : ℝ)|
  have hΩ : Nonempty Ω :=
    stageExactPart_nonempty27 0 m p d hd hb r J.val J.property W
  have hΩcard : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr hΩ
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hPmod : 0 < P := hP
  have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
  have hbad_sigma : ∀ sigma : Chunk (w + w),
      ((bad sigma).card : ℝ) / Fintype.card Ω ≤
        Cmoment / ((ε : ℝ)^4 * (P : ℝ)^2) := by
    intro sigma
    have hmark := uniformFourthMoment_markov hΩcard
      (fun a : Ω => (inputStagePairCount p d r J.val W a t sigma : ℝ))
      ((P : ℝ) * ((d.betaRegion W t r).prob sigma : ℝ))
      ((ε : ℝ) * P) (Cmoment * (P : ℝ)^2)
      (mul_pos hεR hPReal)
      (hmoment p d hd hb hm r J W t sigma)
    change ((bad sigma).card : ℝ) / Fintype.card Ω ≤ _
    apply hmark.trans_eq
    field_simp
  have hsub : (Finset.univ.filter fun a : Ω =>
      ¬ ApproxConsistent ε (d.betaRegion W t r)
        (fun i => Parent25.paired a.val t i)) ⊆
      (Finset.univ : Finset (Chunk (w + w))).biUnion bad := by
    intro a ha
    have hna := (Finset.mem_filter.mp ha).2
    obtain ⟨sigma,hsigma⟩ :=
      inputParentMarkov_bad_event p d r J W t hP ε hε a hna
    apply Finset.mem_biUnion.mpr
    exact ⟨sigma,Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hsigma⟩⟩
  have hcard : (Finset.univ.filter fun a : Ω =>
      ¬ ApproxConsistent ε (d.betaRegion W t r)
        (fun i => Parent25.paired a.val t i)).card ≤
      ∑ sigma : Chunk (w + w), (bad sigma).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    ((Finset.univ.filter fun a : Ω =>
        ¬ ApproxConsistent ε (d.betaRegion W t r)
          (fun i => Parent25.paired a.val t i)).card : ℝ) /
        Fintype.card Ω ≤
      (∑ sigma : Chunk (w + w), ((bad sigma).card : ℝ)) /
        Fintype.card Ω := by
          apply div_le_div_of_nonneg_right
          exact_mod_cast hcard
          positivity
    _ = ∑ sigma : Chunk (w + w),
        ((bad sigma).card : ℝ) / Fintype.card Ω := by
          rw [Finset.sum_div]
    _ ≤ ∑ _sigma : Chunk (w + w),
        Cmoment / ((ε : ℝ)^4 * (P : ℝ)^2) :=
      Finset.sum_le_sum fun sigma _ => hbad_sigma sigma
    _ = C / ((ε : ℝ)^4 * (P : ℝ)^2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [C]
      ring

end
end OmegaBound.ADVXXZGeneral.Grid29
end

