import OmegaBound.ADVXXZGeneralGridInput29TwinInputParentMarkov
import OmegaBound.ADVXXZGeneralInputTransportCont3

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

private theorem inputKeep_parentCount_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (t : Fin s) :
    Parent25.parentCount p d b m r t =
      StageCandidateRaw.stageParentCount b m p d r t := by
  rfl

private theorem inputKeep_parent_ge_multiplier {w s b m : ℕ}
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

private theorem inputKeep_failure_has_inconsistent_parent {w s b m : ℕ} {ε : ℚ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (a : StageExactPart27 0 b m p d r J.val W)
    (ha : ¬ Parent25.inputPartKeep p d b m ε r W a.val) :
    ∃ t : Fin s,
      0 < StageCandidateRaw.stageParentCount b m p d r t ∧
      ¬ ApproxConsistent ε (d.betaRegion W t r)
        (fun i => Parent25.paired a.val t i) := by
  by_contra hnone
  push_neg at hnone
  apply ha
  intro t
  by_cases hP : StageCandidateRaw.stageParentCount b m p d r t = 0
  · left
    exact hP
  · right
    refine ⟨hnone t (Nat.pos_of_ne_zero hP), ?_, ?_⟩
    · simpa only [inputKeep_parentCount_eq] using
        (inputExactPart_region_num_ne p d hd r J W a t)
    · cases W <;> simpa only [inputKeep_parentCount_eq] using
        (inputExactPart_region_grade p d hd r J _ a t)

/-- Taking the finite union over all fixed parent cells preserves inverse-square
concentration, uniformly over roles, alpha labels, and physical sides. -/
theorem inputExactPart_not_keep_bound {w s : ℕ}
    (ε : ℚ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m), 2 ≤ m →
      ∀ (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side),
      ((Finset.univ.filter fun a : StageExactPart27 0 b m p d r J.val W =>
        ¬ Parent25.inputPartKeep p d b m ε r W a.val).card : ℝ) /
        Fintype.card (StageExactPart27 0 b m p d r J.val W) ≤
      C / (m : ℝ)^2 := by
  obtain ⟨Cparent,hCparent,hparent⟩ :=
    (inputExactPart_parent_inconsistent_bound (w := w))
  let C : ℝ := 1 + (s : ℝ) * Cparent / (ε : ℝ)^4
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b m p d hd hb hm r J W
  let Ω := StageExactPart27 0 b m p d r J.val W
  let P : Fin s → ℕ := fun t =>
    StageCandidateRaw.stageParentCount b m p d r t
  let bad : Fin s → Finset Ω := fun t =>
    if hPt : 0 < P t then
      Finset.univ.filter fun a =>
        ¬ ApproxConsistent ε (d.betaRegion W t r)
          (fun i => Parent25.paired a.val t i)
    else ∅
  have hΩ : Nonempty Ω :=
    stageExactPart_nonempty27 0 m p d hd hb r J.val J.property W
  have hΩcard : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr hΩ
  have hbad_t : ∀ t : Fin s,
      ((bad t).card : ℝ) / Fintype.card Ω ≤
        Cparent / ((ε : ℝ)^4 * (m : ℝ)^2) := by
    intro t
    by_cases hPt : 0 < P t
    · have ht := hparent p d hd hb hm ε hε r J W t hPt
      have hPm : m ≤ P t := inputKeep_parent_ge_multiplier p d hb r t hm hPt
      have hPmR : (m : ℝ) ≤ P t := by exact_mod_cast hPm
      rw [show bad t = Finset.univ.filter fun a : Ω =>
          ¬ ApproxConsistent ε (d.betaRegion W t r)
            (fun i => Parent25.paired a.val t i) by simp [bad,hPt]]
      apply ht.trans
      apply div_le_div_of_nonneg_left hCparent.le
      · positivity
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hPmR 2
    · rw [show bad t = ∅ by simp [bad,hPt]]
      simp
      positivity
  have hsub : (Finset.univ.filter fun a : Ω =>
      ¬ Parent25.inputPartKeep p d b m ε r W a.val) ⊆
      (Finset.univ : Finset (Fin s)).biUnion bad := by
    intro a ha
    obtain ⟨t,hPt,ht⟩ := inputKeep_failure_has_inconsistent_parent
      p d hd r J W a (Finset.mem_filter.mp ha).2
    apply Finset.mem_biUnion.mpr
    have hPt' : 0 < P t := hPt
    refine ⟨t,Finset.mem_univ _,?_⟩
    rw [show bad t = Finset.univ.filter fun a : Ω =>
        ¬ ApproxConsistent ε (d.betaRegion W t r)
          (fun i => Parent25.paired a.val t i) by simp [bad,hPt']]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
  have hcard : (Finset.univ.filter fun a : Ω =>
      ¬ Parent25.inputPartKeep p d b m ε r W a.val).card ≤
      ∑ t : Fin s, (bad t).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    ((Finset.univ.filter fun a : Ω =>
        ¬ Parent25.inputPartKeep p d b m ε r W a.val).card : ℝ) /
        Fintype.card Ω ≤
      (∑ t : Fin s, ((bad t).card : ℝ)) / Fintype.card Ω := by
        apply div_le_div_of_nonneg_right
        exact_mod_cast hcard
        positivity
    _ = ∑ t : Fin s, ((bad t).card : ℝ) / Fintype.card Ω := by
      rw [Finset.sum_div]
    _ ≤ ∑ _t : Fin s, Cparent / ((ε : ℝ)^4 * (m : ℝ)^2) :=
      Finset.sum_le_sum fun t _ => hbad_t t
    _ ≤ C / (m : ℝ)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [C]
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      field_simp
      nlinarith [pow_pos hεR 4]

end
end OmegaBound.ADVXXZGeneral.Grid29
end

