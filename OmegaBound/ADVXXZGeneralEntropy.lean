import OmegaBound.ADVXXZGeneralRates
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Topology.ContinuousMap.Compact

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem entropy_dual_sound {α J : Type*} [Fintype α] [Fintype J]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (feature : α → J → ℝ) (u : J → ℝ) :
  entropyNats p ≤ Real.log (∑ a, Real.exp (∑ j, u j*feature a j)) -
    ∑ j, u j*(∑ a, p a*feature a j) := by
  classical
  let score : α → ℝ := fun a => ∑ j, u j * feature a j
  let Z : ℝ := ∑ a, Real.exp (score a)
  have huniv : (Finset.univ : Finset α).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
    simp at hsum
  have hZ : 0 < Z := Finset.sum_pos (fun a _ => Real.exp_pos (score a)) huniv
  let q : α → ℝ := fun a => Real.exp (score a) / Z
  have hq (a : α) : 0 < q a := div_pos (Real.exp_pos _) hZ
  have hqsum : ∑ a, q a = 1 := by
    dsimp [q]
    rw [← Finset.sum_div, show (∑ a, Real.exp (score a)) = Z from rfl]
    exact div_self hZ.ne'
  have hterm (a : α) :
      q a * InformationTheory.klFun (p a / q a) =
        p a * Real.log (p a) - p a * Real.log (q a) + q a - p a := by
    by_cases hpa : p a = 0
    · simp [hpa, InformationTheory.klFun]
    · rw [InformationTheory.klFun_apply, Real.log_div hpa (hq a).ne']
      field_simp [(hq a).ne']
  have hkl : 0 ≤ ∑ a, q a * InformationTheory.klFun (p a / q a) :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (hq a).le
        (InformationTheory.klFun_nonneg (div_nonneg (hp a) (hq a).le))
  have hcross :
      0 ≤ (∑ a, p a * Real.log (p a)) - ∑ a, p a * Real.log (q a) := by
    rw [Finset.sum_congr rfl fun a _ => hterm a] at hkl
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hqsum, hsum] at hkl
    linarith
  have hlogq (a : α) : Real.log (q a) = score a - Real.log Z := by
    dsimp [q]
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hweighted :
      (∑ a, p a * Real.log (q a)) = (∑ a, p a * score a) - Real.log Z := by
    simp_rw [hlogq]
    calc
      (∑ a, p a * (score a - Real.log Z)) =
          (∑ a, p a * score a) - (∑ a, p a) * Real.log Z := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = (∑ a, p a * score a) - Real.log Z := by rw [hsum, one_mul]
  have hscore :
      (∑ a, p a * score a) = ∑ j, u j * (∑ a, p a * feature a j) := by
    dsimp [score]
    calc
      (∑ a, p a * ∑ j, u j * feature a j) =
          ∑ a, ∑ j, p a * (u j * feature a j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ a, p a * (u j * feature a j) := Finset.sum_comm
      _ = ∑ j, u j * (∑ a, p a * feature a j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
  rw [hweighted, hscore] at hcross
  dsimp [entropyNats, Z]
  linarith

private abbrev EntropyCube (α : Type*) := α → Set.Icc (0 : ℝ) 1

private noncomputable def entropyCubeMap {α : Type*} [Fintype α] :
    C(EntropyCube α, ℝ) where
  toFun p := entropyNats fun a => p a
  continuous_toFun := by
    unfold entropyNats
    fun_prop

private def entropyOscillation {α : Type*} [Fintype α] (ε : ℚ) : Set ℝ :=
  {z | z = 0 ∨ ∃ p q : EntropyCube α,
    (∀ a, dist (p a) (q a) ≤ (ε : ℝ)) ∧
      z = dist (entropyCubeMap p) (entropyCubeMap q)}

private noncomputable def entropyModulus {α : Type*} [Fintype α] (ε : ℚ) : ℝ :=
  sSup (entropyOscillation (α := α) ε)

private lemma entropyOscillation_nonempty {α : Type*} [Fintype α] (ε : ℚ) :
    (entropyOscillation (α := α) ε).Nonempty :=
  ⟨0, Or.inl rfl⟩

private lemma entropyOscillation_bddAbove {α : Type*} [Fintype α] (ε : ℚ) :
    BddAbove (entropyOscillation (α := α) ε) := by
  have hrange : Bornology.IsBounded (Set.range (entropyCubeMap (α := α))) :=
    (isCompact_range (entropyCubeMap (α := α)).continuous).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hrange
  let z : EntropyCube α := fun _ => ⟨0, le_rfl, zero_le_one⟩
  have hC0 : 0 ≤ C := by simpa using hC z z
  refine ⟨C, ?_⟩
  intro z hz
  rcases hz with rfl | ⟨p, q, _, rfl⟩
  · exact hC0
  · exact hC p q

private lemma entropyModulus_nonneg {α : Type*} [Fintype α] (ε : ℚ) :
    0 ≤ entropyModulus (α := α) ε := by
  exact le_csSup (entropyOscillation_bddAbove (α := α) ε) (Or.inl rfl)

private lemma entropyModulus_vanishes {α : Type*} [Fintype α] :
    VanishesWithTolerance (entropyModulus (α := α)) := by
  constructor
  · exact entropyModulus_nonneg
  · intro η hη
    obtain ⟨d, hd, hmap⟩ := (entropyCubeMap (α := α)).uniform_continuity η hη
    obtain ⟨ε₀, hε₀, hε₀d⟩ := exists_pos_rat_lt hd
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε hε hεle
    rw [abs_of_nonneg (entropyModulus_nonneg ε)]
    unfold entropyModulus
    refine csSup_le (entropyOscillation_nonempty ε) ?_
    intro z hz
    rcases hz with rfl | ⟨p, q, hpq, rfl⟩
    · exact hη.le
    · exact (hmap ((dist_pi_lt_iff hd).2 fun a =>
        (hpq a).trans_lt ((Rat.cast_le.mpr hεle).trans_lt hε₀d))).le

theorem entropy_uniform_continuity {α : Type*} [Fintype α] :
  ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
    ∀ (ε : ℚ), 0 < ε → ∀ (p q : α → ℝ),
      (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ q a) →
      (∑ a, p a = 1) → (∑ a, q a = 1) →
      (∀ a, |p a-q a| ≤ ε) → |entropyNats p-entropyNats q| ≤ delta ε := by
  classical
  refine ⟨entropyModulus (α := α), entropyModulus_vanishes (α := α), ?_⟩
  intro ε hε p q hp hq hpsum hqsum hpq
  have hp_one (a : α) : p a ≤ 1 := by
    calc
      p a ≤ ∑ x, p x := Finset.single_le_sum (fun x _ => hp x) (Finset.mem_univ a)
      _ = 1 := hpsum
  have hq_one (a : α) : q a ≤ 1 := by
    calc
      q a ≤ ∑ x, q x := Finset.single_le_sum (fun x _ => hq x) (Finset.mem_univ a)
      _ = 1 := hqsum
  let p' : EntropyCube α := fun a => ⟨p a, hp a, hp_one a⟩
  let q' : EntropyCube α := fun a => ⟨q a, hq a, hq_one a⟩
  have hmem : dist (entropyCubeMap p') (entropyCubeMap q') ∈
      entropyOscillation (α := α) ε := by
    right
    refine ⟨p', q', ?_, rfl⟩
    intro a
    simpa [Real.dist_eq] using hpq a
  have hbound := le_csSup (entropyOscillation_bddAbove (α := α) ε) hmem
  simpa [p', q', entropyCubeMap, Real.dist_eq] using hbound

end OmegaBound.ADVXXZGeneral
end
