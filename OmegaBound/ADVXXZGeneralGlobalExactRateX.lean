import OmegaBound.ADVXXZGeneralGlobalExactSubadditivity

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem rateX_negMulLog_sum_le27 {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (p : alpha → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∀ a, p a ≤ 1) (S : Finset alpha) :
    Real.negMulLog (∑ a ∈ S, p a) ≤ ∑ a ∈ S, Real.negMulLog (p a) := by
  let q := ∑ a ∈ S, p a
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun a _ => hp0 a
  by_cases hq : q = 0
  · change Real.negMulLog q ≤ _
    rw [hq, Real.negMulLog_zero]
    exact Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hp0 a) (hp1 a)
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    rw [Entropy.negMulLog_eq]
    have hrewrite : -(q * Real.log q) = ∑ a ∈ S, -(p a * Real.log q) := by
      dsimp only [q]
      rw [Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hrewrite]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpapos : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm hpa)
      have hpaq : p a ≤ q := by
        dsimp only [q]
        exact Finset.single_le_sum (fun x _ => hp0 x) ha
      have hlog : Real.log (p a) ≤ Real.log q :=
        Real.strictMonoOn_log.monotoneOn hpapos hqpos hpaq
      rw [Entropy.negMulLog_eq]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hlog (hp0 a))

/-- Entropy cannot increase when a finite probability law is pushed forward along a map. -/
theorem entropy_map_le27 {alpha gamma : Type*}
    [Fintype alpha] [Fintype gamma] [DecidableEq alpha] [DecidableEq gamma]
    (p : alpha → ℝ) (hp : IsProbability p) (f : alpha → gamma) :
    entropy (fun c => ∑ a ∈ (Finset.univ.filter fun a => f a = c), p a) ≤ entropy p := by
  let q := fun c : gamma => ∑ a ∈ (Finset.univ.filter fun a => f a = c), p a
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    calc
      p a ≤ ∑ x, p x := Finset.single_le_sum (fun x _ => hp.1 x) (Finset.mem_univ a)
      _ = 1 := hp.2
  have hfiber :
      (∑ c ∈ (Finset.univ : Finset gamma),
          ∑ a ∈ (Finset.univ.filter fun a => f a = c), Real.negMulLog (p a)) =
        ∑ a ∈ (Finset.univ : Finset alpha), Real.negMulLog (p a) :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset alpha)) (t := (Finset.univ : Finset gamma))
      (g := f) (fun a _ => Finset.mem_univ (f a)) (fun a => Real.negMulLog (p a))
  have hH : Entropy.H (Finset.univ : Finset gamma) q ≤
      Entropy.H (Finset.univ : Finset alpha) p := by
    unfold Entropy.H
    calc
      (∑ c ∈ (Finset.univ : Finset gamma), Real.negMulLog (q c)) ≤
          ∑ c ∈ (Finset.univ : Finset gamma),
            ∑ a ∈ (Finset.univ.filter fun a => f a = c), Real.negMulLog (p a) := by
        apply Finset.sum_le_sum
        intro c _
        exact rateX_negMulLog_sum_le27 p hp.1 hp1 _
      _ = ∑ a ∈ (Finset.univ : Finset alpha), Real.negMulLog (p a) := hfiber
  unfold entropy Entropy.H₂
  exact div_le_div_of_nonneg_right hH (Real.log_pos one_lt_two).le

/-- Every shape-coordinate marginal has entropy at most the joint shape entropy. -/
theorem marginal_entropy_le27 {w : ℕ} (P : RatDist (Shape w)) (S : Side) :
    entropy (marginal P.probR S) ≤ entropy P.probR := by
  let f := fun u : Shape w => Parent25.coordFin S u
  have hmap := entropy_map_le27 P.probR ⟨P.probR_nonneg, P.sum_probR⟩ f
  rw [← marginal_eq_fiberSum27 P.probR S]
  exact hmap

set_option maxHeartbeats 1000000 in
-- The supremum proof needs to elaborate the finite shape marginal functions several times.
theorem penalty_le_marginal_entropy27 {w : ℕ} (P : RatDist (Shape w)) (X : Side) :
    penalty P.probR ≤ entropy (marginal P.probR X) := by
  set S : Set ℝ := {h : ℝ | ∃ p' : Shape w → ℝ,
    IsProbability p' ∧ SameMarginals P.probR p' ∧ h = entropy p'} with hSdef
  have hmem_iff (h : ℝ) : h ∈ S ↔ ∃ p' : Shape w → ℝ,
      IsProbability p' ∧ SameMarginals P.probR p' ∧ h = entropy p' := by
    simp only [hSdef, Set.mem_setOf_eq]
  have hpen : penalty P.probR = sSup S - entropy P.probR := by
    unfold penalty
    rw [hSdef]
  have hp : IsProbability P.probR := ⟨P.probR_nonneg, P.sum_probR⟩
  have hmem : entropy P.probR ∈ S :=
    (hmem_iff _).mpr ⟨P.probR, hp, fun _ _ => rfl, rfl⟩
  clear_value S
  have hsup : sSup S ≤
      entropy (marginal P.probR X) + entropy P.probR := by
    apply csSup_le ⟨entropy P.probR, hmem⟩
    intro h hh
    rcases (hmem_iff h).mp hh with ⟨p', hp', hsame, rfl⟩
    have hsame_entropy (W : Side) :
        entropy (marginal p' W) = entropy (marginal P.probR W) := by
      apply congrArg entropy
      funext a
      exact (hsame W a).symm
    have hbound (Y : Side) (hXY : X ≠ Y) :
        entropy p' ≤ entropy (marginal P.probR X) + entropy P.probR := by
      calc
        entropy p' ≤ entropy (marginal p' X) + entropy (marginal p' Y) :=
          entropy_le_add_marginals27 p' hp'.1 hp'.2 X Y hXY
        _ = entropy (marginal P.probR X) + entropy (marginal P.probR Y) := by
          rw [hsame_entropy X, hsame_entropy Y]
        _ ≤ entropy (marginal P.probR X) + entropy P.probR := by
          exact add_le_add_right (marginal_entropy_le27 P Y) _
    cases X with
    | X => exact hbound .Y (by decide +kernel)
    | Y => exact hbound .Z (by decide +kernel)
    | Z => exact hbound .X (by decide +kernel)
  rw [hpen]
  linarith

/-- The X branch of the paper's regional rate is nonnegative. -/
theorem globalRegionRate_x_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    0 ≤ entropy (marginal (g.alpha r).probR (g.perm r .X)) -
      penalty ((g.alpha r).probR) := by
  have h := penalty_le_marginal_entropy27 (g.alpha r) (g.perm r .X)
  linarith

end
end OmegaBound.ADVXXZGeneral
end
