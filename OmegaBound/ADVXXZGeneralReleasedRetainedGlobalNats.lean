import OmegaBound.ADVXXZGeneralReleasedRetainedLegs

/-!
# Natural-log forms of the global Y/Z component penalties

The released retained evaluator works in nats, while the paper definitions use base-two
entropy.  These identities isolate that unit conversion before any released finite table is
expanded.
-/

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable def globalEtaNats {w : ℕ} (d : GlobalData w) (r : Fin 6)
    (_xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord zSide u = 0 then
      d.alpha r u * Entropy.H Finset.univ (d.beta ySide r u).probR else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if coord ySide u = a ∧ 0 < coord zSide u then d.alpha r u else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (d.alpha r) (d.beta ySide r)
        (fun u => coord ySide u = a ∧ 0 < coord zSide u))

noncomputable def globalLambdaNats {w : ℕ} (d : GlobalData w) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord xSide u = 0 ∨ coord ySide u = 0 then
      d.alpha r u * Entropy.H Finset.univ (d.beta zSide r u).probR else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a
      then d.alpha r u else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (d.alpha r) (d.beta zSide r)
        (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a))

theorem log_two_mul_entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    Real.log 2 * entropy p = Entropy.H Finset.univ p := by
  rw [mul_comm]
  exact Entropy.H_mul_log_two Finset.univ p

theorem log_two_mul_globalEta {w : ℕ} (d : GlobalData w) (r : Fin 6)
    (xSide ySide zSide : Side) :
    Real.log 2 * globalEta d r xSide ySide zSide =
      globalEtaNats d r xSide ySide zSide := by
  classical
  unfold globalEta globalEtaNats splitEntropy
  rw [mul_add]
  simp_rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs with h
    · calc
        Real.log 2 * (d.alpha r u * entropy (d.beta ySide r u).probR) =
            d.alpha r u * (Real.log 2 * entropy (d.beta ySide r u).probR) := by ring
        _ = _ := by rw [log_two_mul_entropy]
    · simp
  · apply Finset.sum_congr rfl
    intro a _
    dsimp only
    let mass := ∑ u, if coord ySide u = (a : ℕ) ∧ 0 < coord zSide u
      then d.alpha r u else 0
    change Real.log 2 * (mass * entropy
        (weightedSplit (d.alpha r) (d.beta ySide r)
          (fun u => coord ySide u = (a : ℕ) ∧ 0 < coord zSide u))) =
      mass * Entropy.H Finset.univ
        (weightedSplit (d.alpha r) (d.beta ySide r)
          (fun u => coord ySide u = (a : ℕ) ∧ 0 < coord zSide u))
    calc
      Real.log 2 * (mass * entropy
          (weightedSplit (d.alpha r) (d.beta ySide r)
            (fun u => coord ySide u = ↑a ∧ 0 < coord zSide u))) =
          mass * (Real.log 2 * entropy
            (weightedSplit (d.alpha r) (d.beta ySide r)
              (fun u => coord ySide u = ↑a ∧ 0 < coord zSide u))) := by ring
      _ = _ := by rw [log_two_mul_entropy]

theorem log_two_mul_globalLambda {w : ℕ} (d : GlobalData w) (r : Fin 6)
    (xSide ySide zSide : Side) :
    Real.log 2 * globalLambda d r xSide ySide zSide =
      globalLambdaNats d r xSide ySide zSide := by
  classical
  unfold globalLambda globalLambdaNats splitEntropy
  rw [mul_add]
  simp_rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs with h
    · calc
        Real.log 2 * (d.alpha r u * entropy (d.beta zSide r u).probR) =
            d.alpha r u * (Real.log 2 * entropy (d.beta zSide r u).probR) := by ring
        _ = _ := by rw [log_two_mul_entropy]
    · simp
  · apply Finset.sum_congr rfl
    intro a _
    dsimp only
    let mass := ∑ u, if 0 < coord xSide u ∧ 0 < coord ySide u ∧
      coord zSide u = (a : ℕ) then d.alpha r u else 0
    change Real.log 2 * (mass * entropy
        (weightedSplit (d.alpha r) (d.beta zSide r)
          (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧
            coord zSide u = (a : ℕ)))) =
      mass * Entropy.H Finset.univ
        (weightedSplit (d.alpha r) (d.beta zSide r)
          (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧
            coord zSide u = (a : ℕ)))
    calc
      Real.log 2 * (mass * entropy
          (weightedSplit (d.alpha r) (d.beta zSide r)
            (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = ↑a))) =
          mass * (Real.log 2 * entropy
            (weightedSplit (d.alpha r) (d.beta zSide r)
              (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = ↑a))) := by ring
      _ = _ := by rw [log_two_mul_entropy]

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.log_two_mul_entropy
#print axioms OmegaBound.ADVXXZGeneral.log_two_mul_globalEta
#print axioms OmegaBound.ADVXXZGeneral.log_two_mul_globalLambda
