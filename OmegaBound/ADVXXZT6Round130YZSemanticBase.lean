import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round61ReleasedCountProbe
import OmegaBound.ADVXXZT6Round82RealDisintegration
import Mathlib.Topology.Instances.Rat

/-!
# Nats forms of the paper Y/Z rows

The paper declarations use base-two entropy.  These definitions expose the identical finite
expressions in nats, so later exact table transport never mixes units.
-/

set_option maxRecDepth 1000000
set_library_suggestions Lean.LibrarySuggestions.empty

open Finset

namespace OmegaBound.ADVXXZT6Round130

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT9R16PositiveParents (releasedPositiveInput)

noncomputable def splitEntropyNats130 {w : Nat}
    (b : OmegaBound.ADVXXZ.SplitDist w) : Real :=
  Entropy.H Finset.univ b.probR

noncomputable def constituentEtaNats130
    (d : ConstituentData releasedPositiveInput) (p : Fin 126) (r : Fin 6)
    (_xSide ySide zSide : Side) : Real :=
  (∑ u, if coord zSide u.1 = 0 then
      symWeight d p r u * splitEntropyNats130 (d.betaChild ySide p r u) else 0) +
  ∑ a : Fin 5,
    let mass := ∑ u, if coord ySide u.1 = (a : Nat) ∧ 0 < coord zSide u.1
      then symWeight d p r u else 0
    mass * Entropy.H Finset.univ
      (constituentAverage d p r ySide ySide zSide a)

noncomputable def constituentLambdaNats130
    (d : ConstituentData releasedPositiveInput) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) : Real :=
  (∑ u, if coord xSide u.1 = 0 ∨ coord ySide u.1 = 0 then
      symWeight d p r u * splitEntropyNats130 (d.betaChild zSide p r u) else 0) +
  ∑ a : Fin 5,
    let mass := ∑ u, if 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
        coord zSide u.1 = (a : Nat) then symWeight d p r u else 0
    mass * Entropy.H Finset.univ
      (weightedSplit (symWeight d p r) (d.betaChild zSide p r)
        (fun u => 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
          coord zSide u.1 = (a : Nat)))

theorem log_two_mul_splitEntropy130 {w : Nat}
    (b : OmegaBound.ADVXXZ.SplitDist w) :
    Real.log 2 * splitEntropy b = splitEntropyNats130 b := by
  rw [mul_comm]
  exact Entropy.H_mul_log_two Finset.univ b.probR

private theorem log_two_mul_weighted_entropy130 {A : Type*} [Fintype A]
    (c : Real) (rho : A → Real) :
    Real.log 2 * (c * entropy rho) = c * Entropy.H Finset.univ rho := by
  calc
    Real.log 2 * (c * entropy rho) = c * (entropy rho * Real.log 2) := by ring
    _ = c * Entropy.H Finset.univ rho := by
      rw [entropy, Entropy.H_mul_log_two]

private theorem log_two_mul_weighted_splitEntropy130 {w : Nat}
    (c : Real) (b : OmegaBound.ADVXXZ.SplitDist w) :
    Real.log 2 * (c * splitEntropy b) = c * splitEntropyNats130 b := by
  calc
    Real.log 2 * (c * splitEntropy b) = c * (Real.log 2 * splitEntropy b) := by ring
    _ = c * splitEntropyNats130 b := by
      rw [log_two_mul_splitEntropy130]

theorem log_two_mul_constituentEta130
    (d : ConstituentData releasedPositiveInput) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    Real.log 2 * constituentEta d p r xSide ySide zSide =
      constituentEtaNats130 d p r xSide ySide zSide := by
  classical
  unfold constituentEta constituentEtaNats130
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs
    · exact log_two_mul_weighted_splitEntropy130 _ _
    · simp
  · apply Finset.sum_congr rfl
    intro a _
    exact log_two_mul_weighted_entropy130 _ _

theorem log_two_mul_constituentLambda130
    (d : ConstituentData releasedPositiveInput) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    Real.log 2 * constituentLambda d p r xSide ySide zSide =
      constituentLambdaNats130 d p r xSide ySide zSide := by
  classical
  unfold constituentLambda constituentLambdaNats130
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs
    · exact log_two_mul_weighted_splitEntropy130 _ _
    · simp
  · apply Finset.sum_congr rfl
    intro a _
    exact log_two_mul_weighted_entropy130 _ _

end OmegaBound.ADVXXZT6Round130
