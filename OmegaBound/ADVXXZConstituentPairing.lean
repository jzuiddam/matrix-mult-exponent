import OmegaBound.ADVXXZPaperTheorems

/-!
# Exact algebra of the corrected constituent pairing

The constituent stage pairs a child shape `u` with `parentShape - u`.  Consequently its output
weight is `alpha(u) + alpha(complement u)`, not the one-sided weight printed in the ADVXXZ paper.
This file records the elementary but essential facts that the pairing is an involution, that the
corrected weight is `alpha(u) + alpha(complement u)`, and that its total mass is exactly two.
-/

open Finset

namespace OmegaBound
namespace ADVXXZPaper

variable {w s : ℕ} {p : ConstituentInput w s}

/-- Complementing a child shape twice returns the original child shape. -/
theorem complement_complement (t : Fin s) (u : ChildShape p t) :
    complement p t (complement p t u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  rcases u with ⟨⟨⟨x, y, z⟩, hsum⟩, hx, hy, hz⟩
  have hx' : (x : ℕ) ≤ p.i t := by simpa only [coord] using hx
  have hy' : (y : ℕ) ≤ p.j t := by simpa only [coord] using hy
  have hz' : (z : ℕ) ≤ p.k t := by simpa only [coord] using hz
  simp only [complement, coord]
  congr <;> omega

/-- The finite indicator sum in `symWeight` selects exactly the complementary coefficient. -/
theorem symWeight_eq_add_complement (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (u : ChildShape p t) :
    symWeight d t r u = d.alpha t r u + d.alpha t r (complement p t u) := by
  classical
  unfold symWeight
  rw [Finset.sum_ite_eq']
  simp


/-- A probability law has corrected symmetric total weight two, counting fixed points twice. -/
theorem sum_symWeight_eq_two (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (hprob : IsProbability (d.alpha t r)) :
    ∑ u, symWeight d t r u = 2 := by
  classical
  rw [Finset.sum_congr rfl (fun u _ => symWeight_eq_add_complement d t r u),
    Finset.sum_add_distrib, hprob.2]
  have hperm : Function.Bijective (complement p t) := by
    constructor
    · intro u v huv
      simpa only [complement_complement] using congrArg (complement p t) huv
    · intro u
      exact ⟨complement p t u, complement_complement t u⟩
  rw [hperm.sum_comp, hprob.2]
  norm_num

end ADVXXZPaper
end OmegaBound
