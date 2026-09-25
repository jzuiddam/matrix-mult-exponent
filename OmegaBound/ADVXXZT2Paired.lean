import OmegaBound.ADVXXZT2Marg

/-!
# A paired law on one total level is determined by a half marginal

Two laws can have identical left and right marginals and different joints.  `joint_of_half`
shows, over an arbitrary finite carrier, that this cannot happen for a nonnegative weighting
supported on **one** total level: there the joint is determined by either marginal.

`chunkLvl_split`, `betaIdx_support` and `parBeta_support` supply that hypothesis on the parent
side of the released tables: every word in the support of a parent's complete-split law has the
parent's own leg level (exact level support, `ADVXXZG1.g1_support`).
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT2

open ADVXXZ (Chunk chunkLvl)
open ADVXXZPaper (Side)
open ADVXXZG2 (leftHalfLvl rightHalfLvl)

/-! ## §1  The abstract bridge -/

/-- **THE BRIDGE.**  A nonnegative weighting whose support sits at one total level `M` has its
paired law determined by its left marginal: on the antidiagonal `a + b = M` the joint *is* the
marginal. -/
theorem joint_of_half {ι : Type} [Fintype ι] [DecidableEq ι]
    (num L R : ι → ℕ) (M : ℕ) (hs : ∀ i, num i ≠ 0 → L i + R i = M) (a b : ℕ) (hab : a + b = M) :
    (∑ i, if L i = a ∧ R i = b then num i else 0) = ∑ i, if L i = a then num i else 0 := by
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h1 : L i = a
  · by_cases h2 : R i = b
    · rw [if_pos ⟨h1, h2⟩, if_pos h1]
    · rw [if_neg (fun h => h2 h.2), if_pos h1]
      symm
      by_contra hne
      have hl := hs i hne
      rw [h1] at hl
      exact h2 (by omega)
  · rw [if_neg (fun h => h1 h.1), if_neg h1]

/-! ## §2  Both sides of the released seam sit at one total level -/

/-- The two half levels of a released level-1 word add to its level. -/
theorem chunkLvl_split : ∀ c : Chunk 4, chunkLvl c = leftHalfLvl c + rightHalfLvl c := by
  decide +kernel

/-- **EXACT LEVEL SUPPORT AT A RELEASED ROW INDEX**, transported from `ADVXXZG1.g1_support`
through the bijection `ADVXXZCertRegionalSemantic.shapeIndex`. -/
theorem betaIdx_support (r : Fin 6) (S : Side) (n : Fin 45) (c : Chunk 4) :
    (ADVXXZG1.betaIdx r S n).num c ≠ 0 ↔ chunkLvl c = ADVXXZG1.rowLvl S n := by
  obtain ⟨u, hu⟩ := ADVXXZT1.shapeIndex_bijective.2 n
  subst hu
  rw [ADVXXZG1.betaIdx_shapeIndex, ADVXXZG1.rowLvl_shapeIndex]
  exact (ADVXXZG1.g1_support r S u c).1

/-- **THE PARENT LAW'S SUPPORT SITS AT THE PARENT'S OWN PHYSICAL LEG.**  This is the hypothesis of
`joint_of_half` on the parent side. -/
theorem parBeta_support (p : ℕ) (l : Fin 3) (c : Chunk 4) :
    (parBeta p l.val).num c ≠ 0 →
      leftHalfLvl c + rightHalfLvl c = (legs (parShapeOf p)).getD l.val 0 := by
  intro h
  have h1 := (betaIdx_support (parRegion p) (parSide p l.val)
    (logRow (parRegion p) (parRow p)) c).mp h
  have h2 : ADVXXZG1.rowLvl (parSide p l.val) (logRow (parRegion p) (parRow p))
      = (legs (ADVXXZG1.rowShape (parRow p))).getD l.val 0 := by
    have := rowLvl_logRow (parRegion p) (parRow p) l
    simpa [parSide] using this
  rw [h2, parRow_shape] at h1
  rw [← h1, chunkLvl_split c]

end ADVXXZT2
end OmegaBound
