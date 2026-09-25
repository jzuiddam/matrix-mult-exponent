import OmegaBound.ADVXXZStageDegen

/-!
# Definitions for the two main ADVXXZ stage theorems

This module defines the finite notation in which ADVXXZ `thm:global-stage-with-eps` and
`thm:constituent-stage-with-eps` are read: probability vectors and base-two entropy, level
shapes, marginals and the penalty `P_α`, weighted split averages, the global data with its `η`,
`λ` and region rate, and the constituent data with its rows, region rate and output
parameters.  It proves nothing and introduces no axiom.  A source `o_{1/ε}(1)` loss is
expressed by `VanishesWithTolerance`; there is no asymptotic notation in any declaration below.

## Corrections carried by the constituent statement

The constituent data below use the corrected forms, not the two erroneous printed forms:

1. every child shape `u` has the symmetric output weight
   `α(u) + α(parentShape - u)`; the associated collision entropy is
   `H(α) + Pα` (the sign is `+`, not `-`);
2. the `Y`/`Z` averaged complete-split laws are weighted by that same symmetric weight.
   The printed `α`-only compatibility weighting is the global-stage law and is invalid after
   the constituent stage's odd/even pairing.

These are the forms printed in the D26 derived-quantities calculation and implemented by the
released ADVXXZ MATLAB.

SOURCE: constituent.tex:253-265 (corrected)
SOURCE: constituent.tex:315-326 (corrected)
SOURCE: D26/main.tex:373-450
-/

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZPaper

open ADVXXZ (Chunk RatDist SplitDist)

/-! ## Finite probability and entropy notation -/

/-- A real-valued probability distribution on a finite alphabet. -/
def IsProbability {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Base-two Shannon entropy, with Mathlib's `0 * log 0 = 0` convention. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  Entropy.H₂ Finset.univ p

/-- The three tensor sides. -/
inductive Side
  | X | Y | Z
  deriving DecidableEq, Fintype

/-- A level of total width `w`: `i+j+k = 2*w`.  The coordinates retain their unreduced
`Fin (2*w+1)` types, so finiteness is visible to Lean without replacing the arithmetic by a
computed numeral. -/
abbrev Shape (w : ℕ) :=
  {u : Fin (2 * w + 1) × Fin (2 * w + 1) × Fin (2 * w + 1) //
    (u.1 : ℕ) + (u.2.1 : ℕ) + (u.2.2 : ℕ) = 2 * w}

def coord {w : ℕ} : Side → Shape w → ℕ
  | .X, u => u.1.1
  | .Y, u => u.1.2.1
  | .Z, u => u.1.2.2

/-- A six-region role assignment contains every permutation exactly once.  Its order is
mathematically immaterial; this is the content of the paper's "lexicographic order" clause. -/
def EnumeratesPermutations (π : Fin 6 → Side → Side) : Prop :=
  (∀ r, Function.Bijective (π r)) ∧
  (∀ σ : Side → Side, Function.Bijective σ → ∃! r, π r = σ)

noncomputable def marginal {w : ℕ} (p : Shape w → ℝ) (W : Side)
    (a : Fin (2 * w + 1)) : ℝ :=
  ∑ u, if coord W u = (a : ℕ) then p u else 0

def SameMarginals {w : ℕ} (p p' : Shape w → ℝ) : Prop :=
  ∀ W a, marginal p W a = marginal p' W a

/-- `P_α = max H(α') - H(α)`, written as a supremum so its definition itself needs no
compactness proof.  On the finite probability simplex this is the paper's maximum. -/
noncomputable def penalty {w : ℕ} (p : Shape w → ℝ) : ℝ :=
  sSup {h : ℝ | ∃ p' : Shape w → ℝ,
    IsProbability p' ∧ SameMarginals p p' ∧ h = entropy p'} - entropy p

noncomputable def splitEntropy {w : ℕ} (b : SplitDist w) : ℝ :=
  entropy b.probR

/-- A weighted average of complete split distributions.  If the selected mass is zero, Lean's
division-by-zero convention gives the zero function; all occurrences below are multiplied by
that mass, making this the continuous perspective convention omitted by ADVXXZ. -/
noncomputable def weightedSplit {ι : Type*} [Fintype ι] {w : ℕ}
    (mass : ι → ℝ) (b : ι → SplitDist w) (selected : ι → Prop)
    [DecidablePred selected] (σ : Chunk w) : ℝ :=
  (∑ u, if selected u then mass u * (b u).probR σ else 0) /
    (∑ u, if selected u then mass u else 0)

/-! ## Explicit asymptotic predicates -/

/-- A nonnegative `o_{1/ε}(1)` loss, fully expanded at `ε = 0`. -/
def VanishesWithTolerance (loss : ℚ → ℝ) : Prop :=
  (∀ ε, 0 ≤ loss ε) ∧
  ∀ ζ : ℝ, 0 < ζ → ∃ ε₀ : ℚ, 0 < ε₀ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ ε₀ → |loss ε| ≤ ζ

/-! ## Global-stage data and rates -/

abbrev GlobalTerm (w : ℕ) := Fin 6 × Shape w

structure GlobalData (w : ℕ) where
  A : Fin 6 → ℝ
  alpha : Fin 6 → Shape w → ℝ
  beta : Side → Fin 6 → Shape w → SplitDist w
  E : Fin 6 → ℝ
  perm : Fin 6 → Side → Side
  /-- Integral joint weights `A_r * α_r(u)`, including the source's implicit integrality
  convention. -/
  joint : RatDist (GlobalTerm w)

noncomputable def globalAverage (d : GlobalData w) (r : Fin 6) (W : Side)
    (σ : Chunk w) : ℝ :=
  ∑ u, d.alpha r u * (d.beta W r u).probR σ

noncomputable def globalEta (d : GlobalData w) (r : Fin 6)
    (_xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord zSide u = 0 then
      d.alpha r u * splitEntropy (d.beta ySide r u) else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if coord ySide u = a ∧ 0 < coord zSide u then d.alpha r u else 0
    mass * entropy (weightedSplit (d.alpha r) (d.beta ySide r)
      (fun u => coord ySide u = a ∧ 0 < coord zSide u))

noncomputable def globalLambda (d : GlobalData w) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord xSide u = 0 ∨ coord ySide u = 0 then
      d.alpha r u * splitEntropy (d.beta zSide r u) else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a
      then d.alpha r u else 0
    mass * entropy (weightedSplit (d.alpha r) (d.beta zSide r)
      (fun u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = a))

noncomputable def globalRegionRate (d : GlobalData w) (r : Fin 6) : ℝ :=
  let xSide := d.perm r .X
  let ySide := d.perm r .Y
  let zSide := d.perm r .Z
  min (entropy (marginal (d.alpha r) xSide) - penalty (d.alpha r))
    (min (entropy (globalAverage d r ySide) - globalEta d r xSide ySide zSide)
      (entropy (globalAverage d r zSide) - globalLambda d r xSide ySide zSide))

/-! ## Constituent-stage data and rates -/

/-- The non-corner input terms of the constituent stage.  Parent width is kept literally as
`w + w`; the child width is `w`. -/
structure ConstituentInput (w s : ℕ) where
  terms_nonempty : 0 < s
  baseN : Fin s → ℕ
  baseN_pos : ∀ t, 0 < baseN t
  i : Fin s → ℕ
  j : Fin s → ℕ
  k : Fin s → ℕ
  i_pos : ∀ t, 0 < i t
  j_pos : ∀ t, 0 < j t
  k_pos : ∀ t, 0 < k t
  shape_sum : ∀ t, i t + j t + k t = 2 * (w + w)
  beta : Side → Fin s → SplitDist (w + w)
  beta_supported : ∀ W t σ, (beta W t).probR σ ≠ 0 →
    ADVXXZ.chunkLvl σ = (match W with | .X => i t | .Y => j t | .Z => k t)

/-- Child shapes that fit inside parent term `t`. -/
abbrev ChildShape (p : ConstituentInput w s) (t : Fin s) :=
  {u : Shape w // coord .X u ≤ p.i t ∧ coord .Y u ≤ p.j t ∧ coord .Z u ≤ p.k t}

/-- The paired shape `parentShape - u`.  Its coordinates and its type-level total are left
unreduced. -/
def complement (p : ConstituentInput w s) (t : Fin s) (u : ChildShape p t) :
    ChildShape p t := by
  let x := p.i t - coord .X u.1
  let y := p.j t - coord .Y u.1
  let z := p.k t - coord .Z u.1
  have hsum : x + y + z = 2 * w := by
    dsimp [x, y, z]
    have hshape : coord .X u.1 + coord .Y u.1 + coord .Z u.1 = 2 * w := u.1.property
    have hxle : coord .X u.1 ≤ p.i t := u.property.1
    have hyle : coord .Y u.1 ≤ p.j t := u.property.2.1
    have hzle : coord .Z u.1 ≤ p.k t := u.property.2.2
    have hp : p.i t + p.j t + p.k t = 2 * (w + w) := p.shape_sum t
    omega
  have hx : x < 2 * w + 1 := by omega
  have hy : y < 2 * w + 1 := by omega
  have hz : z < 2 * w + 1 := by omega
  let v : Shape w := ⟨(⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩), hsum⟩
  refine ⟨v, ?_⟩
  dsimp [v, x, y, z, coord]
  omega

def leftHalf {w : ℕ} (σ : Chunk (w + w)) : Chunk w :=
  fun a => σ ⟨a, by omega⟩

def rightHalf {w : ℕ} (σ : Chunk (w + w)) : Chunk w :=
  fun a => σ ⟨w + a, by omega⟩

noncomputable def halfMarginal {w : ℕ} (b : SplitDist (w + w))
    (a : Fin (2 * w + 1)) : ℝ :=
  ∑ σ, if ADVXXZ.chunkLvl (leftHalf σ) = (a : ℕ) then b.probR σ else 0

noncomputable def pairProb {w : ℕ} (left right : SplitDist w)
    (σ : Chunk (w + w)) : ℝ :=
  left.probR (leftHalf σ) * right.probR (rightHalf σ)

abbrev ConstituentTerm (p : ConstituentInput w s) :=
  (t : Fin s) × Fin 6 × ChildShape p t

structure ConstituentData (p : ConstituentInput w s) where
  A : Fin s → Fin 6 → ℝ
  betaRegion : Side → Fin s → Fin 6 → SplitDist (w + w)
  alpha : (t : Fin s) → Fin 6 → ChildShape p t → ℝ
  betaChild : (W : Side) → (t : Fin s) → Fin 6 → ChildShape p t → SplitDist w
  E : Fin 6 → ℝ
  perm : Fin 6 → Side → Side
  /-- Integral base multiplicities for the corrected output parameter list. -/
  outBase : ConstituentTerm p → ℕ

section ConstituentFixed

variable {w s : ℕ} {p : ConstituentInput w s}

noncomputable def constituentMarginal (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (W : Side) (a : Fin (2 * w + 1)) : ℝ :=
  ∑ u, if coord W u.1 = (a : ℕ) then d.alpha t r u else 0

def SameConstituentMarginals (t : Fin s) (a a' : ChildShape p t → ℝ) : Prop :=
  ∀ W x,
    (∑ u, if coord W u.1 = (x : ℕ) then a u else 0) =
    ∑ u, if coord W u.1 = (x : ℕ) then a' u else 0

noncomputable def constituentPenalty (d : ConstituentData p) (t : Fin s)
    (r : Fin 6) : ℝ :=
  sSup {h : ℝ | ∃ a' : ChildShape p t → ℝ,
    IsProbability a' ∧ SameConstituentMarginals t (d.alpha t r) a' ∧
      h = entropy a'} - entropy (d.alpha t r)


/-- The corrected odd/even-pair weight `α(u)+α(parentShape-u)`. -/
noncomputable def symWeight (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (u : ChildShape p t) : ℝ :=
  d.alpha t r u +
    ∑ v, if v = complement p t u then d.alpha t r v else 0

noncomputable def constituentAverage (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (W groupSide positiveSide : Side) (a : Fin (2 * w + 1)) (σ : Chunk w) : ℝ :=
  weightedSplit (symWeight d t r) (d.betaChild W t r)
    (fun u => coord groupSide u.1 = (a : ℕ) ∧ 0 < coord positiveSide u.1) σ

/-- Corrected `η`: both the outer mass and the averaged target law use `symWeight`. -/
noncomputable def constituentEta (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (_xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord zSide u.1 = 0 then
      symWeight d t r u * splitEntropy (d.betaChild ySide t r u) else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if coord ySide u.1 = (a : ℕ) ∧ 0 < coord zSide u.1
      then symWeight d t r u else 0
    mass * entropy (constituentAverage d t r ySide ySide zSide a)

/-- Corrected `λ`: both the outer mass and the averaged target law use `symWeight`. -/
noncomputable def constituentLambda (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  (∑ u, if coord xSide u.1 = 0 ∨ coord ySide u.1 = 0 then
      symWeight d t r u * splitEntropy (d.betaChild zSide t r u) else 0) +
  ∑ a : Fin (2 * w + 1),
    let mass := ∑ u, if 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
        coord zSide u.1 = (a : ℕ) then symWeight d t r u else 0
    mass * entropy (weightedSplit (symWeight d t r) (d.betaChild zSide t r)
      (fun u => 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
        coord zSide u.1 = (a : ℕ)))

noncomputable def constituentRowX (d : ConstituentData p) (r : Fin 6)
    (xSide : Side) : ℝ :=
  ∑ t, d.A t r * (p.baseN t : ℝ) *
    (entropy (constituentMarginal d t r xSide) - constituentPenalty d t r)

noncomputable def constituentRowY (d : ConstituentData p) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  ∑ t, d.A t r * (p.baseN t : ℝ) *
    (splitEntropy (d.betaRegion ySide t r) - constituentEta d t r xSide ySide zSide)

noncomputable def constituentRowZ (d : ConstituentData p) (r : Fin 6)
    (xSide ySide zSide : Side) : ℝ :=
  ∑ t, d.A t r * (p.baseN t : ℝ) *
    (splitEntropy (d.betaRegion zSide t r) - constituentLambda d t r xSide ySide zSide)

noncomputable def constituentRegionRate (d : ConstituentData p) (r : Fin 6) : ℝ :=
  let xSide := d.perm r .X
  let ySide := d.perm r .Y
  let zSide := d.perm r .Z
  min (constituentRowX d r xSide)
    (min (constituentRowY d r xSide ySide zSide)
      (constituentRowZ d r xSide ySide zSide))


noncomputable def constituentBaseTotal (p : ConstituentInput w s) : ℕ :=
  ∑ t, p.baseN t


noncomputable def constituentIndex (x : Fin (Fintype.card (ConstituentTerm p))) :
    ConstituentTerm p :=
  (Fintype.equivFin (ConstituentTerm p)).symm x

noncomputable def constituentOutN (d : ConstituentData p) (m : ℕ)
    (x : Fin (Fintype.card (ConstituentTerm p))) : ℕ :=
  d.outBase (constituentIndex x) * m

noncomputable def constituentOutI (x : Fin (Fintype.card (ConstituentTerm p))) : ℕ :=
  coord .X (constituentIndex x).2.2.1

noncomputable def constituentOutJ (x : Fin (Fintype.card (ConstituentTerm p))) : ℕ :=
  coord .Y (constituentIndex x).2.2.1

noncomputable def constituentOutK (x : Fin (Fintype.card (ConstituentTerm p))) : ℕ :=
  coord .Z (constituentIndex x).2.2.1

noncomputable def constituentOutBeta (d : ConstituentData p) (W : Side)
    (x : Fin (Fintype.card (ConstituentTerm p))) : SplitDist w :=
  d.betaChild W (constituentIndex x).1 (constituentIndex x).2.1
    (constituentIndex x).2.2

end ConstituentFixed

end ADVXXZPaper
end OmegaBound
