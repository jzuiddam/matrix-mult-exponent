import OmegaBound.CW90EightBlkPi
import OmegaBound.ADVXXZSplitDist
import OmegaBound.CW90EightDSum
import OmegaBound.ADVXXZHoles

/-!
# Level-`ℓ` constituent tensors and interface tensors

This file builds the objects that Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou,
*More Asymmetry Yields Faster Matrix Multiplication* (`outline.tex:9-17`) call *interface
tensors*, on top of the split-distribution layer of `ADVXXZSplitDist`.  The definitions are
Vassilevska Williams–Xu–Xu–Zhou's (`prelim.tex:249-279`); ADVXXZ says its own are "the same
as in prior work".

* the **level-`ℓ` constituent tensor** `T_{i,j,k}^{(ℓ)}`, the subtensor of
  `T^{(ℓ)} = CW_q^{⊗2^{ℓ-1}}` on the variable blocks of levels `i, j, k`
  (`prelim.tex:130-160`), here `conT`;
* the **interface tensor**
  `⊗_{t ∈ [s]} T_{i_t,j_t,k_t}^{⊗n_t}[β_X^t, β_Y^t, β_Z^t, ε]`,
  here `iface`, whose factors `ifaceTerm` are the subtensors of `T_{i,j,k}^{⊗n}` cut out by
  `ε`-approximate consistency with three complete split distributions.

## Design

Everything is defined **by an indicator on the full leg type** `Fin N → Fin w → Idx7 q`,
never by a subtype.  Together with orienting every substitution as `x ↦ x ∘ π`, this keeps the layer free of
`cast` gymnastics.

A level-1 index sequence `Î ∈ {0,1,2}^{w·N}` of the source is here the curried
`chunkSeq x : Fin N → Chunk w` read off a leg `x : Fin N → Fin w → Idx7 q`; consecutive
chunking is currying, so no index arithmetic occurs anywhere.

## Main definitions

* `zoP` — the zero-out of a tensor by three decidable predicates; `act_sub`,
  `restricts_of_sub`, `zoP_restricts`.
* `chunkOf`, `levOf`, `chunkSeq` — the level-1 word of a level-`ℓ` variable, its level, and
  the level-1 index sequence of a leg.
* `Tlev`, `conT` — `T^{(ℓ)}` and its constituent tensors.
* `ifaceTerm`, `iface` — the terms of an interface tensor, and the interface tensor.

## Main results

* `zoP_eq_boxZO`, `zoP_zoP` — a predicate zero-out is a box zero-out, and nested zero-outs
  conjoin their predicates.
* `restricts_of_sub`, `zoP_restricts` — a substitution of variables, and a predicate zero-out,
  is a restriction.
-/

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZ

open CW90 CW90Eight

/-! ## Substitutions and predicate zero-outs -/

section ZODefs

variable {R : Type*} [CommSemiring R] {X Y Z : Type*}

/-- **The zero-out of `T` by three predicates**: keep the entry `(x,y,z)` iff all three
predicates hold.  Every zero-out in the laser method is of this shape. -/
def zoP (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) : Tensor3 R X Y Z :=
  fun x y z => if pX x ∧ pY y ∧ pZ z then T x y z else 0

theorem zoP_apply (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) (x : X) (y : Y) (z : Z) :
    zoP pX pY pZ T x y z = if pX x ∧ pY y ∧ pZ z then T x y z else 0 := rfl

/-- A predicate zero-out is a box zero-out with `Bool`-valued parts. -/
theorem zoP_eq_boxZO (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) :
    zoP pX pY pZ T = ADVXXZHoles.boxZO (fun x => decide (pX x)) (fun y => decide (pY y))
      (fun z => decide (pZ z)) {true} {true} {true} T := by
  funext x y z
  simp only [zoP, ADVXXZHoles.boxZO, Finset.mem_singleton, decide_eq_true_eq]

/-- Nested zero-outs conjoin their predicates. -/
theorem zoP_zoP (pX qX : X → Prop) [DecidablePred pX] [DecidablePred qX]
    (pY qY : Y → Prop) [DecidablePred pY] [DecidablePred qY]
    (pZ qZ : Z → Prop) [DecidablePred pZ] [DecidablePred qZ] (T : Tensor3 R X Y Z) :
    zoP pX pY pZ (zoP qX qY qZ T)
      = zoP (fun x => pX x ∧ qX x) (fun y => pY y ∧ qY y) (fun z => pZ z ∧ qZ z) T := by
  funext x y z
  simp only [zoP]
  split_ifs <;> tauto

end ZODefs

section ZORestrict

variable {R : Type*} [CommSemiring R] {X Y Z X' Y' Z' : Type*}
  [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Acting by the three "substitution" matrices renames the variables along arbitrary maps.
This is `ADVXXZHoles.act_perm` without the requirement that the maps be permutations of one
type; the orientation is `x ↦ x ∘ π`, which is what typechecks on dependent legs. -/
theorem act_sub (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z) (T : Tensor3 R X Y Z) :
    act (fun x' x => if x = f₁ x' then 1 else 0)
        (fun y' y => if y = f₂ y' then 1 else 0)
        (fun z' z => if z = f₃ z' then 1 else 0) T
      = fun x y z => T (f₁ x) (f₂ y) (f₃ z) := by
  funext x y z
  simp only [act]
  rw [Finset.sum_eq_single (f₁ x)]
  · rw [Finset.sum_eq_single (f₂ y)]
    · rw [Finset.sum_eq_single (f₃ z)]
      · simp
      · intro k _ hk
        simp [hk]
      · intro h; exact absurd (Finset.mem_univ (f₃ z)) h
    · intro j _ hj
      rw [Finset.sum_eq_zero]
      intro k _
      simp [hj]
    · intro h; exact absurd (Finset.mem_univ (f₂ y)) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    rw [Finset.sum_eq_zero]
    intro k _
    simp [hi]
  · intro h; exact absurd (Finset.mem_univ (f₁ x)) h

/-- **A substitution of variables is a restriction**, in the orientation
`T' x y z = T (f₁ x) (f₂ y) (f₃ z)`. -/
theorem restricts_of_sub {T : Tensor3 R X Y Z} {T' : Tensor3 R X' Y' Z'}
    (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z)
    (h : ∀ x y z, T' x y z = T (f₁ x) (f₂ y) (f₃ z)) : T' ≤ₜ T := by
  refine ⟨fun x' x => if x = f₁ x' then 1 else 0, fun y' y => if y = f₂ y' then 1 else 0,
    fun z' z => if z = f₃ z' then 1 else 0, ?_⟩
  rw [act_sub]
  funext x y z
  exact h x y z

/-- **A predicate zero-out is a restriction.** -/
theorem zoP_restricts (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) : zoP pX pY pZ T ≤ₜ T := by
  rw [zoP_eq_boxZO]
  exact ADVXXZHoles.boxZO_restricts _ _ _ _ _ _ T

end ZORestrict

/-! ## The level-`ℓ` partition of `CW_q^{⊗w}` -/

/-- **The level-1 word of a level-`ℓ` variable**: the sequence of level-1 block indices of
its `w` factors.  `prelim.tex:139-146`. -/
def chunkOf {q w : ℕ} (a : Fin w → Idx7 q) : Chunk w := fun p => lvl7 (a p)

/-- **The level-`ℓ` block index of a level-`ℓ` variable**, `∑_p σ_p`. -/
def levOf {q w : ℕ} (a : Fin w → Idx7 q) : ℕ := chunkLvl (chunkOf a)


/-- **`T^{(ℓ)} = CW_q^{⊗2^{ℓ-1}}`**, stated for a general width `w`. -/
abbrev Tlev (q w : ℕ) : Tensor3 ℚ (Fin w → Idx7 q) (Fin w → Idx7 q) (Fin w → Idx7 q) :=
  powT (T7 q) w


/-- **The level-`ℓ` constituent tensor `T_{i,j,k}^{(ℓ)}`**, as a zero-out of `T^{(ℓ)}` on the
full leg type. -/
def conT (q w i j k : ℕ) : Tensor3 ℚ (Fin w → Idx7 q) (Fin w → Idx7 q) (Fin w → Idx7 q) :=
  zoP (fun a => levOf a = i) (fun b => levOf b = j) (fun c => levOf c = k) (Tlev q w)

/-! ## Interface tensors -/

/-- **The level-1 index sequence of a leg** of `(T^{(ℓ)})^{⊗N}`: the source's
`Î ∈ {0,1,2}^{w·N}`, curried.  `prelim.tex:171-190`. -/
def chunkSeq {q w N : ℕ} (x : Fin N → Fin w → Idx7 q) : Fin N → Chunk w :=
  fun t => chunkOf (x t)

/-- **A term of an interface tensor**, `T_{i,j,k}^{⊗N}[β_X, β_Y, β_Z, ε]` of
`prelim.tex:265-274`: the subtensor of `T_{i,j,k}^{⊗N}` spanned by the level-1 triples whose
index sequences are `ε`-approximately consistent with `β_X, β_Y, β_Z`. -/
def ifaceTerm (q w i j k N : ℕ) (bX bY bZ : SplitDist w) (ε : ℚ) :
    Tensor3 ℚ (Fin N → Fin w → Idx7 q) (Fin N → Fin w → Idx7 q) (Fin N → Fin w → Idx7 q) :=
  fun x y z =>
    if ApproxConsistent ε bX (chunkSeq x) ∧ ApproxConsistent ε bY (chunkSeq y)
        ∧ ApproxConsistent ε bZ (chunkSeq z)
      then powT (conT q w i j k) N x y z else 0

/-- **The interface tensor** `⊗_{t ∈ [s]} T_{i_t,j_t,k_t}^{⊗n_t}[β_X^t, β_Y^t, β_Z^t, ε]`,
ADVXXZ `outline.tex:9-17`, Definition 2.1.  The `s` terms have different leg types, so this
is the *heterogeneous* product `CW90Eight.piT`, which is what the §8 layer's multiplicativity
results consume. -/
def iface (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ) (bX bY bZ : Fin s → SplitDist w) (ε : ℚ) :
    Tensor3 ℚ ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q) :=
  piT fun t => ifaceTerm q w (i t) (j t) (k t) (n t) (bX t) (bY t) (bZ t) ε

end ADVXXZ
end OmegaBound
