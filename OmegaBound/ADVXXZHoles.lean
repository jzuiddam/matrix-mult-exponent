/-
# Hole fixing for partitioned tensors

This file formalises the "fixing holes" step of the modern laser method, i.e.

* Vassilevska Williams–Xu–Xu–Zhou, *New Bounds for Matrix Multiplication: from Alpha to Omega*
  (arXiv:2307.07970), Section 3, Theorem 3.1 and Corollary 3.2; and
* Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou, *More Asymmetry Yields Faster Matrix
  Multiplication* (arXiv:2404.16349), where the same statement is quoted as
  `thm:fix-holes` and used once per stage per level.

The statement: let `T` be a tensor whose `X`-, `Y`-, `Z`-variables are partitioned into
*parts*, and suppose `T` admits a family of symmetries that permute parts transitively.
A *broken copy* of `T` is a zero-out of `T` that deletes a few whole parts (the *holes*).
Then sub-polynomially many broken copies, each missing at most a `1/(4D)` fraction of the
parts in each of the three modes, restrict onto an unbroken copy of `T`.

Two deviations from the source, both proved here:

* The source splits the target into `8` sub-boxes and recurses on `7` of them.  Nesting the
  three binary splits instead leaves only `3` recursive sub-boxes, so the copy count is
  `4 ^ (…)` rather than `7 ^ (…)`; see `boxZO_split`.
* The source states its shuffling lemma with the part-sets universally quantified *inside*
  the existential (VXXZ24, Lemma 3.3).  As stated that is false; the proof — an averaging
  argument followed by Markov and a union bound — establishes it for a *fixed* triple of
  part-sets, which is all the application needs.  `exists_good_shuffle` below is the fixed
  version, with the averaging made exact (no probability measure is involved: the family of
  symmetries is a `Finset`).

Everything here is finite and exact.  No asymptotics enter.
-/
import OmegaBound.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Tensor3

namespace OmegaBound
namespace ADVXXZHoles

variable {R : Type*} [CommSemiring R]

/-! ## Boxes and family direct sums -/

section Defs

variable {X Y Z PX PY PZ ι : Type*}

/-- `boxZO pX pY pZ A C E T` zeroes out every variable whose part is outside `A`, `C`, `E`
respectively.  This is the subtensor `T‖_{A, C, E}` of the source. -/
def boxZO [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
    (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ)
    (A : Finset PX) (C : Finset PY) (E : Finset PZ) (T : Tensor3 R X Y Z) :
    Tensor3 R X Y Z :=
  fun x y z => if pX x ∈ A ∧ pY y ∈ C ∧ pZ z ∈ E then T x y z else 0

/-- The direct sum `⨁_{i ∈ S} T i`, realised on the index sets `ι × X`, `ι × Y`, `ι × Z`. -/
def famDS [DecidableEq ι] (S : Finset ι) (T : ι → Tensor3 R X Y Z) :
    Tensor3 R (ι × X) (ι × Y) (ι × Z) :=
  fun a b c => if a.1 = b.1 ∧ b.1 = c.1 ∧ a.1 ∈ S then T a.1 a.2 b.2 c.2 else 0

end Defs

/-! ## Acting by diagonal and permutation matrices -/

section Act

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Acting by three diagonal matrices scales each entry. -/
theorem act_diag (a : X → R) (b : Y → R) (c : Z → R) (T : Tensor3 R X Y Z) :
    act (fun x' x => if x' = x then a x' else 0)
        (fun y' y => if y' = y then b y' else 0)
        (fun z' z => if z' = z then c z' else 0) T
      = fun x y z => a x * b y * c z * T x y z := by
  funext x y z
  simp only [act]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · rw [Finset.sum_eq_single z]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ z) h
    · intro j _ hj
      rw [Finset.sum_eq_zero]
      intro k _
      simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ y) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    rw [Finset.sum_eq_zero]
    intro k _
    simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Acting by three permutation matrices relabels the variables. -/
theorem act_perm (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (ρ : Equiv.Perm Z)
    (T : Tensor3 R X Y Z) :
    act (fun x' x => if x = σ x' then 1 else 0)
        (fun y' y => if y = τ y' then 1 else 0)
        (fun z' z => if z = ρ z' then 1 else 0) T
      = fun x y z => T (σ x) (τ y) (ρ z) := by
  funext x y z
  simp only [act]
  rw [Finset.sum_eq_single (σ x)]
  · rw [Finset.sum_eq_single (τ y)]
    · rw [Finset.sum_eq_single (ρ z)]
      · simp
      · intro k _ hk
        simp [hk]
      · intro h; exact absurd (Finset.mem_univ (ρ z)) h
    · intro j _ hj
      rw [Finset.sum_eq_zero]
      intro k _
      simp [hj]
    · intro h; exact absurd (Finset.mem_univ (τ y)) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    rw [Finset.sum_eq_zero]
    intro k _
    simp [hi]
  · intro h; exact absurd (Finset.mem_univ (σ x)) h

/-- The zero tensor is a restriction of anything. -/
theorem zero_restricts {X' Y' Z' : Type*} (T : Tensor3 R X Y Z) :
    (fun (_ : X') (_ : Y') (_ : Z') => (0 : R)) ≤ₜ T := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  funext x y z
  simp [act]

end Act

/-! ## Basic properties of `boxZO` -/

section BoxZO

variable {X Y Z PX PY PZ : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
  (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ)

/-- A box zero-out of a box zero-out is the zero-out to the intersection. -/
theorem boxZO_boxZO (A A' : Finset PX) (C C' : Finset PY) (E E' : Finset PZ)
    (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ A C E (boxZO pX pY pZ A' C' E' T)
      = boxZO pX pY pZ (A ∩ A') (C ∩ C') (E ∩ E') T := by
  funext x y z
  simp only [boxZO, Finset.mem_inter]
  by_cases h1 : pX x ∈ A <;> by_cases h2 : pY y ∈ C <;> by_cases h3 : pZ z ∈ E <;>
    by_cases h4 : pX x ∈ A' <;> by_cases h5 : pY y ∈ C' <;> by_cases h6 : pZ z ∈ E' <;>
    simp [h1, h2, h3, h4, h5, h6]

/-- A box zero-out is a restriction. -/
theorem boxZO_restricts (A : Finset PX) (C : Finset PY) (E : Finset PZ)
    (T : Tensor3 R X Y Z) : boxZO pX pY pZ A C E T ≤ₜ T := by
  refine ⟨fun x' x => if x' = x then (if pX x' ∈ A then (1 : R) else 0) else 0,
          fun y' y => if y' = y then (if pY y' ∈ C then (1 : R) else 0) else 0,
          fun z' z => if z' = z then (if pZ z' ∈ E then (1 : R) else 0) else 0, ?_⟩
  rw [act_diag]
  funext x y z
  simp only [boxZO]
  by_cases h1 : pX x ∈ A <;> by_cases h2 : pY y ∈ C <;> by_cases h3 : pZ z ∈ E <;>
    simp [h1, h2, h3]

/-- Monotonicity of `boxZO` in the boxes. -/
theorem boxZO_mono {A A' : Finset PX} {C C' : Finset PY} {E E' : Finset PZ}
    (hA : A ⊆ A') (hC : C ⊆ C') (hE : E ⊆ E') (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ A C E T ≤ₜ boxZO pX pY pZ A' C' E' T := by
  have h : boxZO pX pY pZ A C E T
      = boxZO pX pY pZ A C E (boxZO pX pY pZ A' C' E' T) := by
    rw [boxZO_boxZO, Finset.inter_eq_left.2 hA, Finset.inter_eq_left.2 hC,
      Finset.inter_eq_left.2 hE]
  rw [h]
  exact boxZO_restricts pX pY pZ A C E _

/-- A box with an empty side is the zero tensor. -/
theorem boxZO_empty_left (C : Finset PY) (E : Finset PZ) (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ (∅ : Finset PX) C E T = fun _ _ _ => 0 := by
  funext x y z; simp [boxZO]

theorem boxZO_empty_mid (A : Finset PX) (E : Finset PZ) (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ A (∅ : Finset PY) E T = fun _ _ _ => 0 := by
  funext x y z; simp [boxZO]

theorem boxZO_empty_right (A : Finset PX) (C : Finset PY) (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ A C (∅ : Finset PZ) T = fun _ _ _ => 0 := by
  funext x y z; simp [boxZO]

/-- Nesting the three binary splits `A = A₀ ⊔ A₁`, `C = C₀ ⊔ C₁`, `E = E₀ ⊔ E₁` writes the
box `A × C × E` as a sum of **four** boxes, not eight. -/
theorem boxZO_split (A₀ A₁ : Finset PX) (C₀ C₁ : Finset PY) (E₀ E₁ : Finset PZ)
    (hA : Disjoint A₀ A₁) (hC : Disjoint C₀ C₁) (hE : Disjoint E₀ E₁)
    (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ (A₀ ∪ A₁) (C₀ ∪ C₁) (E₀ ∪ E₁) T
      = (fun x y z => boxZO pX pY pZ A₀ (C₀ ∪ C₁) (E₀ ∪ E₁) T x y z
          + (boxZO pX pY pZ A₁ C₀ (E₀ ∪ E₁) T x y z
            + (boxZO pX pY pZ A₁ C₁ E₀ T x y z + boxZO pX pY pZ A₁ C₁ E₁ T x y z))) := by
  funext x y z
  have hA' : pX x ∈ A₀ → pX x ∉ A₁ := fun h => Finset.disjoint_left.1 hA h
  have hC' : pY y ∈ C₀ → pY y ∉ C₁ := fun h => Finset.disjoint_left.1 hC h
  have hE' : pZ z ∈ E₀ → pZ z ∉ E₁ := fun h => Finset.disjoint_left.1 hE h
  simp only [boxZO, Finset.mem_union]
  by_cases h1 : pX x ∈ A₀ <;> by_cases h2 : pX x ∈ A₁ <;>
    by_cases h3 : pY y ∈ C₀ <;> by_cases h4 : pY y ∈ C₁ <;>
    by_cases h5 : pZ z ∈ E₀ <;> by_cases h6 : pZ z ∈ E₁ <;>
    simp_all

end BoxZO

/-! ## The family direct sum -/

section FamDS

variable {X Y Z X' Y' Z' ι : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype ι] [DecidableEq ι]

theorem famDS_apply (S : Finset ι) (T : ι → Tensor3 R X Y Z)
    (i : ι) (x : X) (j : ι) (y : Y) (k : ι) (z : Z) :
    famDS S T (i, x) (j, y) (k, z)
      = (if i = j then (1 : R) else 0) * (if j = k then (1 : R) else 0)
          * (if i ∈ S then (1 : R) else 0) * T i x y z := by
  simp only [famDS]
  by_cases h1 : i = j <;> by_cases h2 : j = k <;> by_cases h3 : i ∈ S <;>
    simp [h1, h2, h3]

/-- The fundamental computation: acting on a family direct sum collapses the three
index-of-summand coordinates to a single one. -/
theorem act_famDS (C₁ : X' → ι × X → R) (C₂ : Y' → ι × Y → R) (C₃ : Z' → ι × Z → R)
    (S : Finset ι) (T : ι → Tensor3 R X Y Z) (x' : X') (y' : Y') (z' : Z') :
    act C₁ C₂ C₃ (famDS S T) x' y' z'
      = ∑ i ∈ S, ∑ x : X, ∑ y : Y, ∑ z : Z,
          C₁ x' (i, x) * C₂ y' (i, y) * C₃ z' (i, z) * T i x y z := by
  have key : ∀ i : ι,
      (∑ x : X, ∑ j : ι, ∑ y : Y, ∑ k : ι, ∑ z : Z,
        C₁ x' (i, x) * C₂ y' (j, y) * C₃ z' (k, z) * famDS S T (i, x) (j, y) (k, z))
      = if i ∈ S then
          (∑ x : X, ∑ y : Y, ∑ z : Z,
            C₁ x' (i, x) * C₂ y' (i, y) * C₃ z' (i, z) * T i x y z) else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_eq_single i]
        · refine Finset.sum_congr rfl (fun z _ => ?_)
          simp [famDS, hi]
        · intro k _ hk
          refine Finset.sum_eq_zero (fun z _ => ?_)
          simp [famDS, Ne.symm hk]
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro j _ hj
        refine Finset.sum_eq_zero (fun y _ => ?_)
        refine Finset.sum_eq_zero (fun k _ => ?_)
        refine Finset.sum_eq_zero (fun z _ => ?_)
        simp [famDS, Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    · simp only [hi, if_false]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      refine Finset.sum_eq_zero (fun y _ => ?_)
      refine Finset.sum_eq_zero (fun k _ => ?_)
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp [famDS, hi]
  simp only [act, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_ite_mem]
  simp

/-- A restriction of one summand is a restriction of the whole family direct sum. -/
theorem restricts_famDS_of_mem {V : Tensor3 R X' Y' Z'} {T : ι → Tensor3 R X Y Z}
    {i : ι} {S : Finset ι} (hi : i ∈ S) (h : V ≤ₜ T i) : V ≤ₜ famDS S T := by
  obtain ⟨A₁, A₂, A₃, hV⟩ := h
  refine ⟨fun x' p => if p.1 = i then A₁ x' p.2 else 0,
          fun y' q => if q.1 = i then A₂ y' q.2 else 0,
          fun z' r => if r.1 = i then A₃ z' r.2 else 0, ?_⟩
  funext x' y' z'
  rw [act_famDS]
  rw [Finset.sum_eq_single i]
  · rw [hV]
    simp only [act]
    simp
  · intro j _ hj
    refine Finset.sum_eq_zero (fun x _ => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    refine Finset.sum_eq_zero (fun z _ => ?_)
    simp [hj]
  · intro h; exact absurd hi h

/-- Enlarging the index set is a restriction (it is a zero-out). -/
theorem famDS_mono {S S' : Finset ι} (hS : S ⊆ S') (T : ι → Tensor3 R X Y Z) :
    famDS S T ≤ₜ famDS S' T := by
  classical
  refine ⟨fun p p' => if p = p' then (if p.1 ∈ S then (1 : R) else 0) else 0,
          fun q q' => if q = q' then (if q.1 ∈ S then (1 : R) else 0) else 0,
          fun r r' => if r = r' then (if r.1 ∈ S then (1 : R) else 0) else 0, ?_⟩
  rw [act_diag]
  funext p q r
  obtain ⟨i, x⟩ := p; obtain ⟨j, y⟩ := q; obtain ⟨k, z⟩ := r
  simp only [famDS]
  by_cases h1 : i = j
  · by_cases h2 : j = k
    · subst h1; subst h2
      by_cases h3 : i ∈ S
      · simp [h3, hS h3]
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- Two restrictions of disjoint sub-families add. -/
theorem restricts_famDS_add {V₁ V₂ : Tensor3 R X' Y' Z'} {T : ι → Tensor3 R X Y Z}
    {S₁ S₂ : Finset ι} (hd : Disjoint S₁ S₂)
    (h₁ : V₁ ≤ₜ famDS S₁ T) (h₂ : V₂ ≤ₜ famDS S₂ T) :
    (fun x y z => V₁ x y z + V₂ x y z) ≤ₜ famDS (S₁ ∪ S₂) T := by
  classical
  obtain ⟨A₁, A₂, A₃, hV₁⟩ := h₁
  obtain ⟨B₁, B₂, B₃, hV₂⟩ := h₂
  refine ⟨fun x' p => (if p.1 ∈ S₁ then A₁ x' p else 0) + (if p.1 ∈ S₂ then B₁ x' p else 0),
          fun y' q => (if q.1 ∈ S₁ then A₂ y' q else 0) + (if q.1 ∈ S₂ then B₂ y' q else 0),
          fun z' r => (if r.1 ∈ S₁ then A₃ z' r else 0) + (if r.1 ∈ S₂ then B₃ z' r else 0),
          ?_⟩
  funext x' y' z'
  rw [act_famDS]
  have hA : ∀ i ∈ S₁, ∀ x : X, ∀ y : Y, ∀ z : Z,
      ((if i ∈ S₁ then A₁ x' (i, x) else 0) + (if i ∈ S₂ then B₁ x' (i, x) else 0))
        * ((if i ∈ S₁ then A₂ y' (i, y) else 0) + (if i ∈ S₂ then B₂ y' (i, y) else 0))
        * ((if i ∈ S₁ then A₃ z' (i, z) else 0) + (if i ∈ S₂ then B₃ z' (i, z) else 0))
        * T i x y z
      = A₁ x' (i, x) * A₂ y' (i, y) * A₃ z' (i, z) * T i x y z := by
    intro i hi x y z
    have hi₂ : i ∉ S₂ := Finset.disjoint_left.1 hd hi
    simp [hi, hi₂]
  have hB : ∀ i ∈ S₂, ∀ x : X, ∀ y : Y, ∀ z : Z,
      ((if i ∈ S₁ then A₁ x' (i, x) else 0) + (if i ∈ S₂ then B₁ x' (i, x) else 0))
        * ((if i ∈ S₁ then A₂ y' (i, y) else 0) + (if i ∈ S₂ then B₂ y' (i, y) else 0))
        * ((if i ∈ S₁ then A₃ z' (i, z) else 0) + (if i ∈ S₂ then B₃ z' (i, z) else 0))
        * T i x y z
      = B₁ x' (i, x) * B₂ y' (i, y) * B₃ z' (i, z) * T i x y z := by
    intro i hi x y z
    have hi₁ : i ∉ S₁ := Finset.disjoint_right.1 hd hi
    simp [hi, hi₁]
  rw [Finset.sum_union hd]
  have e₁ : (∑ i ∈ S₁, ∑ x : X, ∑ y : Y, ∑ z : Z,
      ((if i ∈ S₁ then A₁ x' (i, x) else 0) + (if i ∈ S₂ then B₁ x' (i, x) else 0))
        * ((if i ∈ S₁ then A₂ y' (i, y) else 0) + (if i ∈ S₂ then B₂ y' (i, y) else 0))
        * ((if i ∈ S₁ then A₃ z' (i, z) else 0) + (if i ∈ S₂ then B₃ z' (i, z) else 0))
        * T i x y z) = V₁ x' y' z' := by
    rw [hV₁, act_famDS]
    exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hA i hi x y z))))
  have e₂ : (∑ i ∈ S₂, ∑ x : X, ∑ y : Y, ∑ z : Z,
      ((if i ∈ S₁ then A₁ x' (i, x) else 0) + (if i ∈ S₂ then B₁ x' (i, x) else 0))
        * ((if i ∈ S₁ then A₂ y' (i, y) else 0) + (if i ∈ S₂ then B₂ y' (i, y) else 0))
        * ((if i ∈ S₁ then A₃ z' (i, z) else 0) + (if i ∈ S₂ then B₃ z' (i, z) else 0))
        * T i x y z) = V₂ x' y' z' := by
    rw [hV₂, act_famDS]
    exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hB i hi x y z))))
  rw [e₁, e₂]

end FamDS

/-! ## The shuffling lemma

This is VXXZ24 Lemma 3.3.  No probability measure appears: the symmetry family is a
`Finset`, and the averaging is the exact counting identity `sum_card_inter_image`. -/

section Shuffle

variable {P ξ : Type*} [Fintype P] [DecidableEq P] [DecidableEq ξ]

/-- Membership in the image of a permutation. -/
theorem mem_image_perm {Q : Type*} [DecidableEq Q] (τ : Equiv.Perm Q) (H : Finset Q) (a : Q) :
    a ∈ H.image τ ↔ τ⁻¹ a ∈ H := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨τ⁻¹ a, h, by simp⟩

/-- **Averaging identity.**  If a uniformly random member of `G` carries a given part to a
uniformly random part, then `∑_{g ∈ G} |A ∩ g(H)| · |P| = |G| · |A| · |H|`. -/
theorem sum_card_inter_image (G : Finset ξ) (t : ξ → Equiv.Perm P)
    (hu : ∀ a b : P, (G.filter (fun g => t g a = b)).card * Fintype.card P = G.card)
    (A H : Finset P) :
    (∑ g ∈ G, (A ∩ H.image (t g)).card) * Fintype.card P
      = G.card * (A.card * H.card) := by
  have h1 : ∀ g : ξ, (A ∩ H.image (t g)).card = (H.filter (fun h => t g h ∈ A)).card := by
    intro g
    rw [← Finset.card_image_of_injective (H.filter (fun h => t g h ∈ A)) (t g).injective]
    congr 1
    ext b
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hb, a, ha, rfl⟩; exact ⟨a, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩; exact ⟨hb, a, ha, rfl⟩
  have h2 : (∑ g ∈ G, (A ∩ H.image (t g)).card)
      = ∑ h ∈ H, ∑ b ∈ A, (G.filter (fun g => t g h = b)).card := by
    rw [Finset.sum_congr rfl (fun g _ => h1 g)]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    exact (Finset.sum_ite_eq A (t g h) (fun _ => 1)).symm
  rw [h2, Finset.sum_mul]
  have h3 : ∀ h ∈ H, (∑ b ∈ A, (G.filter (fun g => t g h = b)).card) * Fintype.card P
      = A.card * G.card := by
    intro h _
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun b _ => hu h b), Finset.sum_const,
      smul_eq_mul]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul]
  ring

/-- **Markov.**  Fewer than a quarter of the family blow the target box up by the factor
`D`, provided the holes occupy at most a `1/(4D)` fraction of the parts. -/
theorem card_bad_lt [Nonempty P] (G : Finset ξ) (hG : G.Nonempty) (t : ξ → Equiv.Perm P)
    (hu : ∀ a b : P, (G.filter (fun g => t g a = b)).card * Fintype.card P = G.card)
    (A H : Finset P) (D : ℕ) (hD : 4 * D * H.card ≤ Fintype.card P) :
    4 * (G.filter (fun g => A.card < (A ∩ H.image (t g)).card * D)).card < G.card := by
  set bad := G.filter (fun g => A.card < (A ∩ H.image (t g)).card * D) with hbad
  have hPpos : 0 < Fintype.card P := Fintype.card_pos
  have hGpos : 0 < G.card := Finset.card_pos.2 hG
  -- the bad members each contribute at least `(A.card + 1) / D`
  have hlow : bad.card * (A.card + 1) ≤ (∑ g ∈ G, (A ∩ H.image (t g)).card) * D := by
    calc bad.card * (A.card + 1)
        = ∑ _g ∈ bad, (A.card + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ g ∈ bad, (A ∩ H.image (t g)).card * D := by
          refine Finset.sum_le_sum (fun g hg => ?_)
          exact (Finset.mem_filter.1 hg).2
      _ ≤ ∑ g ∈ G, (A ∩ H.image (t g)).card * D := by
          refine Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (∑ g ∈ G, (A ∩ H.image (t g)).card) * D := by rw [Finset.sum_mul]
  -- combine with the averaging identity
  have key : 4 * (bad.card * (A.card + 1)) * Fintype.card P
      ≤ G.card * A.card * Fintype.card P := by
    calc 4 * (bad.card * (A.card + 1)) * Fintype.card P
        ≤ 4 * ((∑ g ∈ G, (A ∩ H.image (t g)).card) * D) * Fintype.card P := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlow)
      _ = (G.card * (A.card * H.card)) * (4 * D) := by
          rw [← sum_card_inter_image G t hu A H]; ring
      _ = G.card * A.card * (4 * D * H.card) := by ring
      _ ≤ G.card * A.card * Fintype.card P := Nat.mul_le_mul_left _ hD
  have key2 : 4 * (bad.card * (A.card + 1)) ≤ G.card * A.card :=
    Nat.le_of_mul_le_mul_right key hPpos
  by_contra hcon
  push_neg at hcon
  have e1 : G.card * (A.card + 1) = G.card * A.card + G.card := by ring
  have e2 : 4 * bad.card * (A.card + 1) = 4 * (bad.card * (A.card + 1)) := by ring
  have step1 : G.card * (A.card + 1) ≤ 4 * bad.card * (A.card + 1) :=
    Nat.mul_le_mul_right _ hcon
  omega

end Shuffle

/-! ## Partitioned tensors with a part-transitive symmetry family -/

section Main

variable {X Y Z PX PY PZ ι ξ : Type*}
  [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [Fintype PX] [Fintype PY] [Fintype PZ]
  [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
  [Fintype ι] [DecidableEq ι] [DecidableEq ξ]

/-- The data of VXXZ24 `Property 3.1`: a finite family of symmetries of `T` that permute
the parts, and that carry any given part to a uniformly distributed part. -/
structure Shuffles (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ) (T : Tensor3 R X Y Z)
    (ξ : Type*) [DecidableEq ξ] where
  /-- The family of symmetries. -/
  G : Finset ξ
  /-- The family is nonempty. -/
  ne : G.Nonempty
  /-- The action on `X`-variables. -/
  sX : ξ → Equiv.Perm X
  /-- The action on `Y`-variables. -/
  sY : ξ → Equiv.Perm Y
  /-- The action on `Z`-variables. -/
  sZ : ξ → Equiv.Perm Z
  /-- The induced action on `X`-parts. -/
  tX : ξ → Equiv.Perm PX
  /-- The induced action on `Y`-parts. -/
  tY : ξ → Equiv.Perm PY
  /-- The induced action on `Z`-parts. -/
  tZ : ξ → Equiv.Perm PZ
  /-- `sX` covers `tX`: parts go to whole parts. -/
  partX : ∀ g, ∀ x, pX (sX g x) = tX g (pX x)
  /-- `sY` covers `tY`. -/
  partY : ∀ g, ∀ y, pY (sY g y) = tY g (pY y)
  /-- `sZ` covers `tZ`. -/
  partZ : ∀ g, ∀ z, pZ (sZ g z) = tZ g (pZ z)
  /-- The symmetries preserve the tensor. -/
  inv : ∀ g, ∀ x y z, T (sX g x) (sY g y) (sZ g z) = T x y z
  /-- Part-transitivity in the `X`-dimension. -/
  uniX : ∀ a b : PX, (G.filter (fun g => tX g a = b)).card * Fintype.card PX = G.card
  /-- Part-transitivity in the `Y`-dimension. -/
  uniY : ∀ a b : PY, (G.filter (fun g => tY g a = b)).card * Fintype.card PY = G.card
  /-- Part-transitivity in the `Z`-dimension. -/
  uniZ : ∀ a b : PZ, (G.filter (fun g => tZ g a = b)).card * Fintype.card PZ = G.card

variable {pX : X → PX} {pY : Y → PY} {pZ : Z → PZ} {T : Tensor3 R X Y Z}

/-- **Shuffling lemma** (VXXZ24 Lemma 3.3, with the quantifiers in the order the proof
supports).  For a *fixed* target box and a *fixed* triple of hole sets there is a single
symmetry that simultaneously shrinks the overlap in all three dimensions by the factor
`D`. -/
theorem exists_good_shuffle [Nonempty PX] [Nonempty PY] [Nonempty PZ]
    (S : Shuffles pX pY pZ T ξ) (D : ℕ)
    (A : Finset PX) (C : Finset PY) (E : Finset PZ)
    (HX : Finset PX) (HY : Finset PY) (HZ : Finset PZ)
    (hX : 4 * D * HX.card ≤ Fintype.card PX)
    (hY : 4 * D * HY.card ≤ Fintype.card PY)
    (hZ : 4 * D * HZ.card ≤ Fintype.card PZ) :
    ∃ g ∈ S.G, (A ∩ HX.image (S.tX g)).card * D ≤ A.card
      ∧ (C ∩ HY.image (S.tY g)).card * D ≤ C.card
      ∧ (E ∩ HZ.image (S.tZ g)).card * D ≤ E.card := by
  classical
  set bX := S.G.filter (fun g => A.card < (A ∩ HX.image (S.tX g)).card * D) with hbX
  set bY := S.G.filter (fun g => C.card < (C ∩ HY.image (S.tY g)).card * D) with hbY
  set bZ := S.G.filter (fun g => E.card < (E ∩ HZ.image (S.tZ g)).card * D) with hbZ
  have h1 : 4 * bX.card < S.G.card := card_bad_lt S.G S.ne S.tX S.uniX A HX D hX
  have h2 : 4 * bY.card < S.G.card := card_bad_lt S.G S.ne S.tY S.uniY C HY D hY
  have h3 : 4 * bZ.card < S.G.card := card_bad_lt S.G S.ne S.tZ S.uniZ E HZ D hZ
  by_contra hcon
  push_neg at hcon
  have hsub : S.G ⊆ bX ∪ bY ∪ bZ := by
    intro g hg
    rcases lt_or_ge A.card ((A ∩ HX.image (S.tX g)).card * D) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hg, h⟩))
    rcases lt_or_ge C.card ((C ∩ HY.image (S.tY g)).card * D) with h' | h'
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hg, h'⟩))
    have h'' := hcon g hg h h'
    exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hg, h''⟩)
  have hcard : S.G.card ≤ bX.card + bY.card + bZ.card := by
    calc S.G.card ≤ (bX ∪ bY ∪ bZ).card := Finset.card_le_card hsub
      _ ≤ (bX ∪ bY).card + bZ.card := Finset.card_union_le _ _
      _ ≤ bX.card + bY.card + bZ.card := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  omega

/-- One broken copy, relabelled by a symmetry and then zeroed out, produces any box whose
parts avoid the shifted holes. -/
theorem boxZO_restricts_broken (S : Shuffles pX pY pZ T ξ) (g : ξ)
    (HX : Finset PX) (HY : Finset PY) (HZ : Finset PZ)
    (A : Finset PX) (C : Finset PY) (E : Finset PZ)
    (hA : A ⊆ (HX.image (S.tX g))ᶜ) (hC : C ⊆ (HY.image (S.tY g))ᶜ)
    (hE : E ⊆ (HZ.image (S.tZ g))ᶜ) :
    boxZO pX pY pZ A C E T ≤ₜ boxZO pX pY pZ HXᶜ HYᶜ HZᶜ T := by
  classical
  set U := boxZO pX pY pZ HXᶜ HYᶜ HZᶜ T with hU
  set W : Tensor3 R X Y Z :=
    fun x y z => U ((S.sX g)⁻¹ x) ((S.sY g)⁻¹ y) ((S.sZ g)⁻¹ z) with hW
  -- `W` is the same broken copy with the holes moved by `g`
  have hWeq : W = boxZO pX pY pZ (HX.image (S.tX g))ᶜ (HY.image (S.tY g))ᶜ
      (HZ.image (S.tZ g))ᶜ T := by
    funext x y z
    have ex : pX ((S.sX g)⁻¹ x) = (S.tX g)⁻¹ (pX x) := by
      have h := S.partX g ((S.sX g)⁻¹ x)
      simp only [Equiv.Perm.apply_inv_self] at h
      rw [h, Equiv.Perm.inv_apply_self]
    have ey : pY ((S.sY g)⁻¹ y) = (S.tY g)⁻¹ (pY y) := by
      have h := S.partY g ((S.sY g)⁻¹ y)
      simp only [Equiv.Perm.apply_inv_self] at h
      rw [h, Equiv.Perm.inv_apply_self]
    have ez : pZ ((S.sZ g)⁻¹ z) = (S.tZ g)⁻¹ (pZ z) := by
      have h := S.partZ g ((S.sZ g)⁻¹ z)
      simp only [Equiv.Perm.apply_inv_self] at h
      rw [h, Equiv.Perm.inv_apply_self]
    have eT : T ((S.sX g)⁻¹ x) ((S.sY g)⁻¹ y) ((S.sZ g)⁻¹ z) = T x y z := by
      have := S.inv g ((S.sX g)⁻¹ x) ((S.sY g)⁻¹ y) ((S.sZ g)⁻¹ z)
      simpa using this.symm
    have mX : ((S.tX g)⁻¹ (pX x) ∈ HXᶜ) ↔ (pX x ∈ (HX.image (S.tX g))ᶜ) := by
      simp only [Finset.mem_compl, mem_image_perm]
    have mY : ((S.tY g)⁻¹ (pY y) ∈ HYᶜ) ↔ (pY y ∈ (HY.image (S.tY g))ᶜ) := by
      simp only [Finset.mem_compl, mem_image_perm]
    have mZ : ((S.tZ g)⁻¹ (pZ z) ∈ HZᶜ) ↔ (pZ z ∈ (HZ.image (S.tZ g))ᶜ) := by
      simp only [Finset.mem_compl, mem_image_perm]
    have hcond : (pX ((S.sX g)⁻¹ x) ∈ HXᶜ ∧ pY ((S.sY g)⁻¹ y) ∈ HYᶜ
          ∧ pZ ((S.sZ g)⁻¹ z) ∈ HZᶜ)
        ↔ (pX x ∈ (HX.image (S.tX g))ᶜ ∧ pY y ∈ (HY.image (S.tY g))ᶜ
            ∧ pZ z ∈ (HZ.image (S.tZ g))ᶜ) := by
      rw [ex, ey, ez]
      exact and_congr mX (and_congr mY mZ)
    simp only [hW, hU, boxZO, eT]
    exact if_congr hcond rfl rfl
  have hWU : W ≤ₜ U := by
    refine ⟨fun x' x => if x = (S.sX g)⁻¹ x' then (1 : R) else 0,
            fun y' y => if y = (S.sY g)⁻¹ y' then (1 : R) else 0,
            fun z' z => if z = (S.sZ g)⁻¹ z' then (1 : R) else 0, ?_⟩
    rw [act_perm]
  have hstep : boxZO pX pY pZ A C E T ≤ₜ W := by
    rw [hWeq]
    exact boxZO_mono pX pY pZ hA hC hE T
  exact Tensor3.Restricts.trans hstep hWU

/-- **Fixing holes** (VXXZ24 Theorem 3.1 / Corollary 3.2, ADVXXZ `thm:fix-holes`).

`4 ^ k` broken copies of `T`, each missing at most a `1/(4D)` fraction of the parts in
each of the three modes, restrict onto the unbroken box `A × C × E`, as soon as
`log_D |A| + log_D |C| + log_D |E| < k`.

With `D = 2N`, `|PX|, |PY|, |PZ| ≤ 3 ^ N` and holes a `1/(8N)` fraction this gives
`k = O(N / log N)`, i.e. `2 ^ o(N)` copies, which is what the laser method consumes. -/
theorem holes_restrict [Nonempty PX] [Nonempty PY] [Nonempty PZ]
    (S : Shuffles pX pY pZ T ξ) (D : ℕ) (hD : 2 ≤ D)
    (HX : ι → Finset PX) (HY : ι → Finset PY) (HZ : ι → Finset PZ)
    (hX : ∀ i, 4 * D * (HX i).card ≤ Fintype.card PX)
    (hY : ∀ i, 4 * D * (HY i).card ≤ Fintype.card PY)
    (hZ : ∀ i, 4 * D * (HZ i).card ≤ Fintype.card PZ) :
    ∀ (k : ℕ) (A : Finset PX) (C : Finset PY) (E : Finset PZ) (Sx : Finset ι),
      Nat.log D A.card + Nat.log D C.card + Nat.log D E.card < k →
      4 ^ k ≤ Sx.card →
      boxZO pX pY pZ A C E T ≤ₜ
        famDS Sx (fun i => boxZO pX pY pZ (HX i)ᶜ (HY i)ᶜ (HZ i)ᶜ T) := by
  classical
  set Br : ι → Tensor3 R X Y Z :=
    fun i => boxZO pX pY pZ (HX i)ᶜ (HY i)ᶜ (HZ i)ᶜ T with hBr
  intro k
  induction k with
  | zero => intro A C E Sx hlog _; omega
  | succ k ih =>
    intro A C E Sx hlog hcard
    -- shrinking one side by the factor `D` drops one from the `log`-budget
    have shrink : ∀ (m m' : ℕ), m' * D ≤ m → 1 ≤ m' → Nat.log D m' + 1 ≤ Nat.log D m := by
      intro m m' hm hm'
      have hDpos : 0 < D := by omega
      have hle : m' ≤ m / D := (Nat.le_div_iff_mul_le hDpos).2 hm
      have h1 : Nat.log D m' ≤ Nat.log D (m / D) := Nat.log_mono_right hle
      have h2 : Nat.log D (m / D) = Nat.log D m - 1 := Nat.log_div_base D m
      have hDm : D ≤ m := by
        have h4 : 1 * D ≤ m' * D := mul_le_mul_right' hm' D
        omega
      have h3 : 0 < Nat.log D m := Nat.log_pos (by omega) hDm
      omega
    rcases Finset.eq_empty_or_nonempty A with hA0 | hAne
    · rw [hA0, boxZO_empty_left]; exact zero_restricts _
    rcases Finset.eq_empty_or_nonempty C with hC0 | hCne
    · rw [hC0, boxZO_empty_mid]; exact zero_restricts _
    rcases Finset.eq_empty_or_nonempty E with hE0 | hE0ne
    · rw [hE0, boxZO_empty_right]; exact zero_restricts _
    -- pick the copy to consume
    have hSxne : Sx.Nonempty := by
      refine Finset.card_pos.1 ?_
      have : 0 < 4 ^ (k + 1) := pow_pos (by norm_num : 0 < 4) (k + 1)
      omega
    obtain ⟨i₀, hi₀⟩ := hSxne
    obtain ⟨g, _, hgA, hgC, hgE⟩ :=
      exists_good_shuffle S D A C E (HX i₀) (HY i₀) (HZ i₀) (hX i₀) (hY i₀) (hZ i₀)
    set A₀ := A ∩ (HX i₀).image (S.tX g) with hA₀
    set C₀ := C ∩ (HY i₀).image (S.tY g) with hC₀
    set E₀ := E ∩ (HZ i₀).image (S.tZ g) with hE₀
    set A₁ := A \ A₀ with hA₁
    set C₁ := C \ C₀ with hC₁
    set E₁ := E \ E₀ with hE₁
    have hAu : A₀ ∪ A₁ = A := Finset.union_sdiff_of_subset (Finset.inter_subset_left)
    have hCu : C₀ ∪ C₁ = C := Finset.union_sdiff_of_subset (Finset.inter_subset_left)
    have hEu : E₀ ∪ E₁ = E := Finset.union_sdiff_of_subset (Finset.inter_subset_left)
    have hAd : Disjoint A₀ A₁ := Finset.disjoint_sdiff
    have hCd : Disjoint C₀ C₁ := Finset.disjoint_sdiff
    have hEd : Disjoint E₀ E₁ := Finset.disjoint_sdiff
    -- carve the index set: one copy plus three groups of `4 ^ k`
    have hpow : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
    have hSx' : 3 * 4 ^ k ≤ (Sx.erase i₀).card := by
      rw [Finset.card_erase_of_mem hi₀]; omega
    have cd1 : 4 ^ k ≤ (Sx.erase i₀).card := by omega
    obtain ⟨S1, hS1sub, hS1card⟩ := Finset.exists_subset_card_eq cd1
    have cd2 : 2 * 4 ^ k ≤ ((Sx.erase i₀) \ S1).card := by
      rw [Finset.card_sdiff]
      have h : (S1 ∩ (Sx.erase i₀)).card ≤ S1.card :=
        Finset.card_le_card Finset.inter_subset_left
      omega
    obtain ⟨S2, hS2sub, hS2card⟩ :=
      Finset.exists_subset_card_eq (le_trans (by omega : 4 ^ k ≤ 2 * 4 ^ k) cd2)
    have cd3 : 4 ^ k ≤ (((Sx.erase i₀) \ S1) \ S2).card := by
      rw [Finset.card_sdiff]
      have h : (S2 ∩ ((Sx.erase i₀) \ S1)).card ≤ S2.card :=
        Finset.card_le_card Finset.inter_subset_left
      omega
    obtain ⟨S3, hS3sub, hS3card⟩ := Finset.exists_subset_card_eq cd3
    have hS2sub' : S2 ⊆ Sx.erase i₀ := hS2sub.trans Finset.sdiff_subset
    have hS3sub' : S3 ⊆ Sx.erase i₀ :=
      hS3sub.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
    have hd12 : Disjoint S1 S2 := by
      refine Finset.disjoint_left.2 (fun a ha ha2 => ?_)
      have hmem := hS2sub ha2
      simp only [Finset.mem_sdiff] at hmem
      exact hmem.2 ha
    have hd13 : Disjoint S1 S3 := by
      refine Finset.disjoint_left.2 (fun a ha ha3 => ?_)
      have hmem := hS3sub ha3
      simp only [Finset.mem_sdiff] at hmem
      exact hmem.1.2 ha
    have hd23 : Disjoint S2 S3 := by
      refine Finset.disjoint_left.2 (fun a ha ha3 => ?_)
      have hmem := hS3sub ha3
      simp only [Finset.mem_sdiff] at hmem
      exact hmem.2 ha
    have hd0 : ∀ {W : Finset ι}, W ⊆ Sx.erase i₀ → Disjoint W ({i₀} : Finset ι) := by
      intro W hWsub
      refine Finset.disjoint_right.2 (fun a ha haW => ?_)
      simp only [Finset.mem_singleton] at ha
      subst ha
      exact (Finset.mem_erase.1 (hWsub haW)).1 rfl
    -- the consumed copy handles the box that avoids all the shifted holes
    have h4 : boxZO pX pY pZ A₁ C₁ E₁ T ≤ₜ famDS ({i₀} : Finset ι) Br := by
      refine restricts_famDS_of_mem (Finset.mem_singleton_self i₀) ?_
      refine boxZO_restricts_broken S g (HX i₀) (HY i₀) (HZ i₀) A₁ C₁ E₁ ?_ ?_ ?_
      · intro a ha
        simp only [hA₁, Finset.mem_sdiff, hA₀, Finset.mem_inter] at ha
        simp only [Finset.mem_compl]
        exact fun h => ha.2 ⟨ha.1, h⟩
      · intro a ha
        simp only [hC₁, Finset.mem_sdiff, hC₀, Finset.mem_inter] at ha
        simp only [Finset.mem_compl]
        exact fun h => ha.2 ⟨ha.1, h⟩
      · intro a ha
        simp only [hE₁, Finset.mem_sdiff, hE₀, Finset.mem_inter] at ha
        simp only [Finset.mem_compl]
        exact fun h => ha.2 ⟨ha.1, h⟩
    -- the three recursive sub-boxes
    have h1 : boxZO pX pY pZ A₀ C E T ≤ₜ famDS S1 Br := by
      rcases Finset.eq_empty_or_nonempty A₀ with h | h
      · rw [h, boxZO_empty_left]; exact zero_restricts _
      · refine ih A₀ C E S1 ?_ (by omega)
        have := shrink A.card A₀.card hgA (Finset.card_pos.2 h)
        omega
    have h2 : boxZO pX pY pZ A₁ C₀ E T ≤ₜ famDS S2 Br := by
      rcases Finset.eq_empty_or_nonempty C₀ with h | h
      · rw [h, boxZO_empty_mid]; exact zero_restricts _
      · refine ih A₁ C₀ E S2 ?_ (by omega)
        have hle : Nat.log D A₁.card ≤ Nat.log D A.card :=
          Nat.log_mono_right (Finset.card_le_card Finset.sdiff_subset)
        have := shrink C.card C₀.card hgC (Finset.card_pos.2 h)
        omega
    have h3 : boxZO pX pY pZ A₁ C₁ E₀ T ≤ₜ famDS S3 Br := by
      rcases Finset.eq_empty_or_nonempty E₀ with h | h
      · rw [h, boxZO_empty_right]; exact zero_restricts _
      · refine ih A₁ C₁ E₀ S3 ?_ (by omega)
        have hleA : Nat.log D A₁.card ≤ Nat.log D A.card :=
          Nat.log_mono_right (Finset.card_le_card Finset.sdiff_subset)
        have hleC : Nat.log D C₁.card ≤ Nat.log D C.card :=
          Nat.log_mono_right (Finset.card_le_card Finset.sdiff_subset)
        have := shrink E.card E₀.card hgE (Finset.card_pos.2 h)
        omega
    -- assemble
    have c34 := restricts_famDS_add (hd0 hS3sub') h3 h4
    have c234 := restricts_famDS_add
      (Finset.disjoint_union_right.2 ⟨hd23, hd0 hS2sub'⟩) h2 c34
    have c1234 := restricts_famDS_add
      (Finset.disjoint_union_right.2 ⟨hd12, Finset.disjoint_union_right.2
        ⟨hd13, hd0 hS1sub⟩⟩) h1 c234
    have hfinal : boxZO pX pY pZ A C E T
        = fun x y z => boxZO pX pY pZ A₀ C E T x y z
          + (boxZO pX pY pZ A₁ C₀ E T x y z
            + (boxZO pX pY pZ A₁ C₁ E₀ T x y z + boxZO pX pY pZ A₁ C₁ E₁ T x y z)) := by
      conv_lhs => rw [← hAu, ← hCu, ← hEu]
      rw [boxZO_split pX pY pZ A₀ A₁ C₀ C₁ E₀ E₁ hAd hCd hEd T, hCu, hEu]
    rw [hfinal]
    refine Tensor3.Restricts.trans c1234 (famDS_mono ?_ Br)
    have hsub1 : S1 ⊆ Sx := hS1sub.trans (Finset.erase_subset _ _)
    have hsub2 : S2 ⊆ Sx := hS2sub'.trans (Finset.erase_subset _ _)
    have hsub3 : S3 ⊆ Sx := hS3sub'.trans (Finset.erase_subset _ _)
    refine Finset.union_subset hsub1 (Finset.union_subset hsub2
      (Finset.union_subset hsub3 ?_))
    simpa using hi₀

/-- The full box is the whole tensor. -/
theorem boxZO_univ (T : Tensor3 R X Y Z) :
    boxZO pX pY pZ (Finset.univ : Finset PX) (Finset.univ : Finset PY)
      (Finset.univ : Finset PZ) T = T := by
  funext x y z; simp [boxZO]

/-- **Fixing holes, in the form the laser method consumes.**

`4 ^ (log_D |PX| + log_D |PY| + log_D |PZ| + 1)` broken copies of `T`, each missing at most
a `1/(4D)` fraction of the parts in every mode, restrict onto an unbroken `T`.

In VXXZ24 / ADVXXZ this is applied with `D = 2N`, where the number of parts in each mode is
at most `3 ^ N` and the hole fraction is at most `1/(8N)`; the copy count is then
`4 ^ (3 · log_{2N}(3 ^ N) + 1) = 2 ^ O(N / log N) = 2 ^ o(N)`, which the asymptotic sum
inequality absorbs. -/
theorem holes_restrict_univ [Nonempty PX] [Nonempty PY] [Nonempty PZ]
    (S : Shuffles pX pY pZ T ξ) (D : ℕ) (hD : 2 ≤ D)
    (HX : ι → Finset PX) (HY : ι → Finset PY) (HZ : ι → Finset PZ)
    (hX : ∀ i, 4 * D * (HX i).card ≤ Fintype.card PX)
    (hY : ∀ i, 4 * D * (HY i).card ≤ Fintype.card PY)
    (hZ : ∀ i, 4 * D * (HZ i).card ≤ Fintype.card PZ)
    (Sx : Finset ι)
    (hcard : 4 ^ (Nat.log D (Fintype.card PX) + Nat.log D (Fintype.card PY)
        + Nat.log D (Fintype.card PZ) + 1) ≤ Sx.card) :
    T ≤ₜ famDS Sx (fun i => boxZO pX pY pZ (HX i)ᶜ (HY i)ᶜ (HZ i)ᶜ T) := by
  have h := holes_restrict S D hD HX HY HZ hX hY hZ
      (Nat.log D (Fintype.card PX) + Nat.log D (Fintype.card PY)
        + Nat.log D (Fintype.card PZ) + 1)
      Finset.univ Finset.univ Finset.univ Sx
      (by rw [Finset.card_univ, Finset.card_univ, Finset.card_univ]; omega) hcard
  rwa [boxZO_univ] at h

end Main

end ADVXXZHoles
end OmegaBound
