import OmegaBound.ADVXXZSplitIface
import OmegaBound.CW90EightDSum

/-!
# The degeneration plumbing of the two stage theorems

Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou state their two stage theorems — Theorem 4.2
(`global.tex:118-130`, the global stage) and Theorem 5.3 (`constituent.tex:138-150`, the
constituent stage) — as corollaries of the corresponding `ε = 0` propositions
(`prop:global-stage-no-eps`, `prop:constituent-stage-no-eps`), with the proofs *omitted*:
"We omit its proof as it is similar to the proof of [VXXZ24, Theorem 5.3]", resp. "The proof
of Theorem 5.3 assuming Proposition 5.2 is the same as the proof of [VXXZ24, Theorem 6.3],
so we omit the proof here."

So the proof that has to be formalised is Vassilevska Williams–Xu–Xu–Zhou's, at
`analysis_global.tex:77-104`.  This module holds the `ADVXXZHoles.famDS` direct-sum calculus
that argument uses.

## Main results

* `sum_restricts_famDS` — **a sum of tensors is a restriction of their direct sum**, the
  source's last sentence ("because a direct sum of some tensors can be degenerated into the
  sum of these tensors").
* `famDS_swap`, `famDS_const_mono`, `famDS_copies_mono` — the regrouping of a double direct
  sum, and monotonicity in the summand and in the number of copies.
-/

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZStage

open ADVXXZHoles CW90Eight


section TransRestricts

variable {F : Type*} [Field F]

end TransRestricts


section FamDS

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']

end FamDS

/-! ## Sums, swaps and monotonicity of `famDS` -/

section FamDSCalc

variable {R : Type*} [CommSemiring R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {X Y Z X' Y' Z' : Type}
  [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']

/-- **A sum of tensors is a restriction of their direct sum.**  This is the last step of
`analysis_global.tex:99`: "because a direct sum of some tensors can be degenerated into the
sum of these tensors, the theorem follows".  It is in fact a restriction, not merely a
degeneration. -/
theorem sum_restricts_famDS (S : Finset ι) (T : ι → Tensor3 R X Y Z) :
    (fun x y z => ∑ i ∈ S, T i x y z) ≤ₜ famDS S T := by
  classical
  refine ⟨fun x' p => if p.2 = x' then 1 else 0, fun y' q => if q.2 = y' then 1 else 0,
    fun z' r => if r.2 = z' then 1 else 0, ?_⟩
  funext x y z
  rw [act_famDS]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · rw [Finset.sum_eq_single z]
      · simp
      · intro c _ hc; simp [hc]
      · intro hc; exact absurd (Finset.mem_univ z) hc
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => by simp [hb]
    · intro hc; exact absurd (Finset.mem_univ y) hc
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => by simp [ha]
  · intro hc; exact absurd (Finset.mem_univ x) hc

/-- **Restricting the summand restricts the direct sum**, for a constant family. -/
theorem famDS_const_mono (S : Finset ι) {V : Tensor3 R X' Y' Z'} {W : Tensor3 R X Y Z}
    (h : V ≤ₜ W) : famDS S (fun _ => V) ≤ₜ famDS S (fun _ => W) := by
  classical
  obtain ⟨A₁, A₂, A₃, hV⟩ := h
  refine ⟨fun p q => if q.1 = p.1 then A₁ p.2 q.2 else 0,
    fun p q => if q.1 = p.1 then A₂ p.2 q.2 else 0,
    fun p q => if q.1 = p.1 then A₃ p.2 q.2 else 0, ?_⟩
  funext p q r
  obtain ⟨i, x'⟩ := p; obtain ⟨j, y'⟩ := q; obtain ⟨k, z'⟩ := r
  rw [act_famDS, famDS_apply]
  have hz1 : ∀ l : ι, ¬ (l = i) →
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (if l = i then A₁ x' a else 0) * (if l = j then A₂ y' b else 0)
          * (if l = k then A₃ z' c else 0) * W a b c) = 0 := fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => by rw [if_neg hl]; ring
  have hz2 : ∀ l : ι, ¬ (l = j) →
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (if l = i then A₁ x' a else 0) * (if l = j then A₂ y' b else 0)
          * (if l = k then A₃ z' c else 0) * W a b c) = 0 := fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => by rw [if_neg hl]; ring
  have hz3 : ∀ l : ι, ¬ (l = k) →
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (if l = i then A₁ x' a else 0) * (if l = j then A₂ y' b else 0)
          * (if l = k then A₃ z' c else 0) * W a b c) = 0 := fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => by rw [if_neg hl]; ring
  have key : ∀ l : ι,
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (if l = i then A₁ x' a else 0) * (if l = j then A₂ y' b else 0)
          * (if l = k then A₃ z' c else 0) * W a b c)
        = if l = i then (if i = j then (if j = k then V x' y' z' else 0) else 0) else 0 := by
    intro l
    by_cases h1 : l = i
    · rw [if_pos h1]
      by_cases h2 : i = j
      · rw [if_pos h2]
        by_cases h3 : j = k
        · rw [if_pos h3, hV]
          simp only [act, if_pos h1, if_pos (h1.trans h2), if_pos ((h1.trans h2).trans h3)]
        · rw [if_neg h3]
          exact hz3 l fun hc => h3 ((h1.trans h2).symm.trans hc)
      · rw [if_neg h2]
        exact hz2 l fun hc => h2 (h1.symm.trans hc)
    · rw [if_neg h1]
      exact hz1 l h1
  rw [Finset.sum_congr rfl fun l _ => key l, Finset.sum_ite_eq']
  by_cases h1 : i = j
  · by_cases h2 : j = k
    · by_cases h3 : i ∈ S <;> simp [h1, h2, h3]
    · simp [h2]
  · simp [h1]

/-- **Swapping the two indices of a double direct sum**: `⊕_m ⊕_ξ = ⊕_ξ ⊕_m`, over full
index types. -/
theorem famDS_swap [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (T : ι → Tensor3 R X Y Z) :
    famDS (Finset.univ : Finset κ) (fun _ => famDS (Finset.univ : Finset ι) T)
      ≤ₜ famDS (Finset.univ : Finset ι)
          (fun i => famDS (Finset.univ : Finset κ) fun _ => T i) := by
  classical
  refine ADVXXZ.restricts_of_sub (fun p => (p.2.1, (p.1, p.2.2)))
    (fun q => (q.2.1, (q.1, q.2.2))) (fun r => (r.2.1, (r.1, r.2.2))) ?_
  rintro ⟨m, i, x⟩ ⟨m', i', y⟩ ⟨m'', i'', z⟩
  simp only [famDS_apply, Finset.mem_univ, if_true]
  ring

/-- **Fewer copies is a restriction of more copies.** -/
theorem famDS_copies_mono [DecidableEq X] [DecidableEq Y] [DecidableEq Z] {C C' : ℕ}
    (hC : C ≤ C') (V : Tensor3 R X Y Z) :
    famDS (Finset.univ : Finset (Fin C)) (fun _ => V)
      ≤ₜ famDS (Finset.univ : Finset (Fin C')) (fun _ => V) := by
  classical
  refine ADVXXZ.restricts_of_sub (fun p => (Fin.castLE hC p.1, p.2))
    (fun q => (Fin.castLE hC q.1, q.2)) (fun r => (Fin.castLE hC r.1, r.2)) ?_
  rintro ⟨m, x⟩ ⟨m', y⟩ ⟨m'', z⟩
  simp only [famDS_apply, Finset.mem_univ, if_true, Fin.ext_iff, Fin.coe_castLE]

end FamDSCalc


section Stage

variable {G₀ : Type} [Fintype G₀] [DecidableEq G₀]
  {XI YI ZI XO YO ZO : Type} [Fintype XI] [Fintype YI] [Fintype ZI]
  [Fintype XO] [Fintype YO] [Fintype ZO]

end Stage

end ADVXXZStage

end OmegaBound
