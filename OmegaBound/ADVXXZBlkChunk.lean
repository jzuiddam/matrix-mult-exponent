import OmegaBound.ADVXXZSplitIface

/-!
# The level-`ℓ` → level-`(ℓ-1)` chunk split

Vassilevska Williams–Xu–Xu–Zhou, `prelim.tex:157-158`, record that the level-`ℓ` partition is
a coarsening of the level-`(ℓ-1)` one:

  `X_i^{(ℓ)} = ⨆_{i' + i'' = i} X_{i'}^{(ℓ-1)} ⊗ X_{i''}^{(ℓ-1)}`.

At width `w = 2^{ℓ-1} = a + b` this is the statement that a level-1 word of width `a+b`
splits into its first `a` and last `b` letters, that the level index is the sum of the two
level indices, and that `T^{(ℓ)} = T^{(ℓ-1)} ⊗ T^{(ℓ-1)}` under that splitting.  Since
`ADVXXZSplitDist` makes a level-1 word literally a function `Fin w → Fin 3`, the split is
`Fin.append`/`Fin.castAdd`/`Fin.natAdd` and **no index arithmetic occurs**: `Fin.sum_univ_add`
and `Fin.prod_univ_add` do all of it.

Everything is stated for a general split `w = a + b`, not only the halving `a = b`, which is
both more general and free of `2^{ℓ-1} = 2·2^{ℓ-2}` rewriting.

## Design

Following `ADVXXZSplitIface`, the two halves are taken by **precomposition**
(`legFst x = x ∘ Fin.castAdd b`), never by a subtype or a `cast`; that is why
no lemma below needs a `cast`.

## Main definitions

* `legFst`, `legSnd`, `legApp`, `legPairEquiv` — the split of a leg (or a word) of width
  `a + b`, and `chunkPairEquiv : Chunk (a+b) ≃ Chunk a × Chunk b`.
* `RatDist.ext`, `RatDist.map_map` — the missing structural lemmas about `RatDist`.
* `SplitDist.concat` — the source's `α × β` for concatenation (`prelim.tex:198-200`).

## Main results

* `chunkLvl_append`, `chunkLvl_eq_add` — the level index is additive under concatenation.
  This is `prelim.tex:158`.
* `RatDist.map_map` — pushforwards compose.
* `SplitDist.concat_num`, `SplitDist.concat_den` — the concatenation product, coordinatewise.

## A source defect

**`prelim.tex:158` bounds the summation index by `2^ℓ` where it must be `2^{ℓ-1}`.**  The
display reads `⨆_{0 ≤ i' ≤ i, 0 ≤ i', i−i' ≤ 2^ℓ} X^{(ℓ-1)}_{i'} ⊗ X^{(ℓ-1)}_{i−i'}`, but a
level-`(ℓ−1)` block index runs over `0,…,2^{ℓ-1}`, so `X^{(ℓ-1)}_{i'}` is undefined for
`2^{ℓ-1} < i' ≤ 2^ℓ`.  (The extra terms are empty, so the union is still correct; the
constraint `0 ≤ i' ≤ i` is also redundant given `0 ≤ i − i'`.)  Here the statement carries no
range at all: `chunkLvl_eq_add` says the two halves' levels *add*.
-/

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZ

open CW90 CW90Eight

/-! ## Splitting a leg of width `a + b` -/

section Split

variable {A : Type*} {a b : ℕ}

/-- The first `a` letters of a width-`(a+b)` word or leg.  A precomposition, never a
`cast`. -/
def legFst (x : Fin (a + b) → A) : Fin a → A := fun p => x (Fin.castAdd b p)

/-- The last `b` letters of a width-`(a+b)` word or leg. -/
def legSnd (x : Fin (a + b) → A) : Fin b → A := fun p => x (Fin.natAdd a p)

/-- Concatenation of a width-`a` and a width-`b` word or leg. -/
def legApp (u : Fin a → A) (v : Fin b → A) : Fin (a + b) → A := Fin.append u v

@[simp] theorem legFst_legApp (u : Fin a → A) (v : Fin b → A) : legFst (legApp u v) = u := by
  funext p
  exact Fin.append_left u v p

@[simp] theorem legSnd_legApp (u : Fin a → A) (v : Fin b → A) : legSnd (legApp u v) = v := by
  funext p
  exact Fin.append_right u v p

@[simp] theorem legApp_legFst_legSnd (x : Fin (a + b) → A) :
    legApp (legFst x) (legSnd x) = x := by
  funext i
  refine Fin.addCases (fun p => ?_) (fun p => ?_) i
  · rw [legApp, Fin.append_left]; rfl
  · rw [legApp, Fin.append_right]; rfl

/-- **`(Fin (a+b) → A) ≃ (Fin a → A) × (Fin b → A)`** — the chunk split, with both round
trips `rfl`-free of casts. -/
def legPairEquiv (A : Type*) (a b : ℕ) :
    (Fin (a + b) → A) ≃ ((Fin a → A) × (Fin b → A)) where
  toFun x := (legFst x, legSnd x)
  invFun p := legApp p.1 p.2
  left_inv x := legApp_legFst_legSnd x
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact legFst_legApp p.1 p.2
    · exact legSnd_legApp p.1 p.2

end Split

/-- **`Chunk (a+b) ≃ Chunk a × Chunk b`** — the level-1 words of width `a+b` are the pairs of
a width-`a` and a width-`b` word.  `prelim.tex:157-158`. -/
abbrev chunkPairEquiv (a b : ℕ) : Chunk (a + b) ≃ Chunk a × Chunk b :=
  legPairEquiv (Fin 3) a b

/-! ## The level index is additive -/

section LevelAdd

variable {a b : ℕ}

/-- **`chunkLvl` is additive under concatenation.** -/
theorem chunkLvl_append (σ : Chunk a) (τ : Chunk b) :
    chunkLvl (legApp σ τ) = chunkLvl σ + chunkLvl τ := by
  rw [chunkLvl, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by rw [legApp, Fin.append_left]
  · exact Finset.sum_congr rfl fun p _ => by rw [legApp, Fin.append_right]

/-- **`chunkLvl` splits as the sum of the two halves' levels.** -/
theorem chunkLvl_eq_add (σ : Chunk (a + b)) :
    chunkLvl σ = chunkLvl (legFst σ) + chunkLvl (legSnd σ) := by
  conv_lhs => rw [← legApp_legFst_legSnd σ]
  exact chunkLvl_append _ _

end LevelAdd

section Variables

variable {q a b : ℕ}

end Variables

/-! ## Two structural lemmas about `RatDist` -/

namespace RatDist

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- Two `RatDist`s with the same numerators and denominator are equal (the two remaining
fields are proofs). -/
theorem ext {P Q : RatDist ι} (hnum : P.num = Q.num) (hden : P.den = Q.den) : P = Q := by
  cases P
  cases Q
  simp only at hnum hden
  subst hnum
  subst hden
  rfl

/-- **Pushforwards compose.**  This is what lets a level-`ℓ` marginal be computed from a
level-`(ℓ-1)` one. -/
theorem map_map [DecidableEq κ] [DecidableEq ν] (g : ι → κ) (h : κ → ν) (P : RatDist ι) :
    (P.map g).map h = P.map (h ∘ g) := by
  refine RatDist.ext ?_ rfl
  funext v
  rw [map_num, map_num]
  simp only [Function.comp_apply]
  have hmaps : ∀ i ∈ Finset.univ.filter fun i => h (g i) = v,
      g i ∈ Finset.univ.filter fun c => h c = v := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps P.num]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_filter] at hc
  rw [map_num]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact ⟨by rw [hi]; exact hc.2, hi⟩
  · intro hi
    exact hi.2

end RatDist

section SplitFactor

variable {a b n : ℕ}

end SplitFactor

/-! ## The concatenation product `α × β`

`prelim.tex:198-200` defines the product of two distributions on integer sequences as the
distribution on concatenations.  This is that product, in the integrality convention. -/

namespace SplitDist

variable {a b : ℕ}

/-- **The concatenation product of two complete split distributions.** -/
def concat (Pa : SplitDist a) (Pb : SplitDist b) : SplitDist (a + b) where
  num σ := Pa.num (legFst σ) * Pb.num (legSnd σ)
  den := Pa.den * Pb.den
  den_pos := Nat.mul_pos Pa.den_pos Pb.den_pos
  sum_num := by
    have h : ∑ σ : Chunk (a + b), Pa.num (legFst σ) * Pb.num (legSnd σ)
        = ∑ p : Chunk a × Chunk b, Pa.num p.1 * Pb.num p.2 :=
      Equiv.sum_comp (chunkPairEquiv a b) fun p => Pa.num p.1 * Pb.num p.2
    rw [h, Fintype.sum_prod_type]
    calc ∑ u : Chunk a, ∑ v : Chunk b, Pa.num u * Pb.num v
        = ∑ u : Chunk a, Pa.num u * Pb.den :=
          Finset.sum_congr rfl fun u _ => by rw [← Finset.mul_sum, Pb.sum_num]
      _ = Pa.den * Pb.den := by rw [← Finset.sum_mul, Pa.sum_num]

@[simp] theorem concat_num (Pa : SplitDist a) (Pb : SplitDist b) (σ : Chunk (a + b)) :
    (Pa.concat Pb).num σ = Pa.num (legFst σ) * Pb.num (legSnd σ) := rfl

@[simp] theorem concat_den (Pa : SplitDist a) (Pb : SplitDist b) :
    (Pa.concat Pb).den = Pa.den * Pb.den := rfl

end SplitDist

end ADVXXZ
end OmegaBound
