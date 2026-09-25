import OmegaBound.ADVXXZIfaceCol
import OmegaBound.ADVXXZMulGlue
import OmegaBound.ADVXXZBlkCount
import OmegaBound.ADVXXZHashRung
import OmegaBound.ADVXXZSplitIface
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-!
# Group families acting on level-1 blocks

Ingredients for an `ADVXXZHoles.Shuffles` family on the CW interface tensor, whose parts are the
level-1 blocks of a leg and whose symmetries permute the chunks within each term:

* `card_filter_mul_card` — for a finite group acting transitively (through an
  anti-homomorphism) on the parts, a uniformly random member carries a given part to a
  uniformly random part; this is the form `ADVXXZHoles.Shuffles.uniX` asks for.
* `typeCnt_comp`, `exists_perm_of_typeCnt` — empirical types are permutation invariant, and two
  sequences of one empirical type differ by a permutation.
* `preComp` — precomposition with a permutation of the positions.
* `blkKeep`, `Blk` — the keep predicate of `ADVXXZ.iface` read on level-1 blocks, and the
  surviving blocks.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZShuf

open ADVXXZ (Chunk SplitDist chunkLvl typeCnt ApproxConsistent)
open ADVXXZMul (grpSplit)

/-! ## Uniformity from transitivity -/

section Uniform

variable {Γ P : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [Fintype P] [DecidableEq P]

/-- **Orbit–stabiliser, in the shape `ADVXXZHoles.Shuffles.uniX` asks for.**

If the symmetry family is a finite group acting transitively on the parts, then a uniformly
random member carries a given part to a uniformly random part.  The hypothesis is stated for an
*anti*-homomorphism because the action used below is precomposition, `I ↦ I ∘ π g`, which
reverses the order.

No probability appears: the statement is the exact counting identity
`|{g : g·a = b}| · |P| = |Γ|`, which is `ADVXXZHoles.Shuffles.uniX` verbatim at `G = univ`. -/
theorem card_filter_mul_card (t : Γ → Equiv.Perm P)
    (hanti : ∀ g h : Γ, t (g * h) = t h * t g)
    (htr : ∀ a b : P, ∃ g : Γ, t g a = b) (a b : P) :
    (Finset.univ.filter fun g : Γ => t g a = b).card * Fintype.card P = Fintype.card Γ := by
  have key : ∀ c d : P, (Finset.univ.filter fun g : Γ => t g a = c).card
      ≤ (Finset.univ.filter fun g : Γ => t g a = d).card := by
    intro c d
    obtain ⟨h, hh⟩ := htr c d
    refine Finset.card_le_card_of_injOn (fun g => g * h) ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hanti, Equiv.Perm.mul_apply, hg.2, hh]⟩
    · intro g₁ _ g₂ _ hg
      exact mul_right_cancel hg
  have hsum : (Finset.univ : Finset Γ).card
      = ∑ c : P, (Finset.univ.filter fun g : Γ => t g a = c).card :=
    Finset.card_eq_sum_card_fiberwise fun g _ => Finset.mem_coe.2 (Finset.mem_univ _)
  rw [Finset.card_univ] at hsum
  rw [hsum, Finset.sum_congr rfl fun c _ => le_antisymm (key c b) (key b c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.mul_comm]

end Uniform

/-! ## Empirical types are permutation invariant -/

section TypeCnt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Reindexing a sequence by a permutation does not change its empirical type. -/
theorem typeCnt_comp (f : Fin m → ι) (σ : Equiv.Perm (Fin m)) (i : ι) :
    typeCnt (f ∘ σ) i = typeCnt f i := by
  rw [ADVXXZ.typeCnt_eq_sum, ADVXXZ.typeCnt_eq_sum]
  exact Equiv.sum_comp σ fun t => if f t = i then 1 else 0

/-- Two sequences of the same length with the same empirical type differ by a permutation.
This is `ADVXXZIface.exists_equiv_of_marg` at `ι = ι' = Fin m`; it is the transitivity half of
`Property 3.1`. -/
theorem exists_perm_of_typeCnt (f g : Fin m → ι) (h : ∀ i, typeCnt f i = typeCnt g i) :
    ∃ σ : Equiv.Perm (Fin m), ∀ p, g (σ p) = f p :=
  ADVXXZIface.exists_equiv_of_marg f g fun v => h v

end TypeCnt

/-! ## The chunk-permutation family -/

section Perm

variable {s : ℕ} {nr : Fin s → ℕ}


variable {N : ℕ}

/-- Precomposition with a permutation of the positions, as a permutation of the leg type. -/
def preComp {A C : Type*} (π : Equiv.Perm A) : Equiv.Perm (A → C) where
  toFun f := f ∘ π
  invFun f := f ∘ π.symm
  left_inv f := by funext a; simp
  right_inv f := by funext a; simp

end Perm

/-! ## The level-1 block of a leg, and the block-level keep predicate -/

section Blk

variable {q w s N : ℕ} {nr : Fin s → ℕ}

/-- **The keep predicate of `ADVXXZ.iface`, read on level-1 blocks.**

A leg is kept iff, in every group `r`, each chunk of its level-1 index sequence has level `i r`
and the sequence is `ε`-consistent with `b r`.  The predicate depends on a leg only through its
level-1 index sequence, so whole blocks are kept or dropped together. -/
def blkKeep (w : ℕ) (e : ((r : Fin s) × Fin (nr r)) ≃ Fin N) (i : Fin s → ℕ)
    (b : Fin s → SplitDist w) (ε : ℚ) (Î : Fin N → Chunk w) : Prop :=
  ∀ r, (∀ p, chunkLvl (grpSplit e Î r p) = i r) ∧ ApproxConsistent ε (b r) (grpSplit e Î r)

/-- **The level-1 blocks that survive the zero-outs**: the parts of the partition. -/
abbrev Blk (w : ℕ) (e : ((r : Fin s) × Fin (nr r)) ≃ Fin N) (i : Fin s → ℕ)
    (b : Fin s → SplitDist w) (ε : ℚ) : Type :=
  {Î : Fin N → Chunk w // blkKeep w e i b ε Î}

end Blk

section Main

variable {q w s N : ℕ} {nr : Fin s → ℕ}

end Main

end ADVXXZShuf

end OmegaBound
