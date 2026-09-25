import OmegaBound.ASISum
import OmegaBound.CW90Seven
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Marginals of sequences, and the sequences with prescribed marginals

`marg b v` counts the positions at which `b : ι → κ` takes the value `v`; `marg_comp` shows the
marginals are invariant under a permutation of the positions.  `MSeq A` is the finset of
sequences with marginals `A` (`mem_MSeq`).  These are the level-sequence objects of the
Coppersmith–Winograd 1990 §8 counting.
-/

open Finset

namespace OmegaBound

namespace CW90Eight

/-! ## Marginals of a sequence, and the transitivity of the position group -/

section Marg

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The number of positions at which `b` takes the value `v`. -/
def marg (b : ι → κ) (v : κ) : ℕ := (Finset.univ.filter (fun p => b p = v)).card

omit [DecidableEq ι] [Fintype κ] in
/-- Precomposing with a permutation of the positions does not change the marginals. -/
theorem marg_comp (b : ι → κ) (π : Equiv.Perm ι) (v : κ) :
    marg (fun p => b (π p)) v = marg b v := by
  unfold marg
  refine Finset.card_bij' (fun p _ => π p) (fun p _ => π.symm p) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  · intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (Finset.mem_filter.mp hp).2
  · intro p _
    exact π.symm_apply_apply p
  · intro p _
    exact π.apply_symm_apply p

/-! ## The number of sequences with prescribed marginals -/

/-- The sequences with prescribed marginals. -/
def MSeq (A : κ → ℕ) : Finset (ι → κ) := Finset.univ.filter (fun b => ∀ v, marg b v = A v)

theorem mem_MSeq {A : κ → ℕ} {b : ι → κ} :
    b ∈ (MSeq A : Finset (ι → κ)) ↔ ∀ v, marg b v = A v := by
  simp [MSeq]

end Marg

variable {N : ℕ} {A : Fin 5 → ℕ}

end CW90Eight

end OmegaBound
