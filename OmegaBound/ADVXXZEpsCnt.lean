import OmegaBound.ADVXXZEntCon
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-!
# Two type-counting facts

* `ADVXXZEps.typeCnt_comp_fiber` — the type of a relabelled sequence, in fibre form.
* `ADVXXZEps.exists_typeCnt_eq` — every count vector summing to `n` is the type of a sequence.

SOURCE: global.tex:99-112 (rmk:assumptions_on_complete_split_dist)
SOURCE: constituent.tex:14-24 (rmk:constituent:assumptions_on_complete_split_dist)
-/

set_option linter.unusedSectionVars false

open Finset

namespace OmegaBound

namespace ADVXXZEps

open ADVXXZ (typeCnt typeCnt_eq_sum sum_typeCnt card_filter_typeCnt empDist consistent_empDist approxConsistent_zero_iff)

/-! ## Two type-counting facts -/

section TypeFacts

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}

omit [Fintype κ] in
/-- **The type of a relabelled sequence, in fibre form.**  This is the identity inside
`ADVXXZ.Consistent.map`, extracted so that a consistency demand on a *pushforward* can be
stated as a demand on the type of the underlying sequence. -/
theorem typeCnt_comp_fiber (g : ι → κ) (f : Fin n → ι) (j : κ) :
    typeCnt (fun t => g (f t)) j
      = ∑ i ∈ Finset.univ.filter fun i => g i = j, typeCnt f i := by
  simp only [typeCnt_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

/-- **Every count vector summing to `n` is the type of a sequence.**  The class of sequences of
that type is counted exactly by the multinomial coefficient
(`ADVXXZ.card_filter_typeCnt`), which is positive, so the class is nonempty. -/
theorem exists_typeCnt_eq [Nonempty ι] (k : ι → ℕ) (hk : ∑ i, k i = n) :
    ∃ f : Fin n → ι, ∀ i, typeCnt f i = k i := by
  classical
  have hpos : 0 < (Finset.univ.filter fun f : Fin n → ι => ∀ i, typeCnt f i = k i).card := by
    rw [card_filter_typeCnt k hk]
    exact Nat.multinomial_pos _ _
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
  exact ⟨f, (Finset.mem_filter.mp hf).2⟩

end TypeFacts

variable {w N i j k : ℕ}

end ADVXXZEps

end OmegaBound
