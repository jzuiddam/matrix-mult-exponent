import OmegaBound.ADVXXZBlkCount
import OmegaBound.ADVXXZHashRung
import OmegaBound.ADVXXZSplitIface

/-!
# Type-counting identities

A sum of a function of the letters of a sequence is the type of the sequence paired against that
function, and the type of a relabelled sequence is determined by the type of the sequence.

## Main results

* `ADVXXZEnt.sum_comp_eq_sum_typeCnt_mul` — `∑_t F(f t) = ∑_i typeCnt f i · F i`.
* `ADVXXZEnt.typeCnt_comp` — the type of `g ∘ f` from the type of `f`.
-/

open Finset

namespace OmegaBound

namespace ADVXXZEnt

open ADVXXZ (typeCnt typeCnt_eq_sum card_filter_typeCnt)

/-! ## Everything is a function of the type -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ}

/-- **The type-weighted sum.**  A sum of a function of the letters of a sequence is the type of
the sequence paired against that function.  Every "depends only on the type" claim below is
this identity at some `F`. -/
theorem sum_comp_eq_sum_typeCnt_mul (f : Fin N → ι) (F : ι → ℕ) :
    ∑ t, F (f t) = ∑ i, typeCnt f i * F i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := (Finset.univ : Finset ι))
    (fun t _ => Finset.mem_univ (f t)) (fun t => F (f t))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcongr : ∀ t ∈ (Finset.univ : Finset (Fin N)).filter (fun t => f t = i),
      F (f t) = F i := fun t ht => by rw [(Finset.mem_filter.mp ht).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, typeCnt, smul_eq_mul]

omit [Fintype κ] in
/-- The type of a **relabelled** sequence is determined by the type of the sequence. -/
theorem typeCnt_comp (g : ι → κ) (f : Fin N → ι) (j : κ) :
    typeCnt (fun t => g (f t)) j = ∑ i, typeCnt f i * (if g i = j then 1 else 0) := by
  rw [typeCnt_eq_sum]
  exact sum_comp_eq_sum_typeCnt_mul f (fun i => if g i = j then 1 else 0)

variable {w : ℕ}

end ADVXXZEnt

end OmegaBound
