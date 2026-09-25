import OmegaBound.ADVXXZHashPat
import OmegaBound.ADVXXZSplitIface
import OmegaBound.CW90Hash
import Mathlib.Data.List.GetD

/-!
# Two colourings of one joint type differ by a bijection

`exists_equiv_of_marg`: two sequences `b : ι → κ` and `b' : ι' → κ` with the same marginals
(`CW90Eight.marg`) differ by a bijection `ι ≃ ι'` of the positions.  The two position types may
differ; their cardinalities then agree automatically.
-/

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZIface

open CW90Eight (marg)

/-! ## Two colourings of one joint type differ by a bijection -/

/-- **Two sequences with the same marginals differ by a bijection of the positions.**  The two
position types are allowed to differ, and their cardinalities then agree automatically. -/
theorem exists_equiv_of_marg {ι ι' κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype κ] [DecidableEq κ] (b : ι → κ) (b' : ι' → κ)
    (h : ∀ v, marg b v = marg b' v) : ∃ e : ι ≃ ι', ∀ p, b' (e p) = b p := by
  classical
  obtain ⟨e⟩ : Nonempty (∀ v : κ, {p : ι // b p = v} ≃ {p : ι' // b' p = v}) :=
    ⟨fun v => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h v)⟩
  refine ⟨(Equiv.sigmaFiberEquiv b).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b')), fun p => ?_⟩
  exact (e (b p) ⟨p, rfl⟩).2

variable {q w : ℕ}

variable {s : ℕ}

end ADVXXZIface

end OmegaBound
