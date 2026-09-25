import OmegaBound.ADVXXZBlkCount
import OmegaBound.ADVXXZHashPat
import OmegaBound.ADVXXZSplitIface
import OmegaBound.CW90Hash
import OmegaBound.ADVXXZIfaceCol

/-!
# Grouping the positions of a colouring by pattern

`grpSplit` cuts a leg `Fin N → X` into groups along a grouping equivalence
`((r : Fin s) × Fin (nr r)) ≃ Fin N`: the `r`-th group is `p ↦ φ (e ⟨r, p⟩)`.  At
`nr r = marg γ (pat r)` the groups are the pattern classes of a colouring `γ`.
-/

set_option linter.unusedSectionVars false

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZMul

open ADVXXZ (restricts_of_sub)

/-! ## Cutting a leg into its pattern classes -/

section Split

variable {N s : ℕ} {nr : Fin s → ℕ}

/-- **The `r`-th group of a leg**, along a grouping equivalence.  The group lengths
are an arbitrary `nr`; at `nr r = marg γ (pat r)` the groups are the pattern classes of `γ`. -/
def grpSplit {X : Type*} (e : ((r : Fin s) × Fin (nr r)) ≃ Fin N) (φ : Fin N → X) :
    (r : Fin s) → Fin (nr r) → X := fun r p => φ (e ⟨r, p⟩)

end Split

section Keep

variable {q w N s : ℕ} {nr : Fin s → ℕ}

end Keep

section Value

variable {t : ℝ} {q w N s : ℕ} {nr : Fin s → ℕ}

end Value

section Block

variable {q w N s : ℕ} {nr : Fin s → ℕ}

end Block

section Group

variable {L : ℕ}

end Group

section JVal

variable {L : ℕ}

end JVal

end ADVXXZMul

end OmegaBound
