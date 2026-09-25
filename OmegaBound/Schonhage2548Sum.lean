import OmegaBound.ASISum
import OmegaBound.ASI

/-!
# Transport of a degeneration along an equality

`Degenerates.of_eq`: a degeneration of `T` to `S` is also one to any `S'` with `S' = S`.
-/

open Tensor3 Finset

namespace OmegaBound


/-- Transport a degeneration along an equality of the target. -/
theorem Degenerates.of_eq {F : Type*} [Field F] {α β γ α' β' γ' : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
    {T : Tensor3 F α β γ} {S S' : Tensor3 F α' β' γ'} (h : Degenerates F T S) (he : S' = S) :
    Degenerates F T S' := by rw [he]; exact h


end OmegaBound
