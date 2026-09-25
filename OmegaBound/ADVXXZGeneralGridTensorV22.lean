import OmegaBound.ADVXXZGeneralGridFull
import OmegaBound.ADVXXZGeneralTensorAux

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- One physical leg has exactly the histogram recorded by a full grid. -/
noncomputable def GridLegMatches {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (W : Side) (ξ : FullGrid g n ε) (x : (globalOutputZ q g n ε).X) : Prop :=
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  ∀ t σ, ξ.val.count W (e t).1 (e t).2 σ = typeCnt (chunkSeq (x t)) σ

noncomputable instance instDecidableGridLegMatches {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (W : Side) (ξ : FullGrid g n ε) : DecidablePred (GridLegMatches (q := q) W ξ) :=
  Classical.decPred _

/-- The exact empirical-histogram zero-out on the common physical global-output legs.
The underlying output is plain, so full grids can retain words outside beta support. -/
noncomputable def fullGridTensor (q : ℕ) {w : ℕ} (g : GlobalSpec w) (n : ℕ) {ε : ℚ}
    (ξ : FullGrid g n ε) : ITensor :=
  let T := globalOutputZ q g n ε
  { X := T.X
    Y := T.Y
    Z := T.Z
    tensor := zoP (GridLegMatches (q := q) .X ξ) (GridLegMatches (q := q) .Y ξ)
      (GridLegMatches (q := q) .Z ξ) T.tensor }

end OmegaBound.ADVXXZGeneral
end
