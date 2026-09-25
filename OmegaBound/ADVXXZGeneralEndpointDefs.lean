import OmegaBound.ADVXXZGeneralRank

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def IsRectExponent (F : Type u) [Field F] (κ τ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ r : ℕ,
    RankLE (Tensor3.matMul (R := F) n (Nat.ceil ((n:ℝ)^κ)) n) r ∧
      (r:ℝ) ≤ C*(n:ℝ)^τ

noncomputable def omegaRect (F : Type u) [Field F] (κ : ℝ) : ℝ :=
  sInf {τ | IsRectExponent F κ τ}

end OmegaBound.ADVXXZGeneral
end
