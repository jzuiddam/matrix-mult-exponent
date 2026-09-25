import OmegaBound.ADVXXZGeneralCertInventory

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def Sublinear (L : ℕ → ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m, M ≤ m → |f m| ≤ δ * (L m : ℝ)

def Loss (L : ℕ → ℕ) (ell : ℚ → ℕ → ℝ) : Prop :=
  (∀ ε m, 0 ≤ ell ε m) ∧ ∀ ε, 0 < ε → Sublinear L (ell ε)

def CopyBound (L : ℕ → ℕ) (rate : ℝ) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (V : ℚ → ℕ → ℕ) : Prop :=
  ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
    Real.exp ((rate - delta ε) * (L m : ℝ) - ell ε m) ≤ (V ε m : ℝ)

noncomputable def cRate {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) : ℝ :=
  Real.log 2 * (∑ r, constituentRegionRate d.toPaper r) / constituentBaseTotal p

noncomputable def gRate {w : ℕ} (g : GlobalSpec w) : ℝ :=
  Real.log 2 * ∑ r, g.A.probR r * globalRegionRate g.toPaper r

def LowerRate (O : ℕ → ℕ) (x : ℚ → ℕ → ℕ) (r : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℚ, 0 < ε₀ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ ε₀ → ∃ M, ∀ m, M ≤ m →
      1 ≤ x ε m ∧ (r-δ)*(O m:ℝ) ≤ Real.log (x ε m:ℝ)

noncomputable def demandCompatRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (which : Fin 2) : ℝ :=
  let X := d.perm r .X
  let Y := d.perm r .Y
  let Z := d.perm r .Z
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
    (if which = 0 then
      constituentEta d.toPaper t r X Y Z - splitEntropy (d.betaRegion Y t r) +
        entropy (constituentMarginal d.toPaper t r Y)
     else
      constituentLambda d.toPaper t r X Y Z - splitEntropy (d.betaRegion Z t r) +
        entropy (constituentMarginal d.toPaper t r Z))

noncomputable def entropyNats {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a, p a * Real.log (p a)

end OmegaBound.ADVXXZGeneral
end
