import OmegaBound.ADVXXZGeneralCertInventory

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

structure RawPopulation where
  n : ℕ
  grade : ℕ
  Label : Type
  [labelFinite : Fintype Label]
  target : Finset Label
  coarse : Label → Side → Fin n → Fin (grade+1)
  Part : Side → Type
  [partFinite : ∀ W, Fintype (Part W)]
  fine : (W : Side) → Part W → Fin n → ℕ
  incidence : (W : Side) → Label → Part W → Prop

attribute [instance] RawPopulation.labelFinite RawPopulation.partFinite

abbrev HashOutcome (P : RawPopulation) (M : ℕ) := Fin (P.n+2) → ZMod M

noncomputable def natural_demand (floor Ntriple NX NY NZ Nalpha H : ℕ)
    (pY pZ : ℝ) : ℕ :=
  max floor (max (if NX=0 then 0 else Nat.ceil (8*(Ntriple:ℝ)/NX))
    (max (if NY=0 then 0 else Nat.ceil ((H:ℝ)*Nalpha*pY/NY))
         (if NZ=0 then 0 else Nat.ceil ((H:ℝ)*Nalpha*pZ/NZ))))

noncomputable def cond {Ω : Type*} [DecidableEq Ω]
    (E B : Finset Ω) : ℝ := ((E ∩ B).card : ℝ) / E.card

end OmegaBound.ADVXXZGeneral
end
