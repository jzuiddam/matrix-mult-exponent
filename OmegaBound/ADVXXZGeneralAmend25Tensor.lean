import OmegaBound.ADVXXZGeneralTensorAux

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/--
The physical labelled dependent sum.
Paper clauses: `P/constituent.tex:340-345` and `P/global.tex:322-356`.
-/
noncomputable def dependentSumZ {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → ITensor) : ITensor := by
  classical
  exact
    { X := (i : ι) × (T i).X
      Y := (i : ι) × (T i).Y
      Z := (i : ι) × (T i).Z
      tensor := fun x y z =>
        if hxy : x.1 = y.1 then
          if hxz : x.1 = z.1 then
            (T x.1).tensor x.2 (hxy.symm ▸ y.2) (hxz.symm ▸ z.2)
          else 0
        else 0 }

/--
The six-region physical product.
Paper clauses: `P/constituent.tex:340-342` and `P/global.tex:322-356`.
-/
noncomputable def regionProductZ (T : Fin 6 → ITensor) : ITensor :=
  { X := (r : Fin 6) → (T r).X
    Y := (r : Fin 6) → (T r).Y
    Z := (r : Fin 6) → (T r).Z
    tensor := fun x y z => ∏ r, (T r).tensor (x r) (y r) (z r) }

/--
The empty labelled-family tensor.
Paper clauses: the empty invalid-hash branches of `P/constituent.tex:195-205` and
`P/global.tex:158-184`.
-/
def emptyFamilyZ : ITensor :=
  { X := Empty
    Y := Empty
    Z := Empty
    tensor := fun x _ _ => nomatch x }

/--
The zero-position regional tensor unit.
Paper clauses: `P/constituent.tex:340-342` and `P/global.tex:322-356`.
-/
def unitFamilyZ : ITensor :=
  { X := Unit
    Y := Unit
    Z := Unit
    tensor := fun _ _ _ => 1 }

end OmegaBound.ADVXXZGeneral
end

