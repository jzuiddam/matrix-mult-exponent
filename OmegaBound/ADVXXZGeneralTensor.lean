import OmegaBound.ADVXXZGeneralCertCore
import OmegaBound.ADVXXZSplitIface

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

structure ITensor where
  X : Type
  Y : Type
  Z : Type
  [fx : Fintype X]
  [fy : Fintype Y]
  [fz : Fintype Z]
  tensor : Tensor3 ℤ X Y Z

attribute [instance] ITensor.fx ITensor.fy ITensor.fz

def mapTensor {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z : Type*} (f : R →+* S) (T : Tensor3 R X Y Z) : Tensor3 S X Y Z :=
  fun x y z => f (T x y z)

def ITensor.over (T : ITensor) (F : Type*) [Field F] : Tensor3 F T.X T.Y T.Z :=
  mapTensor (Int.castRingHom F) T.tensor

def tensorPower {R : Type*} [CommSemiring R] {X Y Z : Type*}
    (T : Tensor3 R X Y Z) (n : ℕ) :
    Tensor3 R (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

def cwZ (q : ℕ) : Tensor3 ℤ (CW90.Idx7 q) (CW90.Idx7 q) (CW90.Idx7 q) := fun a b c =>
  match a, b, c with
  | .inl none, .inl (some i), .inl (some j) => if i = j then 1 else 0
  | .inl (some i), .inl none, .inl (some j) => if i = j then 1 else 0
  | .inl (some i), .inl (some j), .inl none => if i = j then 1 else 0
  | .inl none, .inl none, .inr _ => 1
  | .inl none, .inr _, .inl none => 1
  | .inr _, .inl none, .inl none => 1
  | _, _, _ => 0

def conZ (q w i j k : ℕ) :
    Tensor3 ℤ (Fin w → CW90.Idx7 q) (Fin w → CW90.Idx7 q) (Fin w → CW90.Idx7 q) :=
  zoP (fun a => levOf a = i) (fun b => levOf b = j) (fun c => levOf c = k)
    (tensorPower (cwZ q) w)

def ifaceTermZ (q w i j k n : ℕ) (bX bY bZ : SplitDist w) (ε : ℚ) :
    Tensor3 ℤ (Fin n → Fin w → CW90.Idx7 q)
      (Fin n → Fin w → CW90.Idx7 q) (Fin n → Fin w → CW90.Idx7 q) :=
  fun x y z => if n = 0 then 1 else
    if ApproxConsistent ε bX (chunkSeq x) ∧
       ApproxConsistent ε bY (chunkSeq y) ∧
       ApproxConsistent ε bZ (chunkSeq z)
    then tensorPower (conZ q w i j k) n x y z else 0

variable {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']

def PolyDegeneratesAt (R : Type*) [CommRing R] (N : ℕ)
    (T : Tensor3 R X Y Z) (U : Tensor3 R X' Y' Z') : Prop :=
  ∃ (A : X' → X → Polynomial R) (B : Y' → Y → Polynomial R)
    (C : Z' → Z → Polynomial R),
    (∀ x y z k, k < N →
      (∑ i, ∑ j, ∑ l, A x i*B y j*C z l*Polynomial.C (T i j l)).coeff k = 0) ∧
    (∀ x y z,
      (∑ i, ∑ j, ∑ l, A x i*B y j*C z l*Polynomial.C (T i j l)).coeff N = U x y z)

end OmegaBound.ADVXXZGeneral
end
