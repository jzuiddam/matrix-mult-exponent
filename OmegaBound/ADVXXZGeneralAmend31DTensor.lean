import OmegaBound.ADVXXZGeneralTensorAux

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clause: `P/prelim.tex:161`. -/
def boundarySymbol31 {q : ℕ} : CW90.Idx7 q → CW90.Idx7 q
  | .inl none => .inr ()
  | .inl (some i) => .inl (some i)
  | .inr _ => .inl none

/-- Paper clause: `P/constituent.tex:17–21`. -/
def boundaryWordPartner31 {q w k : ℕ}
    (x : Fin k → Fin w → CW90.Idx7 q) : Fin k → Fin w → CW90.Idx7 q :=
  fun t j => boundarySymbol31 (x t j)

/-- Paper clauses:
`P/prelim.tex:122` and `P/constituent.tex:32–36`. -/
def boundaryActive31 (a : ℚ × AtomKey) : Side → Prop
  | .X => coord .Y a.2.2.1 = 0 ∧ 0 < coord .X a.2.2.1 ∧ 0 < coord .Z a.2.2.1
  | .Y => coord .Z a.2.2.1 = 0 ∧ 0 < coord .X a.2.2.1 ∧ 0 < coord .Y a.2.2.1
  | .Z => coord .X a.2.2.1 = 0 ∧ 0 < coord .Y a.2.2.1 ∧ 0 < coord .Z a.2.2.1

/-- Paper clause: `P/constituent.tex:35–36`. -/
def boundaryReadingSide31 : Side → Side | .X => .X | .Y => .X | .Z => .Y

/-- Paper clauses:
`P/prelim.tex:181–200,267–278` and `P/constituent.tex:35`. -/
def boundaryWords31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ) (W : Side) :
    Finset (Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q) :=
  Finset.univ.filter fun x =>
    (∀ t, levOf (x t) = coord W a.2.2.1) ∧
    ((a.1 * (n : ℚ)).floor.toNat = 0 ∨
      ∀ σ, emp (chunkSeq x) σ = a.2.2.2 W σ)

/-- Paper clauses:
`P/prelim.tex:267–268` and `P/constituent.tex:11,35`. -/
def boundaryTypeCounts31 (a : ℚ × AtomKey) (n : ℕ) (W : Side)
    (σ : Chunk a.2.1) : ℕ :=
  (((a.1 * (n : ℚ)).floor.toNat : ℚ) * a.2.2.2 W σ).floor.toNat

/-- Paper clause: `P/constituent.tex:39`. -/
def boundaryDimension31 (q : ℕ) (I : Inventory) (n : ℕ) (W : Side) : ℕ :=
  (I.map fun a => if boundaryActive31 a W then
    (boundaryWords31 q a n (boundaryReadingSide31 W)).card else 1).prod

/-- Paper clauses:
`P/prelim.tex:119–122` and `P/constituent.tex:28–39`. -/
def boundaryMatrixZ (q : ℕ) (I : Inventory) (n : ℕ) : ITensor :=
  matMulZ (boundaryDimension31 q I n .X)
    (boundaryDimension31 q I n .Y) (boundaryDimension31 q I n .Z)
end
end OmegaBound.ADVXXZGeneral
end
