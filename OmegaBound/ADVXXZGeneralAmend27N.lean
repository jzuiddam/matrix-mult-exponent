import OmegaBound.ADVXXZGeneralScaleAuxV22
import OmegaBound.ADVXXZGeneralRatesFitV22
import OmegaBound.ADVXXZGeneralInventory
import OmegaBound.ADVXXZLevel2Closure

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

/-- Paper clause: `P/constituent.tex:28–36; P/numerical.tex:19–22`. -/
def BoundaryInventoryAdmissible (I : Inventory) (b : ℕ) : Prop :=
  ∀ a ∈ I,
    0 ≤ a.1 ∧ (∀ W σ, 0 ≤ a.2.2.2 W σ) ∧
    (∀ W, (∑ σ, a.2.2.2 W σ) = 1) ∧
    (∀ W σ, a.2.2.2 W σ ≠ 0 → chunkLvl σ = coord W a.2.2.1) ∧
    (∃ W, coord W a.2.2.1 = 0) ∧
    (∀ Z X Y : Side, X ≠ Y → X ≠ Z → Y ≠ Z → coord Z a.2.2.1 = 0 →
      ∀ σ, a.2.2.2 X σ = a.2.2.2 Y (reflect σ)) ∧
    (∃ k : ℕ, (b : ℚ) * a.1 = k) ∧
    ∀ W σ, ∃ k : ℕ, (b : ℚ) * a.1 * a.2.2.2 W σ = k
end
end OmegaBound.ADVXXZGeneral
end

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clause: `P/constituent.tex:28–36; P/numerical.tex:19–22`. -/
def boundaryRate (q : ℕ) (I : Inventory) (W : Side) : ℝ :=
  (I.map fun a =>
    let u := a.2.2.1
    let beta := a.2.2.2
    let active := match W with
      | .X => coord .Y u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Z u
      | .Y => coord .Z u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Y u
      | .Z => coord .X u = 0 ∧ 0 < coord .Y u ∧ 0 < coord .Z u
    let V : Side := match W with | .X => .X | .Y => .X | .Z => .Y
    if active then (a.1 : ℝ) * (entropyNats (fun σ => (beta V σ : ℝ)) +
      Real.log (q : ℝ) * ∑ σ : Chunk a.2.1, (beta V σ : ℝ) *
        ((Finset.univ.filter (fun i : Fin a.2.1 => (σ i).val = 1)).card : ℝ)) else 0).sum
end
end OmegaBound.ADVXXZGeneral
end

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

-- The filter preserves individual occurrences, including unit occurrences.
/-- Paper clause: `P/numerical.tex:17–22`. -/
def boundaryOccurrences27 (I : Inventory) : Inventory :=
  I.filter fun a => coord .X a.2.2.1 = 0 ∨ coord .Y a.2.2.1 = 0 ∨ coord .Z a.2.2.1 = 0

/-- Paper clause: `P/numerical.tex:17–22`. -/
def accumulatedBoundary27 (C : Certificate) : Inventory :=
  boundaryOccurrences27 (G C) ++
    (((List.finRange (C.top + 1)).reverse).flatMap fun l =>
      if h : 2 ≤ l.val ∧ l.val ≤ C.top then boundaryOccurrences27 (QAt C ⟨l.val, h⟩) else [])
end
end OmegaBound.ADVXXZGeneral
end
