import OmegaBound.ADVXXZGeneralRatesFit
import OmegaBound.ADVXXZGeneralCertComplete

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def StepIntegralAt {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) : Prop :=
  0 < b ∧ ∀ t r, integral ((b : ℚ) * p.baseN t * (d.A t).prob r) ∧
    ∀ u, integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u) ∧
      (∀ W σ τ, integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u *
        (d.betaChild W t r u).prob σ *
          (d.betaChild W t r (complement p t u)).prob τ)) ∧
      ∀ W σ, integral ((d.outBase ⟨t,r,u⟩ : ℚ) * (d.betaChild W t r u).prob σ)

def AtomicIntegralAt (C : Certificate) : Prop :=
  GlobalIntegral C.global (C.D ^ 4) ∧
    ∀ l d, C.stage l = some d → StepIntegralAt d.input d.data (C.D ^ 2)

noncomputable def QAt (C : Certificate) (l : Stage C.top) : Inventory :=
  match C.stage l with
  | none => []
  | some d => childInventory d.data

def scaleParent {w s : ℕ} (p : ConstituentInput w s)
    (b : ℕ) (hb : 0 < b) : ConstituentInput w s :=
  { p with
    baseN := fun t => b * p.baseN t
    baseN_pos := fun t => Nat.mul_pos hb (p.baseN_pos t) }

def ConstituentSpec.atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) :
    ConstituentSpec (scaleParent p b hb) :=
  { A := d.A, alpha := d.alpha, betaRegion := d.betaRegion,
    betaChild := d.betaChild, perm := d.perm, outBase := d.outBase }

noncomputable def derivedMatrixRateAt (C : Certificate) (W : Side) : ℝ := by
  classical
  let atomRate := fun a : ℚ × AtomKey =>
    let u := a.2.2.1
    let beta := a.2.2.2
    let active := match W with
      | .X => coord .Y u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Z u
      | .Y => coord .Z u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Y u
      | .Z => coord .X u = 0 ∧ 0 < coord .Y u ∧ 0 < coord .Z u
    let V : Side := match W with | .X => .X | .Y => .X | .Z => .Y
    if active then
      (a.1 : ℝ) * (entropyNats (fun σ => (beta V σ : ℝ)) +
        Real.log (C.q : ℝ) * ∑ σ : Chunk a.2.1,
          (beta V σ : ℝ) * ((Finset.univ.filter
            (fun i : Fin a.2.1 => (σ i).val = 1)).card : ℝ))
    else 0
  let inventoryRate := fun I : Inventory => (I.map atomRate).sum
  exact (inventoryRate (G C) + ∑ l : Stage C.top, inventoryRate (QAt C l)) / (C.D : ℝ)^4

end OmegaBound.ADVXXZGeneral
end
