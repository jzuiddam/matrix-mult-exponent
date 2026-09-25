import OmegaBound.ADVXXZGeneralCertCore

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

abbrev AtomKey := (w : ℕ) × Shape w × (Side → Chunk w → ℚ)
abbrev Inventory := List (ℚ × AtomKey)

noncomputable def inventoryMass (I : Inventory) (k : AtomKey) : ℚ :=
  (I.map (fun a => if a.2 = k then a.1 else 0)).sum

def InventoryEq (I J : Inventory) : Prop :=
  (I.filter (fun a => decide (a.1 ≠ 0))).Perm
    (J.filter (fun a => decide (a.1 ≠ 0)))

def interior (I : Inventory) : Inventory := I.filter fun a =>
  decide (0 < a.1 ∧ 0 < coord .X a.2.2.1 ∧ 0 < coord .Y a.2.2.1 ∧
    0 < coord .Z a.2.2.1)

structure Step (w : ℕ) where
  s : ℕ
  input : ConstituentInput w s
  data : ConstituentSpec input

abbrev Stage (top : ℕ) := {l : ℕ // 2 ≤ l ∧ l ≤ top}

structure ModulusPolicy where
  floor : ℕ
  collisionPower : ℕ
  floor_ge : 3 ≤ floor
  collisionPower_ge : 3 ≤ collisionPower

structure Certificate where
  q : ℕ
  width : ℕ
  top : ℕ
  kappa : ℝ
  global : GlobalSpec width
  stage : (l : Stage top) → Option (Step (wid (l.val - 1)))
  D : ℕ
  modulus : ModulusPolicy

def integral (x : ℚ) : Prop := ∃ n : ℕ, x = (n : ℚ)

def parentShape {w s : ℕ} (p : ConstituentInput w s) (t : Fin s) : Shape (w + w) :=
  ⟨(⟨p.i t, by have := p.shape_sum t; omega⟩, ⟨p.j t, by have := p.shape_sum t; omega⟩,
    ⟨p.k t, by have := p.shape_sum t; omega⟩), by simpa using p.shape_sum t⟩

noncomputable section

def globalInventory {w : ℕ} (g : GlobalSpec w) : Inventory :=
  (List.finRange (Fintype.card (Fin 6 × Shape w))).map fun i =>
    let ru := (Fintype.equivFin (Fin 6 × Shape w)).symm i
    (g.joint.prob ru, ⟨w, ru.2, fun W σ => (g.beta W ru.1 ru.2).prob σ⟩)

def parentInventory {w s : ℕ} (p : ConstituentInput w s) : Inventory :=
  (List.finRange s).map fun t =>
    ((p.baseN t : ℚ), ⟨w + w, parentShape p t, fun W σ => (p.beta W t).prob σ⟩)

def childInventory {w s : ℕ} {p : ConstituentInput w s} (d : ConstituentSpec p) : Inventory :=
  (List.finRange (Fintype.card (ConstituentTerm p))).map fun i =>
    let x := (Fintype.equivFin (ConstituentTerm p)).symm i
    ((d.outBase x : ℚ), ⟨w, x.2.2.1, fun W σ => (d.betaChild W x.1 x.2.1 x.2.2).prob σ⟩)

def scaleInventory (a : ℚ) (I : Inventory) : Inventory := I.map fun x => (a * x.1, x.2)

def G (C : Certificate) : Inventory :=
  scaleInventory ((C.D : ℚ) ^ 4) (globalInventory C.global)

def P (C : Certificate) (l : Stage C.top) : Inventory :=
  match C.stage l with
  | none => []
  | some d => scaleInventory ((C.D : ℚ) ^ 2) (parentInventory d.input)

def Q (C : Certificate) (l : Stage C.top) : Inventory :=
  match C.stage l with
  | none => []
  | some d => scaleInventory ((C.D : ℚ) ^ 2) (childInventory d.data)

def GlobalIntegral {w : ℕ} (g : GlobalSpec w) (b : ℕ) : Prop :=
  0 < b ∧ ∀ r, integral ((b : ℚ) * g.A.prob r) ∧
    ∀ u, integral ((b : ℚ) * g.joint.prob (r, u)) ∧
      ∀ W σ, integral ((b : ℚ) * g.joint.prob (r, u) * (g.beta W r u).prob σ)

def StepIntegral {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) : Prop :=
  0 < b ∧ ∀ t r, integral ((b : ℚ) * p.baseN t * (d.A t).prob r) ∧
    ∀ u, integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u) ∧
      (∀ W σ τ, integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u *
        (d.betaChild W t r u).prob σ * (d.betaChild W t r (complement p t u)).prob τ)) ∧
      ∀ W σ, integral ((b : ℚ) * d.outBase ⟨t, r, u⟩ * (d.betaChild W t r u).prob σ)

def AtomicIntegral (C : Certificate) : Prop :=
  GlobalIntegral C.global (C.D ^ 4) ∧
    ∀ l d, C.stage l = some d → StepIntegral d.input d.data (C.D ^ 2)

noncomputable def GlobalSpec.toPaper {w : ℕ} (g : GlobalSpec w) : GlobalData w :=
  let g₀ : GlobalData w :=
    { A := fun r => g.A.probR r
      alpha := fun r u => (g.alpha r).probR u
      beta := g.beta
      E := fun _ => 0
      perm := g.perm
      joint := g.joint }
  { A := fun r => g.A.probR r
    alpha := fun r u => (g.alpha r).probR u
    beta := g.beta
    E := fun r => globalRegionRate g₀ r
    perm := g.perm
    joint := g.joint }

noncomputable def ConstituentSpec.toPaper {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) : ConstituentData p :=
  let d₀ : ConstituentData p :=
    { A := fun t r => (d.A t).probR r
      betaRegion := d.betaRegion
      alpha := fun t r u => (d.alpha t r).probR u
      betaChild := d.betaChild
      E := fun _ => 0
      perm := d.perm
      outBase := d.outBase }
  { A := fun t r => (d.A t).probR r
    betaRegion := d.betaRegion
    alpha := fun t r u => (d.alpha t r).probR u
    betaChild := d.betaChild
    E := fun r => constituentRegionRate d₀ r
    perm := d.perm
    outBase := d.outBase }

end
end OmegaBound.ADVXXZGeneral
end
