import OmegaBound.ADVXXZGeneralTensorCopiesZ
import OmegaBound.ADVXXZGeneralCertInventory
import OmegaBound.ASISum

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def topZ (q w n : ℕ) : ITensor :=
  { X := Fin n → Fin w → CW90.Idx7 q
    Y := Fin n → Fin w → CW90.Idx7 q
    Z := Fin n → Fin w → CW90.Idx7 q
    tensor := tensorPower (tensorPower (cwZ q) w) n }

def ifaceZ (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ)
    (beta : Side → Fin s → SplitDist w) (ε : ℚ) : ITensor :=
  { X := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    Y := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    Z := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    tensor := fun x y z => ∏ t, ifaceTermZ q w (i t) (j t) (k t) (n t)
      (beta .X t) (beta .Y t) (beta .Z t) ε (x t) (y t) (z t) }

def supportedIfaceZ (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ)
    (beta : Side → Fin s → SplitDist w) (ε : ℚ) : ITensor :=
  { X := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    Y := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    Z := (t : Fin s) → Fin (n t) → Fin w → CW90.Idx7 q
    tensor := zoP
      (fun x => ∀ t a, (beta .X t).num (chunkOf (x t a)) ≠ 0)
      (fun y => ∀ t a, (beta .Y t).num (chunkOf (y t a)) ≠ 0)
      (fun z => ∀ t a, (beta .Z t).num (chunkOf (z t a)) ≠ 0)
      (ifaceZ q w n i j k beta ε).tensor }

def constituentInputZ (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (n : ℕ) (ε : ℚ) : ITensor :=
  supportedIfaceZ q (w + w) (fun t => p.baseN t * n) p.i p.j p.k p.beta ε

def constituentPlainInputZ (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (n : ℕ) (ε : ℚ) : ITensor :=
  ifaceZ q (w + w) (fun t => p.baseN t * n) p.i p.j p.k p.beta ε

noncomputable def constituentOutputZ (q : ℕ) {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (n : ℕ) (ε : ℚ) : ITensor :=
  ifaceZ q w (constituentOutN d.toPaper n)
    (constituentOutI (p := p)) (constituentOutJ (p := p))
    (constituentOutK (p := p)) (constituentOutBeta d.toPaper) ε

noncomputable def regionalInputZ (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (n : ℕ) (ε : ℚ) : ITensor :=
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  supportedIfaceZ q (w + w)
    (fun x => ((n : ℚ) * (p.baseN (e x).1 : ℚ) *
      (d.A (e x).1).prob (e x).2).floor.toNat)
    (fun x => p.i (e x).1) (fun x => p.j (e x).1) (fun x => p.k (e x).1)
    (fun W x => d.betaRegion W (e x).1 (e x).2) ε

noncomputable def globalOutputZ (q : ℕ) {w : ℕ} (g : GlobalSpec w)
    (n : ℕ) (ε : ℚ) : ITensor :=
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  ifaceZ q w (fun x => ((n : ℚ) * g.joint.prob (e x)).floor.toNat)
    (fun x => coord .X (e x).2) (fun x => coord .Y (e x).2)
    (fun x => coord .Z (e x).2) (fun W x => g.beta W (e x).1 (e x).2) ε

noncomputable def globalSupportedOutputZ (q : ℕ) {w : ℕ} (g : GlobalSpec w)
    (n : ℕ) (ε : ℚ) : ITensor :=
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  supportedIfaceZ q w (fun x => ((n : ℚ) * g.joint.prob (e x)).floor.toNat)
    (fun x => coord .X (e x).2) (fun x => coord .Y (e x).2)
    (fun x => coord .Z (e x).2) (fun W x => g.beta W (e x).1 (e x).2) ε

def matMulZ (a b c : ℕ) : ITensor :=
  { X := Fin a × Fin b
    Y := Fin b × Fin c
    Z := Fin c × Fin a
    tensor := fun ⟨i, j⟩ ⟨j', k⟩ ⟨k', i'⟩ =>
      if j = j' ∧ k = k' ∧ i = i' then 1 else 0 }

def mmDSumF (F : Type u) [Field F] (a b c : ℕ → ℕ) : (s : ℕ) →
    Tensor3 F (mmIdxSum a b s) (mmIdxSum b c s) (mmIdxSum c a s)
  | 0 => fun x _ _ => x.elim
  | s + 1 => Tensor3.matMul (R := F) (a s) (b s) (c s) ⊕ₜ mmDSumF F a b c s

end OmegaBound.ADVXXZGeneral
end
