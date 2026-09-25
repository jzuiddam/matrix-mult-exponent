import OmegaBound.ADVXXZGeneralCertInventory
import OmegaBound.ADVXXZGeneralTensor
import PLATFORM.Statements.«V17_D_Inventory.1»

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable def inventoryTensorZ (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ) : ITensor :=
  P2M.V17_D_Inventory.inventoryTensorZ q I n ε

noncomputable def supportedInventoryTensorZ
    (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ) : ITensor :=
  match I with
  | [] =>
      { X := PUnit
        Y := PUnit
        Z := PUnit
        tensor := fun _ _ _ => 1 }
  | a :: tail =>
      let k := (a.1 * (n : ℚ)).floor.toNat
      let T := supportedInventoryTensorZ q tail n ε
      { X := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.X
        Y := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.Y
        Z := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.Z
        tensor := fun x y z =>
          (if k = 0 then 1 else
            if (∀ σ, |emp (chunkSeq x.1) σ - a.2.2.2 .X σ| ≤ ε) ∧
               (∀ σ, |emp (chunkSeq y.1) σ - a.2.2.2 .Y σ| ≤ ε) ∧
               (∀ σ, |emp (chunkSeq z.1) σ - a.2.2.2 .Z σ| ≤ ε) ∧
               (∀ t, a.2.2.2 .X (chunkOf (x.1 t)) ≠ 0) ∧
               (∀ t, a.2.2.2 .Y (chunkOf (y.1 t)) ≠ 0) ∧
               (∀ t, a.2.2.2 .Z (chunkOf (z.1 t)) ≠ 0)
            then tensorPower
              (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
                (coord .Z a.2.2.1)) k x.1 y.1 z.1
            else 0) * T.tensor x.2 y.2 z.2 }

theorem inventoryTensorZ_perm (q : ℕ) {I J : Inventory} (n : ℕ) (ε : ℚ)
    (h : I.Perm J) :
    ∃ (eX : (inventoryTensorZ q I n ε).X ≃ (inventoryTensorZ q J n ε).X)
      (eY : (inventoryTensorZ q I n ε).Y ≃ (inventoryTensorZ q J n ε).Y)
      (eZ : (inventoryTensorZ q I n ε).Z ≃ (inventoryTensorZ q J n ε).Z),
      ∀ x y z, (inventoryTensorZ q J n ε).tensor (eX x) (eY y) (eZ z) =
        (inventoryTensorZ q I n ε).tensor x y z := by
  classical
  induction h with
  | nil =>
      exact ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ _ => rfl⟩
  | cons a h ih =>
      rcases ih with ⟨eX, eY, eZ, he⟩
      refine ⟨Equiv.prodCongr (Equiv.refl _) eX,
        Equiv.prodCongr (Equiv.refl _) eY,
        Equiv.prodCongr (Equiv.refl _) eZ, ?_⟩
      intro x y z
      rcases x with ⟨x₀, x⟩
      rcases y with ⟨y₀, y⟩
      rcases z with ⟨z₀, z⟩
      simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ]
      change _ * (inventoryTensorZ q _ n ε).tensor (eX x) (eY y) (eZ z) =
        _ * (inventoryTensorZ q _ n ε).tensor x y z
      rw [he]
      simp [Equiv.prodCongr]
  | swap a b tail =>
      let eX : (inventoryTensorZ q (b :: a :: tail) n ε).X ≃
          (inventoryTensorZ q (a :: b :: tail) n ε).X :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eY : (inventoryTensorZ q (b :: a :: tail) n ε).Y ≃
          (inventoryTensorZ q (a :: b :: tail) n ε).Y :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eZ : (inventoryTensorZ q (b :: a :: tail) n ε).Z ≃
          (inventoryTensorZ q (a :: b :: tail) n ε).Z :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      refine ⟨eX, eY, eZ, ?_⟩
      intro x y z
      simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ, eX, eY, eZ]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨eX₁, eY₁, eZ₁, he₁⟩
      rcases ih₂ with ⟨eX₂, eY₂, eZ₂, he₂⟩
      refine ⟨eX₁.trans eX₂, eY₁.trans eY₂, eZ₁.trans eZ₂, ?_⟩
      intro x y z
      exact (he₂ (eX₁ x) (eY₁ y) (eZ₁ z)).trans (he₁ x y z)

theorem inventoryTensorZ_filter_ne_zero (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ) :
    ∃ (eX : (inventoryTensorZ q I n ε).X ≃
        (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).X)
      (eY : (inventoryTensorZ q I n ε).Y ≃
        (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).Y)
      (eZ : (inventoryTensorZ q I n ε).Z ≃
        (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).Z),
      ∀ x y z,
        (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
            (eX x) (eY y) (eZ z) =
          (inventoryTensorZ q I n ε).tensor x y z := by
  classical
  induction I with
  | nil =>
      exact ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ _ => rfl⟩
  | cons a tail ih =>
      by_cases ha : a.1 ≠ 0
      · rw [show (a :: tail).filter (fun b => decide (b.1 ≠ 0)) =
            a :: tail.filter (fun b => decide (b.1 ≠ 0)) by simp [ha]]
        rcases ih with ⟨eX, eY, eZ, he⟩
        refine ⟨Equiv.prodCongr (Equiv.refl _) eX,
          Equiv.prodCongr (Equiv.refl _) eY,
          Equiv.prodCongr (Equiv.refl _) eZ, ?_⟩
        intro x y z
        rcases x with ⟨x₀, x⟩
        rcases y with ⟨y₀, y⟩
        rcases z with ⟨z₀, z⟩
        simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ]
        change _ * (inventoryTensorZ q _ n ε).tensor (eX x) (eY y) (eZ z) =
          _ * (inventoryTensorZ q _ n ε).tensor x y z
        rw [he]
        simp [Equiv.prodCongr]
      · have ha0 : a.1 = 0 := not_ne_iff.mp ha
        have hk : (a.1 * (n : ℚ)).floor.toNat = 0 := by
          rw [ha0, zero_mul]
          change (((((0 : ℤ) : ℚ).floor).toNat) = 0)
          rw [Rat.floor_intCast]
          rfl
        rw [show (a :: tail).filter (fun b => decide (b.1 ≠ 0)) =
            tail.filter (fun b => decide (b.1 ≠ 0)) by simp [ha]]
        let eX : (inventoryTensorZ q (a :: tail) n ε).X ≃
            (inventoryTensorZ q tail n ε).X :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        let eY : (inventoryTensorZ q (a :: tail) n ε).Y ≃
            (inventoryTensorZ q tail n ε).Y :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        let eZ : (inventoryTensorZ q (a :: tail) n ε).Z ≃
            (inventoryTensorZ q tail n ε).Z :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        have hdrop : ∀ x y z,
            (inventoryTensorZ q tail n ε).tensor x.2 y.2 z.2 =
              (inventoryTensorZ q (a :: tail) n ε).tensor x y z := by
          intro x y z
          simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ,
            hk, if_true, one_mul]
        rcases ih with ⟨fX, fY, fZ, hf⟩
        refine ⟨eX.trans fX, eY.trans fY, eZ.trans fZ, ?_⟩
        intro x y z
        change (inventoryTensorZ q _ n ε).tensor (fX (eX x)) (fY (eY y)) (fZ (eZ z)) =
          (inventoryTensorZ q (a :: tail) n ε).tensor x y z
        exact (hf (eX x) (eY y) (eZ z)).trans (by
          simpa only [eX, eY, eZ] using hdrop x y z)

theorem inventory_transport (q : ℕ) (I J : Inventory) (n : ℕ) (ε : ℚ)
    (h : InventoryEq I J)
    (_hI : ∀ a ∈ I, ∃ k : ℕ, a.1*(n:ℚ) = k)
    (_hJ : ∀ a ∈ J, ∃ k : ℕ, a.1*(n:ℚ) = k) :
  ∃ (eX : (inventoryTensorZ q I n ε).X ≃ (inventoryTensorZ q J n ε).X)
    (eY : (inventoryTensorZ q I n ε).Y ≃ (inventoryTensorZ q J n ε).Y)
    (eZ : (inventoryTensorZ q I n ε).Z ≃ (inventoryTensorZ q J n ε).Z),
    ∀ x y z, (inventoryTensorZ q J n ε).tensor (eX x) (eY y) (eZ z) =
      (inventoryTensorZ q I n ε).tensor x y z := by
  classical
  rcases inventoryTensorZ_filter_ne_zero q I n ε with ⟨eXI, eYI, eZI, hI⟩
  rcases inventoryTensorZ_perm q n ε h with ⟨eXP, eYP, eZP, hP⟩
  rcases inventoryTensorZ_filter_ne_zero q J n ε with ⟨eXJ, eYJ, eZJ, hJ⟩
  refine ⟨eXI.trans (eXP.trans eXJ.symm), eYI.trans (eYP.trans eYJ.symm),
    eZI.trans (eZP.trans eZJ.symm), ?_⟩
  intro x y z
  calc
    (inventoryTensorZ q J n ε).tensor
        ((eXI.trans (eXP.trans eXJ.symm)) x)
        ((eYI.trans (eYP.trans eYJ.symm)) y)
        ((eZI.trans (eZP.trans eZJ.symm)) z) =
      (inventoryTensorZ q (J.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXP (eXI x)) (eYP (eYI y)) (eZP (eZI z)) := by
          symm
          simpa using hJ (eXJ.symm (eXP (eXI x))) (eYJ.symm (eYP (eYI y)))
            (eZJ.symm (eZP (eZI z)))
    _ = (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXI x) (eYI y) (eZI z) := hP _ _ _
    _ = (inventoryTensorZ q I n ε).tensor x y z := hI _ _ _

theorem supportedInventoryTensorZ_perm (q : ℕ) {I J : Inventory} (n : ℕ) (ε : ℚ)
    (h : I.Perm J) :
    ∃ (eX : (supportedInventoryTensorZ q I n ε).X ≃
        (supportedInventoryTensorZ q J n ε).X)
      (eY : (supportedInventoryTensorZ q I n ε).Y ≃
        (supportedInventoryTensorZ q J n ε).Y)
      (eZ : (supportedInventoryTensorZ q I n ε).Z ≃
        (supportedInventoryTensorZ q J n ε).Z),
      ∀ x y z, (supportedInventoryTensorZ q J n ε).tensor (eX x) (eY y) (eZ z) =
        (supportedInventoryTensorZ q I n ε).tensor x y z := by
  classical
  induction h with
  | nil =>
      exact ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ _ => rfl⟩
  | cons a h ih =>
      rcases ih with ⟨eX, eY, eZ, he⟩
      refine ⟨Equiv.prodCongr (Equiv.refl _) eX,
        Equiv.prodCongr (Equiv.refl _) eY,
        Equiv.prodCongr (Equiv.refl _) eZ, ?_⟩
      intro x y z
      rcases x with ⟨x₀, x⟩
      rcases y with ⟨y₀, y⟩
      rcases z with ⟨z₀, z⟩
      simp only [supportedInventoryTensorZ]
      change _ * (supportedInventoryTensorZ q _ n ε).tensor (eX x) (eY y) (eZ z) =
        _ * (supportedInventoryTensorZ q _ n ε).tensor x y z
      rw [he]
      simp [Equiv.prodCongr]
  | swap a b tail =>
      let eX : (supportedInventoryTensorZ q (b :: a :: tail) n ε).X ≃
          (supportedInventoryTensorZ q (a :: b :: tail) n ε).X :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eY : (supportedInventoryTensorZ q (b :: a :: tail) n ε).Y ≃
          (supportedInventoryTensorZ q (a :: b :: tail) n ε).Y :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eZ : (supportedInventoryTensorZ q (b :: a :: tail) n ε).Z ≃
          (supportedInventoryTensorZ q (a :: b :: tail) n ε).Z :=
        { toFun := fun x => (x.2.1, (x.1, x.2.2))
          invFun := fun x => (x.2.1, (x.1, x.2.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      refine ⟨eX, eY, eZ, ?_⟩
      intro x y z
      simp only [supportedInventoryTensorZ, eX, eY, eZ]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨eX₁, eY₁, eZ₁, he₁⟩
      rcases ih₂ with ⟨eX₂, eY₂, eZ₂, he₂⟩
      refine ⟨eX₁.trans eX₂, eY₁.trans eY₂, eZ₁.trans eZ₂, ?_⟩
      intro x y z
      exact (he₂ (eX₁ x) (eY₁ y) (eZ₁ z)).trans (he₁ x y z)

theorem supportedInventoryTensorZ_filter_ne_zero
    (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ) :
    ∃ (eX : (supportedInventoryTensorZ q I n ε).X ≃
        (supportedInventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).X)
      (eY : (supportedInventoryTensorZ q I n ε).Y ≃
        (supportedInventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).Y)
      (eZ : (supportedInventoryTensorZ q I n ε).Z ≃
        (supportedInventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).Z),
      ∀ x y z,
        (supportedInventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
            (eX x) (eY y) (eZ z) =
          (supportedInventoryTensorZ q I n ε).tensor x y z := by
  classical
  induction I with
  | nil =>
      exact ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ _ => rfl⟩
  | cons a tail ih =>
      by_cases ha : a.1 ≠ 0
      · rw [show (a :: tail).filter (fun b => decide (b.1 ≠ 0)) =
            a :: tail.filter (fun b => decide (b.1 ≠ 0)) by simp [ha]]
        rcases ih with ⟨eX, eY, eZ, he⟩
        refine ⟨Equiv.prodCongr (Equiv.refl _) eX,
          Equiv.prodCongr (Equiv.refl _) eY,
          Equiv.prodCongr (Equiv.refl _) eZ, ?_⟩
        intro x y z
        rcases x with ⟨x₀, x⟩
        rcases y with ⟨y₀, y⟩
        rcases z with ⟨z₀, z⟩
        simp only [supportedInventoryTensorZ]
        change _ * (supportedInventoryTensorZ q _ n ε).tensor (eX x) (eY y) (eZ z) =
          _ * (supportedInventoryTensorZ q _ n ε).tensor x y z
        rw [he]
        simp [Equiv.prodCongr]
      · have ha0 : a.1 = 0 := not_ne_iff.mp ha
        have hk : (a.1 * (n : ℚ)).floor.toNat = 0 := by
          rw [ha0, zero_mul]
          change (((((0 : ℤ) : ℚ).floor).toNat) = 0)
          rw [Rat.floor_intCast]
          rfl
        rw [show (a :: tail).filter (fun b => decide (b.1 ≠ 0)) =
            tail.filter (fun b => decide (b.1 ≠ 0)) by simp [ha]]
        let eX : (supportedInventoryTensorZ q (a :: tail) n ε).X ≃
            (supportedInventoryTensorZ q tail n ε).X :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        let eY : (supportedInventoryTensorZ q (a :: tail) n ε).Y ≃
            (supportedInventoryTensorZ q tail n ε).Y :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        let eZ : (supportedInventoryTensorZ q (a :: tail) n ε).Z ≃
            (supportedInventoryTensorZ q tail n ε).Z :=
          { toFun := fun x => x.2
            invFun := fun x => (fun i => Fin.elim0 (Fin.cast hk i), x)
            left_inv := by
              intro x
              apply Prod.ext
              · funext i
                exact Fin.elim0 (Fin.cast hk i)
              · rfl
            right_inv := fun _ => rfl }
        have hdrop : ∀ x y z,
            (supportedInventoryTensorZ q tail n ε).tensor x.2 y.2 z.2 =
              (supportedInventoryTensorZ q (a :: tail) n ε).tensor x y z := by
          intro x y z
          simp only [supportedInventoryTensorZ, hk, if_true, one_mul]
        rcases ih with ⟨fX, fY, fZ, hf⟩
        refine ⟨eX.trans fX, eY.trans fY, eZ.trans fZ, ?_⟩
        intro x y z
        change (supportedInventoryTensorZ q _ n ε).tensor
            (fX (eX x)) (fY (eY y)) (fZ (eZ z)) =
          (supportedInventoryTensorZ q (a :: tail) n ε).tensor x y z
        exact (hf (eX x) (eY y) (eZ z)).trans (by
          simpa only [eX, eY, eZ] using hdrop x y z)

theorem supported_inventory_transport (q : ℕ) (I J : Inventory) (n : ℕ) (ε : ℚ)
    (h : InventoryEq I J)
    (_hI : ∀ a ∈ I, ∃ k : ℕ, a.1 * (n : ℚ) = k)
    (_hJ : ∀ a ∈ J, ∃ k : ℕ, a.1 * (n : ℚ) = k) :
  ∃ (eX : (supportedInventoryTensorZ q I n ε).X ≃
      (supportedInventoryTensorZ q J n ε).X)
    (eY : (supportedInventoryTensorZ q I n ε).Y ≃
      (supportedInventoryTensorZ q J n ε).Y)
    (eZ : (supportedInventoryTensorZ q I n ε).Z ≃
      (supportedInventoryTensorZ q J n ε).Z),
    ∀ x y z, (supportedInventoryTensorZ q J n ε).tensor (eX x) (eY y) (eZ z) =
      (supportedInventoryTensorZ q I n ε).tensor x y z := by
  classical
  rcases supportedInventoryTensorZ_filter_ne_zero q I n ε with ⟨eXI, eYI, eZI, hI⟩
  rcases supportedInventoryTensorZ_perm q n ε h with ⟨eXP, eYP, eZP, hP⟩
  rcases supportedInventoryTensorZ_filter_ne_zero q J n ε with ⟨eXJ, eYJ, eZJ, hJ⟩
  refine ⟨eXI.trans (eXP.trans eXJ.symm), eYI.trans (eYP.trans eYJ.symm),
    eZI.trans (eZP.trans eZJ.symm), ?_⟩
  intro x y z
  calc
    (supportedInventoryTensorZ q J n ε).tensor
        ((eXI.trans (eXP.trans eXJ.symm)) x)
        ((eYI.trans (eYP.trans eYJ.symm)) y)
        ((eZI.trans (eZP.trans eZJ.symm)) z) =
      (supportedInventoryTensorZ q (J.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXP (eXI x)) (eYP (eYI y)) (eZP (eZI z)) := by
          symm
          simpa using hJ (eXJ.symm (eXP (eXI x))) (eYJ.symm (eYP (eYI y)))
            (eZJ.symm (eZP (eZI z)))
    _ = (supportedInventoryTensorZ q
          (I.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXI x) (eYI y) (eZI z) := hP _ _ _
    _ = (supportedInventoryTensorZ q I n ε).tensor x y z := hI _ _ _

end OmegaBound.ADVXXZGeneral
end
