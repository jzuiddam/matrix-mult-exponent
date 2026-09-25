import OmegaBound.ADVXXZGeneralReleasedInventoryAux
import Mathlib.Data.Fin.Tuple.Basic

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private def uniformInventoryEntries {w : ℕ} : {s : ℕ} →
    (Fin s → ℚ) → (Fin s → Shape w) → (Side → Fin s → SplitDist w) → Inventory
  | 0, _mass, _shape, _beta => []
  | s + 1, mass, shape, beta =>
      (mass 0, ⟨w, shape 0, fun W σ => (beta W 0).prob σ⟩) ::
        uniformInventoryEntries (fun t : Fin s => mass t.succ)
          (fun t : Fin s => shape t.succ) (fun W t => beta W t.succ)

private def uniformCount {s : ℕ} (mass : Fin s → ℚ) (n : ℕ) (t : Fin s) : ℕ :=
  (mass t * (n : ℚ)).floor.toNat

private theorem uniformInventoryEntries_eq {s w : ℕ} (mass : Fin s → ℚ)
    (shape : Fin s → Shape w) (beta : Side → Fin s → SplitDist w) :
    uniformInventoryEntries mass shape beta =
      (List.finRange s).map fun t =>
        (mass t, ⟨w, shape t, fun W σ => (beta W t).prob σ⟩) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      simp only [uniformInventoryEntries, List.finRange_succ, List.map_cons,
        List.map_map, Function.comp_def]
      rw [ih]

private noncomputable def uniformLegEquiv (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (inventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).X ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := uniformLegEquiv q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

private noncomputable def uniformLegEquivY (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (inventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).Y ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := uniformLegEquivY q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

private noncomputable def uniformLegEquivZ (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (inventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).Z ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := uniformLegEquivZ q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

private theorem uniform_plain_tensor (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    ∀ x y z,
      (inventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).tensor x y z =
        (ifaceZ q w (uniformCount mass n) (fun t => coord .X (shape t))
          (fun t => coord .Y (shape t)) (fun t => coord .Z (shape t)) beta ε).tensor
          (uniformLegEquiv q n ε mass shape beta x)
          (uniformLegEquivY q n ε mass shape beta y)
          (uniformLegEquivZ q n ε mass shape beta z) := by
  induction s with
  | zero =>
      intro x y z
      cases x
      cases y
      cases z
      rfl
  | succ s ih =>
      intro x y z
      change _ × _ at x
      change _ × _ at y
      change _ × _ at z
      rcases x with ⟨x₀, x⟩
      rcases y with ⟨y₀, y⟩
      rcases z with ⟨z₀, z⟩
      simp only [uniformInventoryEntries, List.finRange_succ, List.map_cons,
        List.map_map, Function.comp_apply, inventoryTensorZ,
        P2M.V17_D_Inventory.inventoryTensorZ, ifaceZ, uniformLegEquiv,
        uniformLegEquivY, uniformLegEquivZ,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
        Fin.consEquiv_apply, Fin.prod_univ_succ]
      change _ *
          (inventoryTensorZ q
            (uniformInventoryEntries (fun t : Fin s => mass t.succ)
              (fun t : Fin s => shape t.succ) (fun W t => beta W t.succ)) n ε).tensor x y z =
        _ * ∏ t : Fin s,
          ifaceTermZ q w (coord .X (shape t.succ)) (coord .Y (shape t.succ))
            (coord .Z (shape t.succ)) (uniformCount mass n t.succ)
            (beta .X t.succ) (beta .Y t.succ) (beta .Z t.succ) ε
            ((uniformLegEquiv q n ε (fun t : Fin s => mass t.succ)
              (fun t : Fin s => shape t.succ) (fun W t => beta W t.succ) x) t)
            ((uniformLegEquivY q n ε (fun t : Fin s => mass t.succ)
              (fun t : Fin s => shape t.succ) (fun W t => beta W t.succ) y) t)
            ((uniformLegEquivZ q n ε (fun t : Fin s => mass t.succ)
              (fun t : Fin s => shape t.succ) (fun W t => beta W t.succ) z) t)
      rw [ih (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ) x y z]
      rfl

private theorem uniform_inventory_plain_transport (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    OrdinaryTensorTransport
      (inventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε)
      (ifaceZ q w (uniformCount mass n) (fun t => coord .X (shape t))
        (fun t => coord .Y (shape t)) (fun t => coord .Z (shape t)) beta ε) := by
  exact ⟨uniformLegEquiv q n ε mass shape beta,
    uniformLegEquivY q n ε mass shape beta,
    uniformLegEquivZ q n ε mass shape beta,
    uniform_plain_tensor q n ε mass shape beta⟩

private theorem prob_ne_zero_iff_num_ne_zero {iota : Type*} [Fintype iota]
    (P : RatDist iota) (i : iota) : P.prob i ≠ 0 ↔ P.num i ≠ 0 := by
  simp [RatDist.prob, P.den_pos.ne']

private noncomputable def supportedUniformLegEquiv (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (supportedInventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).X ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := supportedUniformLegEquiv q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

private noncomputable def supportedUniformLegEquivY (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (supportedInventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).Y ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := supportedUniformLegEquivY q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

private noncomputable def supportedUniformLegEquivZ (q n : ℕ) (ε : ℚ) {w : ℕ} :
    {s : ℕ} → (mass : Fin s → ℚ) → (shape : Fin s → Shape w) →
      (beta : Side → Fin s → SplitDist w) →
      (supportedInventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).Z ≃
        ((t : Fin s) → Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q)
  | 0, _mass, _shape, _beta =>
      { toFun := fun _ t => Fin.elim0 t
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext t; exact Fin.elim0 t }
  | s + 1, mass, shape, beta => by
      let tailEquiv := supportedUniformLegEquivZ q n ε
        (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ)
      change (_ × _) ≃ _
      exact (Equiv.prodCongr (Equiv.refl _) tailEquiv).trans
        (Fin.consEquiv (fun t : Fin (s + 1) =>
          Fin (uniformCount mass n t) → Fin w → CW90.Idx7 q))

set_option maxHeartbeats 5000000 in
private theorem uniform_supported_tensor (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    ∀ x y z,
      (supportedInventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε).tensor x y z =
        (supportedIfaceZ q w (uniformCount mass n) (fun t => coord .X (shape t))
          (fun t => coord .Y (shape t)) (fun t => coord .Z (shape t)) beta ε).tensor
          (supportedUniformLegEquiv q n ε mass shape beta x)
          (supportedUniformLegEquivY q n ε mass shape beta y)
          (supportedUniformLegEquivZ q n ε mass shape beta z) := by
  induction s with
  | zero =>
      intro x y z
      cases x
      cases y
      cases z
      rfl
  | succ s ih =>
      intro x y z
      change _ × _ at x
      change _ × _ at y
      change _ × _ at z
      rcases x with ⟨x₀, x⟩
      rcases y with ⟨y₀, y⟩
      rcases z with ⟨z₀, z⟩
      simp only [uniformInventoryEntries, List.finRange_succ, List.map_cons,
        List.map_map, Function.comp_apply, supportedInventoryTensorZ, supportedIfaceZ,
        zoP, ifaceZ, supportedUniformLegEquiv, supportedUniformLegEquivY,
        supportedUniformLegEquivZ, Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.refl_apply, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.forall_fin_succ, prob_ne_zero_iff_num_ne_zero]
      rw [ih (fun t : Fin s => mass t.succ) (fun t : Fin s => shape t.succ)
        (fun W t => beta W t.succ) x y z]
      by_cases hk : uniformCount mass n 0 = 0
      · have hcount : (mass 0 * (n : ℚ)).floor.toNat = 0 := by
          simpa [uniformCount] using hk
        have hX0 : ∀ a : Fin (mass 0 * (n : ℚ)).floor.toNat,
            (beta .X 0).num (chunkOf (x₀ a)) ≠ 0 := by
          intro a
          exact Fin.elim0 (Fin.cast hcount a)
        have hY0 : ∀ a : Fin (mass 0 * (n : ℚ)).floor.toNat,
            (beta .Y 0).num (chunkOf (y₀ a)) ≠ 0 := by
          intro a
          exact Fin.elim0 (Fin.cast hcount a)
        have hZ0 : ∀ a : Fin (mass 0 * (n : ℚ)).floor.toNat,
            (beta .Z 0).num (chunkOf (z₀ a)) ≠ 0 := by
          intro a
          exact Fin.elim0 (Fin.cast hcount a)
        simp_all [uniformCount, supportedIfaceZ, zoP, ifaceZ,
          Fin.forall_fin_succ, ifaceTermZ, ApproxConsistent]
      · split_ifs <;> simp_all [uniformCount, supportedIfaceZ, zoP, ifaceZ,
          Fin.forall_fin_succ, ifaceTermZ, ApproxConsistent] <;> aesop <;> omega

private theorem uniform_inventory_supported_transport (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    OrdinaryTensorTransport
      (supportedInventoryTensorZ q (uniformInventoryEntries mass shape beta) n ε)
      (supportedIfaceZ q w (uniformCount mass n) (fun t => coord .X (shape t))
        (fun t => coord .Y (shape t)) (fun t => coord .Z (shape t)) beta ε) := by
  exact ⟨supportedUniformLegEquiv q n ε mass shape beta,
    supportedUniformLegEquivY q n ε mass shape beta,
    supportedUniformLegEquivZ q n ε mass shape beta,
    uniform_supported_tensor q n ε mass shape beta⟩

theorem finRange_inventory_plain_transport (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    OrdinaryTensorTransport
      (inventoryTensorZ q ((List.finRange s).map fun t =>
        (mass t, ⟨w, shape t, fun W σ => (beta W t).prob σ⟩)) n ε)
      (ifaceZ q w (fun t => (mass t * (n : ℚ)).floor.toNat)
        (fun t => coord .X (shape t)) (fun t => coord .Y (shape t))
        (fun t => coord .Z (shape t)) beta ε) := by
  simpa only [uniformInventoryEntries_eq, uniformCount] using
    uniform_inventory_plain_transport q n ε mass shape beta

theorem finRange_inventory_supported_transport (q n : ℕ) (ε : ℚ) {s w : ℕ}
    (mass : Fin s → ℚ) (shape : Fin s → Shape w)
    (beta : Side → Fin s → SplitDist w) :
    OrdinaryTensorTransport
      (supportedInventoryTensorZ q ((List.finRange s).map fun t =>
        (mass t, ⟨w, shape t, fun W σ => (beta W t).prob σ⟩)) n ε)
      (supportedIfaceZ q w (fun t => (mass t * (n : ℚ)).floor.toNat)
        (fun t => coord .X (shape t)) (fun t => coord .Y (shape t))
        (fun t => coord .Z (shape t)) beta ε) := by
  simpa only [uniformInventoryEntries_eq, uniformCount] using
    uniform_inventory_supported_transport q n ε mass shape beta

end OmegaBound.ADVXXZGeneral
end
