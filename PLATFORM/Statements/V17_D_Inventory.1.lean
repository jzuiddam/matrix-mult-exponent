/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_D_Inventory.1
paper_clause: the actual output occurrence list and accumulated boundary matrix factors (P/constituent.tex:120,169,341; P/numerical.tex:19–22).
sha256: 9b63c4e64dce8ac8ca0bcd1f87652fab59b9a7c2ef60f0b1c5101e9aa02bf270
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralCertInventory
import OmegaBound.ADVXXZGeneralTensor

-- P2M-DEF Def_V17_D_Inventory_1 P2M.V17_D_Inventory.inventoryTensorZ
section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open OmegaBound.ADVXXZGeneral
open scoped BigOperators
namespace P2M.V17_D_Inventory

noncomputable def inventoryTensorZ (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ) : ITensor :=
  match I with
  | [] =>
      { X := PUnit
        Y := PUnit
        Z := PUnit
        tensor := fun _ _ _ => 1 }
  | a :: tail =>
      let k := (a.1 * (n : ℚ)).floor.toNat
      let T := inventoryTensorZ q tail n ε
      { X := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.X
        Y := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.Y
        Z := (Fin k → Fin a.2.1 → CW90.Idx7 q) × T.Z
        tensor := fun x y z =>
          (if k = 0 then 1 else
            if (∀ σ, |emp (chunkSeq x.1) σ - a.2.2.2 .X σ| ≤ ε) ∧
               (∀ σ, |emp (chunkSeq y.1) σ - a.2.2.2 .Y σ| ≤ ε) ∧
               (∀ σ, |emp (chunkSeq z.1) σ - a.2.2.2 .Z σ| ≤ ε)
            then tensorPower
              (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
                (coord .Z a.2.2.1)) k x.1 y.1 z.1
            else 0) * T.tensor x.2 y.2 z.2 }

end P2M.V17_D_Inventory
end
