import OmegaBound.ADVXXZGeneralAmend27CRepair
import OmegaBound.ADVXXZGeneralAmend27CExact
import OmegaBound.ADVXXZGeneralAmend25Ordered

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

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def singletonIndex27 (I : Type) : ((t : PUnit) × I) ≃ I where
  toFun := fun x => x.2
  invFun := fun i => ⟨PUnit.unit,i⟩
  left_inv := by rintro ⟨⟨⟩,i⟩; rfl
  right_inv := fun _ => rfl

section GlobalPhysical
variable {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n)
  (r : Fin 6) (j : (globalPopulation g n ξ r).Label)

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
abbrev GlobalExactPart27 (W : Side) :=
  {a : (globalPopulation g n ξ r).Part W // (globalPopulation g n ξ r).incidence W j a}

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
abbrev GlobalExactLeg27 (W : Side) :=
  {x : GlobalPhysicalWord q g n ξ r //
    (globalPopulation g n ξ r).incidence W j (globalPhysicalPart q g n ξ r W x)}

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalExactPart27 (W : Side) :
    GlobalExactLeg27 q g n ξ r j W → GlobalExactPart27 g n ξ r j W :=
  fun x => ⟨globalPhysicalPart q g n ξ r W x.val, x.property⟩

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalExactTensorZ27 : Tensor3 ℤ (GlobalExactLeg27 q g n ξ r j .X)
    (GlobalExactLeg27 q g n ξ r j .Y) (GlobalExactLeg27 q g n ξ r j .Z) :=
  fun x y z => ∏ i : Fin (globalPopulation g n ξ r).n,
    conZ q w (coord .X (j.val i)) (coord .Y (j.val i)) (coord .Z (j.val i))
      (x.val i) (y.val i) (z.val i)

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalColour27 (_ : PUnit) (i : Fin (globalPopulation g n ξ r).n) : Shape w := j.val i

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalCounts27 (W : Side) (_ : PUnit) (u : Shape w) (σ : Chunk w) : ℕ := ξ.count W r u σ

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
theorem globalExact_iff_partition27 (W : Side) (a : (globalPopulation g n ξ r).Part W) :
    (globalPopulation g n ξ r).incidence W j a ↔
      PartitionExact27 (globalColour27 g n ξ r j) (fun _ u => u)
        (globalCounts27 g n ξ r) W (fun i => a i.2) := by
  change ((∀ i, chunkLvl (a i) = coord W (j.val i)) ∧
    ∀ u σ, (Finset.univ.filter fun i => j.val i = u ∧ a i = σ).card = ξ.count W r u σ) ↔ _
  simp only [PartitionExact27, globalColour27, globalCounts27, histogram27, Prod.mk.injEq]
  constructor
  · rintro ⟨hg,hc⟩; exact ⟨fun _ => hg, fun _ => hc⟩
  · rintro ⟨hg,hc⟩; exact ⟨hg PUnit.unit, hc PUnit.unit⟩

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalPartEquiv27 (W : Side) : GlobalExactPart27 g n ξ r j W ≃
    PartitionPart27 (globalColour27 g n ξ r j) (fun _ u => u) (globalCounts27 g n ξ r) W :=
  Equiv.subtypeEquiv
    (Equiv.arrowCongr (singletonIndex27 (Fin (globalPopulation g n ξ r).n)).symm (Equiv.refl _))
    (globalExact_iff_partition27 g n ξ r j W)

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def globalLegEquiv27 (W : Side) : GlobalExactLeg27 q g n ξ r j W ≃
    PartitionLeg27 (globalColour27 g n ξ r j) (fun _ u => u) (globalCounts27 g n ξ r) q W :=
  Equiv.subtypeEquiv
    (Equiv.arrowCongr (singletonIndex27 (Fin (globalPopulation g n ξ r).n)).symm (Equiv.refl _))
    (fun x => globalExact_iff_partition27 g n ξ r j W (globalPhysicalPart q g n ξ r W x))

/-- Paper clause: `H/hole.tex:121–132; P/global.tex:311`. -/
def global_exact_interface_shuffles27 :
    Shuffles (globalExactPart27 q g n ξ r j .X) (globalExactPart27 q g n ξ r j .Y)
      (globalExactPart27 q g n ξ r j .Z) (globalExactTensorZ27 q g n ξ r j)
      (PartitionGroup27 (globalColour27 g n ξ r j)) :=
  transportShuffles27 (partitionShuffles27 (globalColour27 g n ξ r j) (fun _ u => u)
    (globalCounts27 g n ξ r) q)
    (globalLegEquiv27 q g n ξ r j .X) (globalLegEquiv27 q g n ξ r j .Y)
    (globalLegEquiv27 q g n ξ r j .Z)
    (globalPartEquiv27 g n ξ r j .X) (globalPartEquiv27 g n ξ r j .Y)
    (globalPartEquiv27 g n ξ r j .Z)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by
      intro x y z
      let f := fun i : Fin (globalPopulation g n ξ r).n =>
        conZ q w (coord .X (j.val i)) (coord .Y (j.val i)) (coord .Z (j.val i))
          (x.val i) (y.val i) (z.val i)
      change (∏ i, f i) = ∏ k : (t : PUnit) × Fin (globalPopulation g n ξ r).n, f k.2
      exact (Equiv.prod_comp (singletonIndex27 _) f).symm)
end GlobalPhysical
end
end OmegaBound.ADVXXZGeneral
end
