import OmegaBound.ADVXXZGeneralRepairFibres
import OmegaBound.ADVXXZGeneralAmend25Rates
import OmegaBound.ADVXXZShufCW

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

open OmegaBound.ADVXXZShuf
section Transport
variable {X Y Z PX PY PZ X' Y' Z' PX' PY' PZ' ξ : Type}
  [Fintype X] [Fintype Y] [Fintype Z] [Fintype PX] [Fintype PY] [Fintype PZ]
  [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype PX'] [Fintype PY'] [Fintype PZ']
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
  [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
  [DecidableEq PX'] [DecidableEq PY'] [DecidableEq PZ'] [DecidableEq ξ]

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def transportShuffles27 {pX : X → PX} {pY : Y → PY} {pZ : Z → PZ}
    {pX' : X' → PX'} {pY' : Y' → PY'} {pZ' : Z' → PZ'}
    {T : Tensor3 ℤ X Y Z} {T' : Tensor3 ℤ X' Y' Z'}
    (S : Shuffles pX pY pZ T ξ)
    (eX : X' ≃ X) (eY : Y' ≃ Y) (eZ : Z' ≃ Z)
    (ePX : PX' ≃ PX) (ePY : PY' ≃ PY) (ePZ : PZ' ≃ PZ)
    (hpX : ∀ x, ePX (pX' x) = pX (eX x))
    (hpY : ∀ y, ePY (pY' y) = pY (eY y))
    (hpZ : ∀ z, ePZ (pZ' z) = pZ (eZ z))
    (hT : ∀ x y z, T' x y z = T (eX x) (eY y) (eZ z)) :
    Shuffles pX' pY' pZ' T' ξ where
  G := S.G
  ne := S.ne
  sX g := (eX.trans (S.sX g)).trans eX.symm
  sY g := (eY.trans (S.sY g)).trans eY.symm
  sZ g := (eZ.trans (S.sZ g)).trans eZ.symm
  tX g := (ePX.trans (S.tX g)).trans ePX.symm
  tY g := (ePY.trans (S.tY g)).trans ePY.symm
  tZ g := (ePZ.trans (S.tZ g)).trans ePZ.symm
  partX g x := by apply ePX.injective; simp [hpX, S.partX]
  partY g y := by apply ePY.injective; simp [hpY, S.partY]
  partZ g z := by apply ePZ.injective; simp [hpZ, S.partZ]
  inv g x y z := by simpa only [Equiv.trans_apply, hT, Equiv.apply_symm_apply] using S.inv g (eX x) (eY y) (eZ z)
  uniX a b := by
    simpa only [Equiv.trans_apply, Equiv.symm_apply_eq, Fintype.card_congr ePX] using S.uniX (ePX a) (ePX b)
  uniY a b := by
    simpa only [Equiv.trans_apply, Equiv.symm_apply_eq, Fintype.card_congr ePY] using S.uniY (ePY a) (ePY b)
  uniZ a b := by
    simpa only [Equiv.trans_apply, Equiv.symm_apply_eq, Fintype.card_congr ePZ] using S.uniZ (ePZ a) (ePZ b)
end Transport

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev StageExactPart27 {w s : ℕ} (q b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (W : Side) := {a // a ∈ exactPartsAt q b m p d r j W}

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev StageExactLeg27 {w s : ℕ} (q b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (W : Side) := {x : StagePhysicalWord q p d b m r //
      stagePhysicalPart q p d b m r W x ∈ exactPartsAt q b m p d r j W}

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageExactPart27 {w s : ℕ} (q b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (W : Side) : StageExactLeg27 q b m p d r j W → StageExactPart27 q b m p d r j W :=
  fun x => ⟨stagePhysicalPart q p d b m r W x.val, x.property⟩

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageExactTensorZ27 {w s : ℕ} (q b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label) :
    Tensor3 ℤ (StageExactLeg27 q b m p d r j .X)
      (StageExactLeg27 q b m p d r j .Y) (StageExactLeg27 q b m p d r j .Z) :=
  fun x y z => ∏ pos : StageCandidateRaw.StagePos b m p d r,
    conZ q w (coord .X (j.val pos).val) (coord .Y (j.val pos).val)
      (coord .Z (j.val pos).val) (x.val pos) (y.val pos) (z.val pos)

section FiniteColour
variable {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def ColourPerm27 (c : I → A) : Subgroup (Equiv.Perm I) where
  carrier := {g | ∀ i, c (g i) = c i}
  one_mem' := by intro i; rfl
  mul_mem' := by intro g h hg hh i; exact (hg (h i)).trans (hh i)
  inv_mem' := by intro g hg i; exact (hg (g.symm i)).symm.trans (congrArg c (g.apply_symm_apply i))

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
instance colourPermFintype27 (c : I → A) : Fintype (ColourPerm27 c) := Fintype.ofFinite _

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def histogram27 (f : I → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => f i = a).card

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem histogram_perm27 (f : I → A) (e : Equiv.Perm I) (a : A) :
    histogram27 (fun i => f (e i)) a = histogram27 f a := by
  unfold histogram27
  exact Finset.card_equiv e (by intro i; simp)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def histogramEquiv27 (f g : I → A) (h : ∀ a, histogram27 f a = histogram27 g a) :
    Equiv.Perm I :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact h a)).trans
      (Equiv.sigmaFiberEquiv g))

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem histogramEquiv27_spec (f g : I → A) (h : ∀ a, histogram27 f a = histogram27 g a)
    (i : I) : g (histogramEquiv27 f g h i) = f i := by
  exact (Fintype.equivOfCardEq (show Fintype.card {j // f j = f i} =
    Fintype.card {j // g j = f i} from by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact h (f i)) ⟨i, rfl⟩).property
end FiniteColour

section Partition
variable {T : Type} [Fintype T] [DecidableEq T]
variable {I A : T → Type} [∀ t, Fintype (I t)] [∀ t, DecidableEq (I t)]
  [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]
variable {w : ℕ} (c : (t : T) → I t → A t) (shape : (t : T) → A t → Shape w)
  (counts : Side → (t : T) → A t → Chunk w → ℕ)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev PartitionWord27 := (t : T) × I t → Chunk w

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def PartitionExact27 (W : Side) (a : PartitionWord27 (I := I) (w := w)) : Prop :=
  (∀ t i, chunkLvl (a ⟨t, i⟩) = coord W (shape t (c t i))) ∧
  ∀ t u σ, histogram27 (fun i => (c t i, a ⟨t, i⟩)) (u, σ) = counts W t u σ

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev PartitionGroup27 := (t : T) → ColourPerm27 (c t)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionIndexPerm27 (g : PartitionGroup27 c) : Equiv.Perm ((t : T) × I t) :=
  Equiv.sigmaCongrRight fun t => (g t).val

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem partitionExact_perm27 (W : Side) (a : PartitionWord27 (I := I) (w := w))
    (g : PartitionGroup27 c) :
    PartitionExact27 c shape counts W (a ∘ partitionIndexPerm27 c g) ↔
      PartitionExact27 c shape counts W a := by
  have hg : ∀ t u σ, histogram27 (fun i => (c t i, a ⟨t, (g t).val i⟩)) (u, σ) =
      histogram27 (fun i => (c t i, a ⟨t, i⟩)) (u, σ) := by
    intro t u σ
    conv_lhs => arg 1; ext i; rw [← (g t).property i]
    exact histogram_perm27 (fun i => (c t i, a ⟨t,i⟩)) (g t).val (u,σ)
  have hcolour : ∀ t i, c t ((g t).val i) = c t i := fun t i => (g t).property i
  constructor
  · rintro ⟨hgrade, hcount⟩
    constructor
    · intro t i
      have hi := hgrade t ((g t).val.symm i)
      have hiC : c t ((g t).val.symm i) = c t i := by
        simpa using (hcolour t ((g t).val.symm i)).symm
      simpa [partitionIndexPerm27, hiC] using hi
    · intro t u σ
      exact (hg t u σ).symm.trans (hcount t u σ)
  · rintro ⟨hgrade, hcount⟩
    constructor
    · intro t i
      simpa [partitionIndexPerm27, hcolour] using hgrade t ((g t).val i)
    · intro t u σ
      exact (hg t u σ).trans (hcount t u σ)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev PartitionPart27 (W : Side) := {a // PartitionExact27 c shape counts W a}

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
abbrev PartitionLeg27 (q : ℕ) (W : Side) :=
  {x : ((t : T) × I t) → Fin w → CW90.Idx7 q //
    PartitionExact27 c shape counts W (fun i => chunkOf (x i))}

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionPart27 (q : ℕ) (W : Side) :
    PartitionLeg27 c shape counts q W → PartitionPart27 c shape counts W :=
  fun x => ⟨fun i => chunkOf (x.val i), x.property⟩

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionPartPerm27 (W : Side) (g : PartitionGroup27 c) :
    Equiv.Perm (PartitionPart27 c shape counts W) :=
  Equiv.subtypeEquiv (preComp (partitionIndexPerm27 c g))
    (fun a => (partitionExact_perm27 c shape counts W a g).symm)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionLegPerm27 (q : ℕ) (W : Side) (g : PartitionGroup27 c) :
    Equiv.Perm (PartitionLeg27 c shape counts q W) :=
  Equiv.subtypeEquiv (preComp (partitionIndexPerm27 c g))
    (fun x => (partitionExact_perm27 c shape counts W (fun i => chunkOf (x i)) g).symm)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem partitionPartPerm_mul27 (W : Side) (g h : PartitionGroup27 c) :
    partitionPartPerm27 c shape counts W (g*h) =
      partitionPartPerm27 c shape counts W h * partitionPartPerm27 c shape counts W g := by
  ext a i
  rfl

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem partitionPart_transitive27 (W : Side) (a b : PartitionPart27 c shape counts W) :
    ∃ g : PartitionGroup27 c, partitionPartPerm27 c shape counts W g a = b := by
  have hc : ∀ t z, histogram27 (fun i => (c t i, b.val ⟨t,i⟩)) z =
      histogram27 (fun i => (c t i, a.val ⟨t,i⟩)) z := by
    intro t z; exact (b.property.2 t z.1 z.2).trans (a.property.2 t z.1 z.2).symm
  let e := fun t => histogramEquiv27 (fun i => (c t i, b.val ⟨t,i⟩))
    (fun i => (c t i, a.val ⟨t,i⟩)) (hc t)
  have he : ∀ t i, (c t (e t i), a.val ⟨t,e t i⟩) = (c t i, b.val ⟨t,i⟩) :=
    fun t i => histogramEquiv27_spec _ _ (hc t) i
  refine ⟨fun t => ⟨e t, fun i => congrArg Prod.fst (he t i)⟩, ?_⟩
  apply Subtype.ext
  funext i
  exact congrArg Prod.snd (he i.1 i.2)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionTensorZ27 (q : ℕ) : Tensor3 ℤ (PartitionLeg27 c shape counts q .X)
    (PartitionLeg27 c shape counts q .Y) (PartitionLeg27 c shape counts q .Z) :=
  fun x y z => ∏ i : (t : T) × I t,
    conZ q w (coord .X (shape i.1 (c i.1 i.2))) (coord .Y (shape i.1 (c i.1 i.2)))
      (coord .Z (shape i.1 (c i.1 i.2))) (x.val i) (y.val i) (z.val i)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def partitionShuffles27 (q : ℕ) :
    Shuffles (partitionPart27 c shape counts q .X) (partitionPart27 c shape counts q .Y)
      (partitionPart27 c shape counts q .Z) (partitionTensorZ27 c shape counts q)
      (PartitionGroup27 c) where
  G := Finset.univ
  ne := ⟨1, Finset.mem_univ _⟩
  sX := partitionLegPerm27 c shape counts q .X
  sY := partitionLegPerm27 c shape counts q .Y
  sZ := partitionLegPerm27 c shape counts q .Z
  tX := partitionPartPerm27 c shape counts .X
  tY := partitionPartPerm27 c shape counts .Y
  tZ := partitionPartPerm27 c shape counts .Z
  partX _ _ := rfl
  partY _ _ := rfl
  partZ _ _ := rfl
  inv g x y z := by
    let f := fun i : (t : T) × I t =>
      conZ q w (coord .X (shape i.1 (c i.1 i.2))) (coord .Y (shape i.1 (c i.1 i.2)))
        (coord .Z (shape i.1 (c i.1 i.2))) (x.val i) (y.val i) (z.val i)
    change _ = ∏ i, f i
    rw [← Equiv.prod_comp (partitionIndexPerm27 c g) f]
    apply Finset.prod_congr rfl
    intro i _
    have hc : c i.1 ((g i.1).val i.2) = c i.1 i.2 := (g i.1).property i.2
    change conZ q w _ _ _ (x.val ⟨i.1, (g i.1).val i.2⟩)
      (y.val ⟨i.1, (g i.1).val i.2⟩) (z.val ⟨i.1, (g i.1).val i.2⟩) = _
    dsimp only [f, partitionIndexPerm27, Equiv.sigmaCongrRight_apply]
    rw [hc]
  uniX a b := by
    rw [Finset.card_univ]
    exact card_filter_mul_card _ (partitionPartPerm_mul27 c shape counts .X)
      (partitionPart_transitive27 c shape counts .X) a b
  uniY a b := by
    rw [Finset.card_univ]
    exact card_filter_mul_card _ (partitionPartPerm_mul27 c shape counts .Y)
      (partitionPart_transitive27 c shape counts .Y) a b
  uniZ a b := by
    rw [Finset.card_univ]
    exact card_filter_mul_card _ (partitionPartPerm_mul27 c shape counts .Z)
      (partitionPart_transitive27 c shape counts .Z) a b
end Partition

section StagePhysical
variable {w s : ℕ} (q b m : ℕ) (p : ConstituentInput w s)
  (d : ConstituentSpec p) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageColour27 (t : Fin s) (i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :
    ChildShape p t := j.val ⟨t,i⟩

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageCounts27 (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) : ℕ :=
  (((m * d.outBase ⟨t,r,u⟩ : ℕ) : ℚ) * (d.betaChild W t r u).prob σ).floor.toNat

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
theorem stageExact_iff_partition27 (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    a ∈ exactPartsAt q b m p d r j W ↔
      PartitionExact27 (stageColour27 q b m p d r j) (fun _ u => u.val)
        (stageCounts27 m p d r) W a := by
  simp only [exactPartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  change ((∀ z : StageCandidateRaw.StagePos b m p d r,
    chunkLvl (a z) = coord W (j.val z).val) ∧
    ∀ t u σ, (Finset.univ.filter fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
      j.val ⟨t,i⟩ = u ∧ a ⟨t,i⟩ = σ).card = stageCounts27 m p d r W t u σ) ↔ _
  simp only [PartitionExact27, histogram27, stageColour27, Prod.mk.injEq]
  constructor
  · rintro ⟨hg,hc⟩; exact ⟨fun t i => hg ⟨t,i⟩, hc⟩
  · rintro ⟨hg,hc⟩; exact ⟨fun z => hg z.1 z.2, hc⟩

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stagePartEquiv27 (W : Side) : StageExactPart27 q b m p d r j W ≃
    PartitionPart27 (stageColour27 q b m p d r j) (fun _ u => u.val)
      (stageCounts27 m p d r) W :=
  Equiv.subtypeEquiv (Equiv.refl _) (stageExact_iff_partition27 q b m p d r j W)

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageLegEquiv27 (W : Side) : StageExactLeg27 q b m p d r j W ≃
    PartitionLeg27 (stageColour27 q b m p d r j) (fun _ u => u.val)
      (stageCounts27 m p d r) q W :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun x =>
    stageExact_iff_partition27 q b m p d r j W (stagePhysicalPart q p d b m r W x))

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def exact_interface_shuffles :
    Shuffles (stageExactPart27 q b m p d r j .X) (stageExactPart27 q b m p d r j .Y)
      (stageExactPart27 q b m p d r j .Z) (stageExactTensorZ27 q b m p d r j)
      (PartitionGroup27 (stageColour27 q b m p d r j)) :=
  transportShuffles27 (partitionShuffles27 (stageColour27 q b m p d r j) (fun _ u => u.val)
    (stageCounts27 m p d r) q)
    (stageLegEquiv27 q b m p d r j .X) (stageLegEquiv27 q b m p d r j .Y)
    (stageLegEquiv27 q b m p d r j .Z)
    (stagePartEquiv27 q b m p d r j .X) (stagePartEquiv27 q b m p d r j .Y)
    (stagePartEquiv27 q b m p d r j .Z)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
end StagePhysical

/-- Paper clause: `H/hole.tex:121–132; P/constituent.tex:341`. -/
def stageExactHoles27 {w s : ℕ} (q b m M : ℕ) (ε : ℚ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    Finset (StageExactPart27 q b m p d r j W) :=
  Finset.univ.filter fun a => a.val ∈ holesAt25 q b m M ε p d r B ω j W
end
end OmegaBound.ADVXXZGeneral
end
