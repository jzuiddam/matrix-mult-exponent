import OmegaBound.ADVXXZGeneralAmend27CRepair
import OmegaBound.ADVXXZGeneralHRepair

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

private theorem partitionExact_relabel27
    {T : Type} [Fintype T] [DecidableEq T]
    {I A : T → Type} [∀ t, Fintype (I t)] [∀ t, DecidableEq (I t)]
    [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)] {w : ℕ}
    (c c' : (t : T) → I t → A t) (shape : (t : T) → A t → Shape w)
    (counts : Side → (t : T) → A t → Chunk w → ℕ)
    (e : (t : T) → Equiv.Perm (I t))
    (hc : ∀ t i, c' t (e t i) = c t i) (W : Side)
    (a : PartitionWord27 (I := I) (w := w)) :
    PartitionExact27 c shape counts W a ↔
      PartitionExact27 c' shape counts W
        (a ∘ (Equiv.sigmaCongrRight e).symm) := by
  constructor
  · rintro ⟨hgrade,hcount⟩
    constructor
    · intro t i
      have hi := hgrade t ((e t).symm i)
      have hci : c' t i = c t ((e t).symm i) := by
        simpa using hc t ((e t).symm i)
      simpa [hci] using hi
    · intro t u σ
      let f := fun i : I t => (c t i, a ⟨t,i⟩)
      have hf : (fun i : I t =>
          (c' t i, (a ∘ (Equiv.sigmaCongrRight e).symm) ⟨t,i⟩)) =
          fun i => f ((e t).symm i) := by
        funext i
        have hci : c' t i = c t ((e t).symm i) := by
          simpa using hc t ((e t).symm i)
        simp only [Function.comp_apply, f, hci]
        rfl
      rw [hf, histogram_perm27 f (e t).symm (u,σ)]
      exact hcount t u σ
  · rintro ⟨hgrade,hcount⟩
    constructor
    · intro t i
      have hi := hgrade t (e t i)
      simpa [hc t i] using hi
    · intro t u σ
      let f := fun i : I t => (c t i, a ⟨t,i⟩)
      have hf : (fun i : I t =>
          (c' t i, (a ∘ (Equiv.sigmaCongrRight e).symm) ⟨t,i⟩)) =
          fun i => f ((e t).symm i) := by
        funext i
        have hci : c' t i = c t ((e t).symm i) := by
          simpa using hc t ((e t).symm i)
        simp only [Function.comp_apply, f, hci]
        rfl
      have hp := histogram_perm27 f (e t).symm (u,σ)
      rw [← hp, ← hf]
      exact hcount t u σ

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private theorem target_histogram27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (v : ChildShape p t) :
    histogram27 (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      j.val ⟨t,(i,0)⟩) v =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob v).floor.toNat := by
  have h := (Finset.mem_filter.mp hj).2 t v
  simpa only [histogram27] using h

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private theorem label_complementary27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (t : Fin s) (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    j.val ⟨t,(i,1)⟩ = complement p t (j.val ⟨t,(i,0)⟩) := by
  exact j.property.2 t i

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private def labelParentPerm27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) : Equiv.Perm (Fin (StageCandidateRaw.stageParentCount b m p d r t)) :=
  histogramEquiv27 (fun i => j.val ⟨t,(i,0)⟩) (fun i => k.val ⟨t,(i,0)⟩)
    (fun v => (target_histogram27 q m p d r j hj t v).trans
      (target_histogram27 q m p d r k hk t v).symm)

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private theorem labelParentPerm_spec27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    k.val ⟨t,(labelParentPerm27 q m p d r j k hj hk t i,0)⟩ = j.val ⟨t,(i,0)⟩ := by
  exact histogramEquiv27_spec
    (fun a : Fin (StageCandidateRaw.stageParentCount b m p d r t) => j.val ⟨t,(a,0)⟩)
    (fun a : Fin (StageCandidateRaw.stageParentCount b m p d r t) => k.val ⟨t,(a,0)⟩)
    (fun v => (target_histogram27 q m p d r j hj t v).trans
      (target_histogram27 q m p d r k hk t v).symm) i

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private def labelPosEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) :
    StageCandidateRaw.StagePos b m p d r ≃ StageCandidateRaw.StagePos b m p d r :=
  Equiv.sigmaCongrRight fun t =>
    Equiv.prodCongr (labelParentPerm27 q m p d r j k hj hk t) (Equiv.refl (Fin 2))

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private theorem labelPosEquiv_spec27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target)
    (z : StageCandidateRaw.StagePos b m p d r) :
    k.val (labelPosEquiv27 q m p d r j k hj hk z) = j.val z := by
  rcases z with ⟨t,i,h⟩
  fin_cases h
  · exact labelParentPerm_spec27 q m p d r j k hj hk t i
  · change k.val ⟨t,(labelParentPerm27 q m p d r j k hj hk t i,1)⟩ =
      j.val ⟨t,(i,1)⟩
    rw [label_complementary27 q m p d r k t,
      label_complementary27 q m p d r j t,
      labelParentPerm_spec27 q m p d r j k hj hk t i]

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private def labelWordEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) :
    StagePhysicalWord q p d b m r ≃ StagePhysicalWord q p d b m r :=
  preComp (labelPosEquiv27 q m p d r j k hj hk).symm

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private def labelPartEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    (stagePopulationAt q p d b m r).Part W ≃
      (stagePopulationAt q p d b m r).Part W :=
  preComp (labelPosEquiv27 q m p d r j k hj hk).symm

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
private theorem labelPartEquiv_exact27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side)
    (a : (stagePopulationAt q p d b m r).Part W) :
    a ∈ exactPartsAt q b m p d r j W ↔
      labelPartEquiv27 q m p d r j k hj hk W a ∈ exactPartsAt q b m p d r k W := by
  rw [stageExact_iff_partition27 q b m p d r j W,
    stageExact_iff_partition27 q b m p d r k W]
  exact partitionExact_relabel27
    (stageColour27 q b m p d r j) (stageColour27 q b m p d r k)
    (fun _ u => u.val) (stageCounts27 m p d r)
    (fun t => Equiv.prodCongr (labelParentPerm27 q m p d r j k hj hk t)
      (Equiv.refl (Fin 2)))
    (fun t i => labelPosEquiv_spec27 q m p d r j k hj hk ⟨t,i⟩) W a

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
def labelExactPartEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    StageExactPart27 q b m p d r j W ≃ StageExactPart27 q b m p d r k W :=
  Equiv.subtypeEquiv (labelPartEquiv27 q m p d r j k hj hk W)
    (labelPartEquiv_exact27 q m p d r j k hj hk W)

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
def labelExactLegEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    StageExactLeg27 q b m p d r j W ≃ StageExactLeg27 q b m p d r k W :=
  Equiv.subtypeEquiv (labelWordEquiv27 q m p d r j k hj hk)
    (fun x => labelPartEquiv_exact27 q m p d r j k hj hk W
      (stagePhysicalPart q p d b m r W x))

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
theorem labelExactPart_comm27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side)
    (x : StageExactLeg27 q b m p d r j W) :
    labelExactPartEquiv27 q m p d r j k hj hk W (stageExactPart27 q b m p d r j W x) =
      stageExactPart27 q b m p d r k W
        (labelExactLegEquiv27 q m p d r j k hj hk W x) := by
  rfl

set_option maxHeartbeats 1000000 in
-- Dependent stage labels repeatedly unfold the finite raw-population carrier during elaboration.
theorem labelExactTensor_equiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target)
    (x : StageExactLeg27 q b m p d r j .X)
    (y : StageExactLeg27 q b m p d r j .Y)
    (z : StageExactLeg27 q b m p d r j .Z) :
    stageExactTensorZ27 q b m p d r k
        (labelExactLegEquiv27 q m p d r j k hj hk .X x)
        (labelExactLegEquiv27 q m p d r j k hj hk .Y y)
        (labelExactLegEquiv27 q m p d r j k hj hk .Z z) =
      stageExactTensorZ27 q b m p d r j x y z := by
  let e := labelPosEquiv27 q m p d r j k hj hk
  let f := fun pos : StageCandidateRaw.StagePos b m p d r =>
    conZ q w (coord .X (j.val pos).val) (coord .Y (j.val pos).val)
      (coord .Z (j.val pos).val) (x.val pos) (y.val pos) (z.val pos)
  change (∏ pos, conZ q w (coord .X (k.val pos).val) (coord .Y (k.val pos).val)
      (coord .Z (k.val pos).val) (x.val (e.symm pos)) (y.val (e.symm pos))
        (z.val (e.symm pos))) = ∏ pos, f pos
  calc
    _ = ∏ pos, f (e.symm pos) := by
      apply Finset.prod_congr rfl
      intro pos _
      have hs := labelPosEquiv_spec27 q m p d r j k hj hk (e.symm pos)
      have hcoord (W : Side) : coord W (k.val pos).val =
          coord W (j.val (e.symm pos)).val := by
        have hpos := congrArg (fun a => coord W (k.val a).val) (e.apply_symm_apply pos)
        have hshape := congrArg (fun u => coord W u.val) hs
        exact hpos.symm.trans hshape
      rw [hcoord .X, hcoord .Y, hcoord .Z]
    _ = ∏ pos, f pos := Equiv.prod_comp e.symm f

end
end OmegaBound.ADVXXZGeneral
end
