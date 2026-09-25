import OmegaBound.ADVXXZGeneralPopulationConstructorsV22
import OmegaBound.ADVXXZGeneralStageCore
import OmegaBound.ADVXXZGeneralStageLeg
import OmegaBound.ADVXXZGeneralStageNumerical
import OmegaBound.ADVXXZGeneralTensorAux

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def stageAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def stageParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, stageAlphaCount b m p d r t u

private abbrev StagePos {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (stageParentCount b m p d r t) × Fin 2)

private noncomputable def stageWord {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    StagePos b m p d r → Chunk w := by
  classical
  dsimp [stagePopulationAt, StagePos, stageParentCount, stageAlphaCount] at a ⊢
  exact a

private def pairedChunk {w s : ℕ} {b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (a : StagePos b m p d r → Chunk w) (t : Fin s)
    (i : Fin (stageParentCount b m p d r t)) : Chunk (w + w) :=
  fun c => if hc : c.val < w then
    a ⟨t, (i, ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
  else
    a ⟨t, (i, ⟨1, by omega⟩)⟩ ⟨c.val - w, by omega⟩

private def sideGrade {w s : ℕ} (p : ConstituentInput w s)
    (W : Side) (t : Fin s) : ℕ :=
  match W with
  | .X => p.i t
  | .Y => p.j t
  | .Z => p.k t

private noncomputable def inputPartKeep {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  let x := stageWord q b m p d r W a
  ∀ t : Fin s,
    stageParentCount b m p d r t = 0 ∨
      (ApproxConsistent ε (d.betaRegion W t r)
          (fun i => pairedChunk x t i) ∧
       (∀ i, (d.betaRegion W t r).num (pairedChunk x t i) ≠ 0) ∧
       ∀ i, chunkLvl (pairedChunk x t i) = sideGrade p W t)

private def joinedCoord {w : ℕ} (h : Fin 2) (c : Fin w) : Fin (w + w) :=
  ⟨h.val * w + c.val, by
    have hh : h.val = 0 ∨ h.val = 1 := by omega
    rcases hh with hh | hh <;> simp [hh] <;> omega⟩

private abbrev StageSlot (s : ℕ) := Fin (Fintype.card (Fin s × Fin 6))

private noncomputable def regionalSlotCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (x : StageSlot s) : ℕ :=
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  (((b * m : ℕ) : ℚ) * (p.baseN (e x).1 : ℚ) *
    (d.A (e x).1).prob (e x).2).floor.toNat

private noncomputable def regionalLegValue {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (W : Side)
    (x : (regionalInputZ q p d (b*m) ε).leg W) (slot : StageSlot s)
    (i : Fin (regionalSlotCount b m p d slot)) (c : Fin (w + w)) : CW90.Idx7 q := by
  classical
  cases W with
  | X =>
      change (z : StageSlot s) → Fin (regionalSlotCount b m p d z) →
        Fin (w + w) → CW90.Idx7 q at x
      exact x slot i c
  | Y =>
      change (z : StageSlot s) → Fin (regionalSlotCount b m p d z) →
        Fin (w + w) → CW90.Idx7 q at x
      exact x slot i c
  | Z =>
      change (z : StageSlot s) → Fin (regionalSlotCount b m p d z) →
        Fin (w + w) → CW90.Idx7 q at x
      exact x slot i c

private noncomputable def physicalStageWord {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (x : (regionalInputZ q p d (b*m) ε).leg W) : StagePos b m p d r → Chunk w :=
  fun z c =>
    let slot := Fintype.equivFin (Fin s × Fin 6) (z.1, r)
    if hi : z.2.1.val < regionalSlotCount b m p d slot then
      lvl7 (regionalLegValue q b m ε p d W x slot ⟨z.2.1.val, hi⟩
        (joinedCoord z.2.2 c))
    else ⟨0, by omega⟩

noncomputable def stagePartAt {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (x : (regionalInputZ q p d (b*m) ε).leg W) :
    (stagePopulationAt q p d b m r).Part W := by
  classical
  dsimp [stagePopulationAt, StagePos, stageParentCount, stageAlphaCount]
  exact physicalStageWord q b m ε p d r W x

private def outcomeZero {P : RawPopulation} {M : ℕ} (ω : HashOutcome P M) : ZMod M :=
  ω ⟨0, by omega⟩

private def outcomeOne {P : RawPopulation} {M : ℕ} (ω : HashOutcome P M) : ZMod M :=
  ω ⟨1, by omega⟩

private def outcomeWeight {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  ω ⟨i.val + 2, by omega⟩

private def stageHashX (P : RawPopulation) (M : ℕ) (ω : HashOutcome P M)
    (j : P.Label) (X : Side) : ZMod M :=
  outcomeZero ω + ∑ i, (P.coarse j X i).val * outcomeWeight ω i

private def stageHashY (P : RawPopulation) (M : ℕ) (ω : HashOutcome P M)
    (j : P.Label) (Y : Side) : ZMod M :=
  outcomeZero ω + outcomeOne ω +
    ∑ i, (P.coarse j Y i).val * outcomeWeight ω i

private noncomputable def stageHashZ (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) (Z : Side) : ZMod M :=
  outcomeZero ω + Ring.inverse 2 *
    (outcomeOne ω + ∑ i, (P.grade - (P.coarse j Z i).val) * outcomeWeight ω i)

private noncomputable def survivingLabels (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (X Y Z : Side) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun j =>
    stageHashX P M ω j X = stageHashY P M ω j Y ∧
    stageHashY P M ω j Y = stageHashZ P M ω j Z ∧
    stageHashX P M ω j X ∈ B

private noncomputable def selectedLabels (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (X Y Z : Side) : Finset P.Label := by
  classical
  let S := survivingLabels P M B ω X Y Z
  exact S.filter fun j => j ∈ P.target ∧
    ∀ k ∈ S, (∀ i, P.coarse k X i = P.coarse j X i) → k = j

private noncomputable def partChunk {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W)
    (i : Fin (stagePopulationAt q p d b m r).n) : Chunk w := by
  classical
  let code := (stagePopulationAt q p d b m r).fine W a i
  have hcode : code < Fintype.card (Chunk w) := by
    dsimp [code, stagePopulationAt]
    exact (Fintype.equivFin (Chunk w) _).isLt
  exact (Fintype.equivFin (Chunk w)).symm ⟨code, hcode⟩

private noncomputable def coarseMatches {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  ∀ i, chunkLvl (partChunk q b m p d r W a i) =
    ((stagePopulationAt q p d b m r).coarse j W i).val

private noncomputable def fineCount {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W)
    (cell : Fin (stagePopulationAt q p d b m r).n → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => cell i ∧ partChunk q b m p d r W a i = σ).card

private noncomputable def jointCell {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (X Y Z : Side)
    (gx gy gz : Fin ((stagePopulationAt q p d b m r).grade + 1))
    (i : Fin (stagePopulationAt q p d b m r).n) : Prop :=
  (stagePopulationAt q p d b m r).coarse j X i = gx ∧
  (stagePopulationAt q p d b m r).coarse j Y i = gy ∧
  (stagePopulationAt q p d b m r).coarse j Z i = gz

private noncomputable def marginalCell {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (S : Side)
    (g : Fin ((stagePopulationAt q p d b m r).grade + 1))
    (i : Fin (stagePopulationAt q p d b m r).n) : Prop :=
  (stagePopulationAt q p d b m r).coarse j S i = g

private noncomputable def compatibleYPart {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop := by
  classical
  let P := stagePopulationAt q p d b m r
  let X := d.perm r .X
  let Y := d.perm r .Y
  let Z := d.perm r .Z
  exact ∃ a₀ : P.Part W, P.incidence W j a₀ ∧
    (∀ gx gy gz σ, gz.val = 0 →
      fineCount q b m p d r W a (jointCell q b m p d r j X Y Z gx gy gz) σ =
      fineCount q b m p d r W a₀ (jointCell q b m p d r j X Y Z gx gy gz) σ) ∧
    ∀ gy σ,
      fineCount q b m p d r W a (marginalCell q b m p d r j Y gy) σ =
      fineCount q b m p d r W a₀ (marginalCell q b m p d r j Y gy) σ

private noncomputable def compatibleZPart {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop := by
  classical
  let P := stagePopulationAt q p d b m r
  let X := d.perm r .X
  let Y := d.perm r .Y
  let Z := d.perm r .Z
  exact ∃ a₀ : P.Part W, P.incidence W j a₀ ∧
    (∀ gx gy gz σ, (gx.val = 0 ∨ gy.val = 0) →
      fineCount q b m p d r W a (jointCell q b m p d r j X Y Z gx gy gz) σ =
      fineCount q b m p d r W a₀ (jointCell q b m p d r j X Y Z gx gy gz) σ) ∧
    ∀ gz σ,
      fineCount q b m p d r W a (marginalCell q b m p d r j Z gz) σ =
      fineCount q b m p d r W a₀ (marginalCell q b m p d r j Z gz) σ

private noncomputable def matchingLabels {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    Finset (stagePopulationAt q p d b m r).Label := by
  classical
  let P := stagePopulationAt q p d b m r
  let S := selectedLabels P M B ω (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
  exact S.filter fun j => coarseMatches q b m p d r W j a

private noncomputable def compatibleYLabels {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    Finset (stagePopulationAt q p d b m r).Label := by
  classical
  exact (matchingLabels q b m M p d r B ω W a).filter fun j =>
    compatibleYPart q b m p d r W j a

private noncomputable def compatibleZLabels {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    Finset (stagePopulationAt q p d b m r).Label := by
  classical
  exact (matchingLabels q b m M p d r B ω W a).filter fun j =>
    compatibleZPart q b m p d r W j a

private noncomputable def xExactTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .X → ∃ j ∈ matchingLabels q b m M p d r B ω W a,
    (stagePopulationAt q p d b m r).incidence W j a

private noncomputable def yCompatTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Y → (compatibleYLabels q b m M p d r B ω W a).Nonempty

private noncomputable def yUniqueTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Y → (compatibleYLabels q b m M p d r B ω W a).card = 1

private noncomputable def yUsefulTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Y → ∃ j ∈ compatibleYLabels q b m M p d r B ω W a,
    (stagePopulationAt q p d b m r).incidence W j a

private noncomputable def zCompatTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Z → (compatibleZLabels q b m M p d r B ω W a).Nonempty

private noncomputable def zUniqueTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Z → (compatibleZLabels q b m M p d r B ω W a).card = 1

private noncomputable def zUsefulTest {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  W = d.perm r .Z → ∃ j ∈ compatibleZLabels q b m M p d r B ω W a,
    (stagePopulationAt q p d b m r).incidence W j a

noncomputable def stagePartKeepAt {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (step : DeletionStep) (W : Side)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  let hInput := inputPartKeep q b m ε p d r W a
  let hHash := (matchingLabels q b m M p d r B ω W a).Nonempty
  let hX := xExactTest q b m M p d r B ω W a
  let hYC := yCompatTest q b m M p d r B ω W a
  let hYU := yUniqueTest q b m M p d r B ω W a
  let hYF := yUsefulTest q b m M p d r B ω W a
  let hZC := zCompatTest q b m M p d r B ω W a
  let hZU := zUniqueTest q b m M p d r B ω W a
  let hZF := zUsefulTest q b m M p d r B ω W a
  match step with
  | .input => hInput
  | .hash => hInput ∧ hHash
  | .xExact => hInput ∧ hHash ∧ hX
  | .yCompat => hInput ∧ hHash ∧ hX ∧ hYC
  | .yUnique => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU
  | .yUseful => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF
  | .zCompat => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC
  | .zUnique => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU
  | .zUseful => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU ∧ hZF

noncomputable def stageKeepAt {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (step : DeletionStep) (W : Side) :
    (regionalInputZ q p d (b*m) ε).leg W → Prop :=
  fun x => stagePartKeepAt q b m M ε p d r B ω step W
    (stagePartAt q b m ε p d r W x)

noncomputable def exactPartsAt {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    Finset ((stagePopulationAt q p d b m r).Part W) := by
  classical
  exact Finset.univ.filter ((stagePopulationAt q p d b m r).incidence W j)

noncomputable def holesAt {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    Finset ((stagePopulationAt q p d b m r).Part W) := by
  classical
  exact (exactPartsAt q b m p d r j W).filter fun a =>
    ¬ stagePartKeepAt q b m M ε p d r B ω .zUseful W a

theorem stageKeepAt_saturation {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (step : DeletionStep) (W : Side)
    (x y : (regionalInputZ q p d (b*m) ε).leg W)
    (h : stagePartAt q b m ε p d r W x = stagePartAt q b m ε p d r W y) :
    stageKeepAt q b m M ε p d r B ω step W x ↔
      stageKeepAt q b m M ε p d r B ω step W y := by
  simp only [stageKeepAt]
  rw [h]

theorem mem_holesAt {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side)
    (a : (stagePopulationAt q p d b m r).Part W) :
    a ∈ holesAt q b m M ε p d r B ω j W ↔
      a ∈ exactPartsAt q b m p d r j W ∧
        ¬ stagePartKeepAt q b m M ε p d r B ω .zUseful W a := by
  simp [holesAt]

theorem holesAt_subset_exactPartsAt {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    holesAt q b m M ε p d r B ω j W ⊆ exactPartsAt q b m p d r j W := by
  intro a ha
  exact (mem_holesAt q b m M ε p d r B ω j W a).mp ha |>.1

end OmegaBound.ADVXXZGeneral
end
