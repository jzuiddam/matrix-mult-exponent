import OmegaBound.ADVXXZGeneralPopulationConstructorsV22
import OmegaBound.ADVXXZGeneralCertScaleV22

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def outcomeZero {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨0, by omega⟩

private def outcomeOne {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨1, by omega⟩

private def outcomeWeight {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  ω ⟨i.val + 2, by omega⟩

private def hashX (P : RawPopulation) (M : ℕ) (ω : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  outcomeZero ω + ∑ i, (P.coarse j .X i).val * outcomeWeight ω i

private def hashY (P : RawPopulation) (M : ℕ) (ω : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  outcomeZero ω + outcomeOne ω +
    ∑ i, (P.coarse j .Y i).val * outcomeWeight ω i

private noncomputable def hashZ (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  outcomeZero ω + Ring.inverse 2 *
    (outcomeOne ω +
      ∑ i, (P.grade - (P.coarse j .Z i).val) * outcomeWeight ω i)

noncomputable def bucket (P : RawPopulation) (M : ℕ) [NeZero M]
    (j : P.Label) (b : ZMod M) : Finset (HashOutcome P M) := by
  classical
  exact Finset.univ.filter fun ω =>
    hashX P M ω j = b ∧ hashY P M ω j = b ∧ hashZ P M ω j = b

private noncomputable def survives (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun j =>
    hashX P M ω j = hashY P M ω j ∧
    hashY P M ω j = hashZ P M ω j ∧
    hashX P M ω j ∈ B

noncomputable def selected (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  let S := survives P M B ω
  exact S.filter fun j => j ∈ P.target ∧
    ∀ k ∈ S, P.coarse k .X = P.coarse j .X → k = j

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

private noncomputable abbrev stageP {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : RawPopulation :=
  stagePopulationAt 0 p d b m r

noncomputable def AlphaLabel {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : Type :=
  ↑(stageP p d b m r).target

noncomputable instance alphaLabelFintype {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    Fintype (AlphaLabel p d b m r) := by
  classical
  unfold AlphaLabel
  infer_instance

noncomputable instance alphaLabelDecidableEq {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    DecidableEq (AlphaLabel p d b m r) :=
  Classical.decEq _

noncomputable def RepresentedParts {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) {r : Fin 6}
    (J : AlphaLabel p d b m r) (W : Side) : Type := by
  classical
  let P := stageP p d b m r
  exact ↑(Finset.univ.filter (P.incidence W J.1))

noncomputable instance representedPartsFintype {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) {r : Fin 6}
    (J : AlphaLabel p d b m r) (W : Side) :
    Fintype (RepresentedParts p d b m J W) := by
  classical
  unfold RepresentedParts
  infer_instance

noncomputable instance representedPartsDecidableEq {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) {r : Fin 6}
    (J : AlphaLabel p d b m r) (W : Side) :
    DecidableEq (RepresentedParts p d b m J W) :=
  Classical.decEq _

private noncomputable def stageWord {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W) :
    StagePos b m p d r → Chunk w := by
  classical
  dsimp [stageP, stagePopulationAt, StagePos, stageParentCount, stageAlphaCount] at a ⊢
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

private noncomputable def inputCompatible {w s : ℕ} (b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W) : Prop :=
  let x := stageWord b m p d r W a
  ∀ t : Fin s,
    stageParentCount b m p d r t = 0 ∨
      (ApproxConsistent ε (d.betaRegion W t r) (fun i => pairedChunk x t i) ∧
       (∀ i, (d.betaRegion W t r).num (pairedChunk x t i) ≠ 0) ∧
       ∀ i, chunkLvl (pairedChunk x t i) = sideGrade p W t)

noncomputable def InputDensity {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) {r : Fin 6}
    (J : AlphaLabel p d b m r) (W : Side) : ℝ := by
  classical
  let P := stageP p d b m r
  let exactParts : Finset (P.Part W) := Finset.univ.filter (P.incidence W J.1)
  let badParts := exactParts.filter fun x => ¬ inputCompatible b m ε p d r W x
  exact (badParts.card : ℝ) / exactParts.card

private noncomputable def partChunk {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W)
    (i : Fin (stageP p d b m r).n) : Chunk w := by
  classical
  let code := (stageP p d b m r).fine W a i
  have hcode : code < Fintype.card (Chunk w) := by
    dsimp [code, stageP, stagePopulationAt]
    exact (Fintype.equivFin (Chunk w) _).isLt
  exact (Fintype.equivFin (Chunk w)).symm ⟨code, hcode⟩

private noncomputable def coarseContains {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stageP p d b m r).Label)
    (a : (stageP p d b m r).Part W) : Prop :=
  ∀ i, chunkLvl (partChunk b m p d r W a i) =
    ((stageP p d b m r).coarse j W i).val

private noncomputable def fineCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W)
    (cell : Fin (stageP p d b m r).n → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun i =>
    cell i ∧ partChunk b m p d r W a i = σ).card

private noncomputable def jointCell {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stageP p d b m r).Label) (X Y Z : Side)
    (gx gy gz : Fin ((stageP p d b m r).grade + 1))
    (i : Fin (stageP p d b m r).n) : Prop :=
  (stageP p d b m r).coarse j X i = gx ∧
  (stageP p d b m r).coarse j Y i = gy ∧
  (stageP p d b m r).coarse j Z i = gz

private noncomputable def marginalCell {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stageP p d b m r).Label) (S : Side)
    (g : Fin ((stageP p d b m r).grade + 1))
    (i : Fin (stageP p d b m r).n) : Prop :=
  (stageP p d b m r).coarse j S i = g

private noncomputable def compatibleY {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stageP p d b m r).Label)
    (a : (stageP p d b m r).Part W) : Prop := by
  classical
  let P := stageP p d b m r
  let sideX := d.perm r .X
  let sideY := d.perm r .Y
  let sideZ := d.perm r .Z
  exact ∃ a₀ : P.Part W, P.incidence W j a₀ ∧
    (∀ gx gy gz σ, gz.val = 0 →
      fineCount b m p d r W a (jointCell b m p d r j sideX sideY sideZ gx gy gz) σ =
      fineCount b m p d r W a₀ (jointCell b m p d r j sideX sideY sideZ gx gy gz) σ) ∧
    ∀ gy σ,
      fineCount b m p d r W a (marginalCell b m p d r j sideY gy) σ =
      fineCount b m p d r W a₀ (marginalCell b m p d r j sideY gy) σ

private noncomputable def compatibleZ {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stageP p d b m r).Label)
    (a : (stageP p d b m r).Part W) : Prop := by
  classical
  let P := stageP p d b m r
  let sideX := d.perm r .X
  let sideY := d.perm r .Y
  let sideZ := d.perm r .Z
  exact ∃ a₀ : P.Part W, P.incidence W j a₀ ∧
    (∀ gx gy gz σ, (gx.val = 0 ∨ gy.val = 0) →
      fineCount b m p d r W a (jointCell b m p d r j sideX sideY sideZ gx gy gz) σ =
      fineCount b m p d r W a₀ (jointCell b m p d r j sideX sideY sideZ gx gy gz) σ) ∧
    ∀ gz σ,
      fineCount b m p d r W a (marginalCell b m p d r j sideZ gz) σ =
      fineCount b m p d r W a₀ (marginalCell b m p d r j sideZ gz) σ

private noncomputable def compatibleAtSide {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stageP p d b m r).Label)
    (a : (stageP p d b m r).Part W) : Prop :=
  if W = d.perm r .Y then compatibleY b m p d r W j a
  else if W = d.perm r .Z then compatibleZ b m p d r W j a
  else True

private noncomputable def compatibleLabels {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W) :
    Finset (AlphaLabel p d b m r) := by
  classical
  exact Finset.univ.filter fun K =>
    coarseContains b m p d r W K.1 a ∧ compatibleAtSide b m p d r W K.1 a

noncomputable def compatibleDegree {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) {r : Fin 6}
    (J : AlphaLabel p d b m r) (W : Side)
    (x : RepresentedParts p d b m J W) : ℕ :=
  (compatibleLabels b m p d r W x.1).card

private def representedSide {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (which : Fin 2) : Side :=
  if which = 0 then d.perm r .Y else d.perm r .Z

private abbrev EmpiricalLaw (w s : ℕ) :=
  Fin s → Chunk (w + w) → ℚ

private noncomputable def empiricalLaw {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stageP p d b m r).Part W) : EmpiricalLaw w s :=
  let x := stageWord b m p d r W a
  fun t σ =>
    ((OmegaBound.ADVXXZ.typeCnt (fun i => pairedChunk x t i) σ : ℕ) : ℚ) /
      stageParentCount b m p d r t

private def lawTypical {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side) (ε : ℚ)
    (β : EmpiricalLaw w s) : Prop :=
  ∀ t, 0 < stageParentCount b m p d r t →
    ∀ σ, |β t σ - (d.betaRegion W t r).prob σ| ≤ ε

private abbrev LawSample {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side) :=
  AlphaLabel p d b m r × (stageP p d b m r).Part W

private noncomputable def containingSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (r : Fin 6) (W : Side) : Finset (LawSample p d b m r W) := by
  classical
  exact Finset.univ.filter fun z => coarseContains b m p d r W z.1.1 z.2

private noncomputable def representedLawFinset {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2) : Finset (EmpiricalLaw w s) := by
  classical
  let W := representedSide d r which
  exact ((containingSamples p d b m r W).image fun z =>
    empiricalLaw b m p d r W z.2).filter (lawTypical d b m r W ε)

noncomputable def RepresentedLaw {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (which : Fin 2) : Type :=
  ↑(representedLawFinset p d b ε m r which)

noncomputable instance representedLawFintype {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) : Fintype (RepresentedLaw p d b ε m r which) := by
  classical
  unfold RepresentedLaw
  infer_instance

noncomputable instance representedLawDecidableEq {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) : DecidableEq (RepresentedLaw p d b ε m r which) :=
  Classical.decEq _

private noncomputable def lawSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    Finset (LawSample p d b m r (representedSide d r which)) := by
  classical
  let W := representedSide d r which
  exact (containingSamples p d b m r W).filter fun z =>
    empiricalLaw b m p d r W z.2 = β.1

private noncomputable def compatibleForWhich {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : (stageP p d b m r).Label)
    (a : (stageP p d b m r).Part (representedSide d r which)) : Prop :=
  if which = 0 then
    compatibleY b m p d r (representedSide d r which) j a
  else
    compatibleZ b m p d r (representedSide d r which) j a

noncomputable def jointP {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) : ℝ := by
  classical
  let W := representedSide d r which
  let Ω := LawSample p d b m r W
  exact ((lawSamples p d b ε m r which β).card : ℝ) / (Fintype.card Ω : ℝ)

noncomputable def jointQ {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) : ℝ := by
  classical
  let samples := (lawSamples p d b ε m r which β).filter fun z =>
    compatibleForWhich b m p d r which z.1.1 z.2
  let W := representedSide d r which
  let Ω := LawSample p d b m r W
  exact (samples.card : ℝ) / (Fintype.card Ω : ℝ)

private noncomputable def firstLawSample {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    LawSample p d b m r (representedSide d r which) := by
  classical
  let candidates := lawSamples p d b ε m r which β
  have hcandidates : candidates.Nonempty := by
    have hmem : β.1 ∈ representedLawFinset p d b ε m r which := β.2
    have himage := (Finset.mem_filter.mp hmem).1
    rcases Finset.mem_image.mp himage with ⟨z, hz, hzeq⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzeq⟩⟩
  let e := Fintype.equivFin (LawSample p d b m r (representedSide d r which))
  letI : LinearOrder (LawSample p d b m r (representedSide d r which)) :=
    LinearOrder.lift' e e.injective
  exact candidates.min' hcandidates

private noncomputable def compatibilityRatioAtWord {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2)
    (a : (stageP p d b m r).Part (representedSide d r which)) : ℝ := by
  classical
  let incident := (Finset.univ : Finset (AlphaLabel p d b m r)).filter fun K =>
    coarseContains b m p d r (representedSide d r which) K.1 a
  let compatible := incident.filter fun K =>
    compatibleForWhich b m p d r which K.1 a
  exact (compatible.card : ℝ) / incident.card

noncomputable def pcomp {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) : ℝ :=
  compatibilityRatioAtWord b m p d r which
    (firstLawSample p d b ε m r which β).2

noncomputable def pcompMax {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) : ℝ := by
  classical
  let values := (Finset.univ : Finset (RepresentedLaw p d b ε m r which)).image
    (pcomp p d b ε m r which)
  exact if h : values.Nonempty then values.max' h else 0

end OmegaBound.ADVXXZGeneral
end
