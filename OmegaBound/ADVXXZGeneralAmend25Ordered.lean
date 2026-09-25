import OmegaBound.ADVXXZGeneralAmend25Stage
import OmegaBound.ADVXXZGeneralRepair
set_option autoImplicit false
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
namespace StageCandidateRaw

def stageAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

def stageParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, stageAlphaCount b m p d r t u

abbrev StagePos {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (stageParentCount b m p d r t) × Fin 2)

noncomputable def stageWord {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    StagePos b m p d r → Chunk w := by
  classical
  dsimp [stagePopulationAt, StagePos, stageParentCount, stageAlphaCount] at a ⊢
  exact a

def pairedChunk {w s : ℕ} {b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (a : StagePos b m p d r → Chunk w) (t : Fin s)
    (i : Fin (stageParentCount b m p d r t)) : Chunk (w + w) :=
  fun c => if hc : c.val < w then
    a ⟨t, (i, ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
  else
    a ⟨t, (i, ⟨1, by omega⟩)⟩ ⟨c.val - w, by omega⟩

def sideGrade {w s : ℕ} (p : ConstituentInput w s)
    (W : Side) (t : Fin s) : ℕ :=
  match W with
  | .X => p.i t
  | .Y => p.j t
  | .Z => p.k t

noncomputable def inputPartKeep {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  let x := stageWord q b m p d r W a
  ∀ t : Fin s,
    stageParentCount b m p d r t = 0 ∨
      (ApproxConsistent ε (d.betaRegion W t r)
          (fun i => pairedChunk x t i) ∧
       (∀ i, (d.betaRegion W t r).num (pairedChunk x t i) ≠ 0) ∧
       ∀ i, chunkLvl (pairedChunk x t i) = sideGrade p W t)

end StageCandidateRaw

noncomputable def stageCandidateCoarseContains {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side)
    (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop :=
  ∀ z, chunkLvl (a z) = coord W (j.val z).val

noncomputable def stageCandidateCellCount {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side)
    (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) (t : Fin s)
    (cell : Shape w → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun z => z.1 = t ∧ cell (j.val z).val ∧ a z = σ).card

noncomputable def stageCandidateCompatible {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6)
    (which : Fin 2) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part
      (d.perm r (if which = 0 then .Y else .Z))) : Prop :=
  let X := d.perm r .X
  let Y := d.perm r .Y
  let Z := d.perm r .Z
  let W := if which = 0 then Y else Z
  let count := fun t (u : ChildShape p t) σ =>
    ((m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ).floor.toNat
  (∀ t (u : ChildShape p t),
    (if which = 0 then coord Z u.val = 0 else coord X u.val = 0 ∨ coord Y u.val = 0) →
      ∀ σ, stageCandidateCellCount q p d b m r W j a t (fun v => v = u.val) σ = count t u σ) ∧
  ∀ t (k : Fin (2*w+1)) σ,
    stageCandidateCellCount q p d b m r W j a t (fun u => coord W u = k.val) σ =
      ∑ u : ChildShape p t, if coord W u.val = k.val then count t u σ else 0

noncomputable def StageExactPreimageAt {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label) (W : Side) :=
  (a : {a : (stagePopulationAt q p d b m r).Part W //
    (stagePopulationAt q p d b m r).incidence W j a}) ×
    {x : (regionalInputZ q p d (b*m) ε).leg W // stagePartAt q b m ε p d r W x = a.val}

noncomputable def candidateWord {w s M : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M) (W : Side)
    (x : (regionalInputZ q p d (b*m) ε).leg W) : Prop :=
  let P := stagePopulationAt q p d b m r
  let S := selected (rolePopulation P (d.perm r)) M B ω
  let a := stagePartAt q b m ε p d r W x
  StageCandidateRaw.inputPartKeep q b m ε p d r W a ∧
  ∃ (j : P.Label) (pre : StageExactPreimageAt q p d b ε m r j W),
    j ∈ S ∧ pre.2.val = x ∧
    (∀ h : W = d.perm r .Y, ∀ k ∈ S,
      stageCandidateCoarseContains q p d b m r W k a →
      stageCandidateCompatible q p d b m r 0 k (h ▸ a) → k = j) ∧
    (∀ h : W = d.perm r .Z, ∀ k ∈ S,
      stageCandidateCoarseContains q p d b m r W k a →
      stageCandidateCompatible q p d b m r 1 k (h ▸ a) → k = j)

noncomputable def StagePhysicalWord {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :=
  StageCandidateRaw.StagePos b m p d r → Fin w → CW90.Idx7 q

noncomputable instance stagePhysicalWordFintype {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    Fintype (StagePhysicalWord q p d b m r) := by
  unfold StagePhysicalWord StageCandidateRaw.StagePos
  infer_instance

noncomputable def stagePhysicalPart {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side)
    (x : StagePhysicalWord q p d b m r) : (stagePopulationAt q p d b m r).Part W :=
  fun z => chunkOf (x z)

noncomputable def stageBrokenCopyZ25 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) : ITensor := by
  classical
  let P := stagePopulationAt q p d b m r
  let L := fun W => {x : StagePhysicalWord q p d b m r //
    P.incidence W j (stagePhysicalPart q p d b m r W x) ∧
      stagePhysicalPart q p d b m r W x ∉ holesAt25 q b m M ε p d r B ω j W}
  exact
    { X := L .X
      Y := L .Y
      Z := L .Z
      tensor := fun x y z => ∏ pos : StageCandidateRaw.StagePos b m p d r,
        conZ q w (coord .X (j.val pos).val) (coord .Y (j.val pos).val)
          (coord .Z (j.val pos).val) (x.val pos) (y.val pos) (z.val pos) }

noncomputable def goodBrokenFamilyZ25 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label) : ITensor := by
  classical
  exact if ValidStageHashes p d b m M B then
    regionProductZ fun r =>
      if (stagePopulationAt q p d b m r).n = 0 then unitFamilyZ else
        dependentSumZ fun j : {j // j ∈ J r} =>
          stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val
  else emptyFamilyZ

noncomputable def brokenFamilyTensorZ25 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r)) : ITensor :=
  goodBrokenFamilyZ25 q p d b ε m M B ω fun r =>
    selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) (M r) (B r) (ω r)

noncomputable def stageRepairedCount {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (_ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (_B : (r : Fin 6) → Finset (ZMod (M r)))
    (_ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label) : ℕ := by
  classical
  exact ∏ r : Fin 6,
    let P := stagePopulationAt q p d b m r
    if P.n = 0 then 1 else
      (J r).card / repairReserve P.n
        (fun W => (J r).sup (fun j => (exactPartsAt q b m p d r j W).card))

noncomputable def GlobalPhysicalWord {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) :=
  Fin (globalPopulation g n ξ r).n → Fin w → CW90.Idx7 q

noncomputable instance globalPhysicalWordFintype {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n) (r : Fin 6) :
    Fintype (GlobalPhysicalWord q g n ξ r) := by
  unfold GlobalPhysicalWord
  infer_instance

noncomputable def globalPhysicalPart {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Side)
    (x : GlobalPhysicalWord q g n ξ r) : (globalPopulation g n ξ r).Part W :=
  fun i => chunkOf (x i)

noncomputable def globalRegionWord {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Side) (x : (topZ q w n).leg W) :
    GlobalPhysicalWord q g n ξ r := by
  let offset := ∑ t : Fin 6, if t.val < r.val then (globalPopulation g n ξ t).n else 0
  have x' : Fin n → Fin w → CW90.Idx7 q := by cases W <;> exact x
  exact fun i c => if h : offset + i.val < n then x' ⟨offset + i.val, h⟩ c else Sum.inl none

noncomputable def globalPartKeep {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (globalPopulation g n ξ r) M) (step : DeletionStep) (W : Side)
    (a : (globalPopulation g n ξ r).Part W) : Prop := by
  classical
  let P := globalPopulation g n ξ r
  let S := selected (rolePopulation P (g.perm r)) M B ω
  let matching := S.filter fun j => globalCoarseContains g n ξ r W j a
  let ys := matching.filter fun j => globalCompatible g n ξ r 0 j a
  let zs := matching.filter fun j => globalCompatible g n ξ r 1 j a
  let hHash := matching.Nonempty
  let hX := W = g.perm r .X → ∃ j ∈ matching, P.incidence W j a
  let hYC := W = g.perm r .Y → ys.Nonempty
  let hYU := W = g.perm r .Y → ys.card = 1
  let hYF := W = g.perm r .Y → ∃ j ∈ ys, P.incidence W j a
  let hZC := W = g.perm r .Z → zs.Nonempty
  let hZU := W = g.perm r .Z → zs.card = 1
  let hZF := W = g.perm r .Z → ∃ j ∈ zs, P.incidence W j a
  exact match step with
  | .input => True
  | .hash => hHash
  | .xExact => hHash ∧ hX
  | .yCompat => hHash ∧ hX ∧ hYC
  | .yUnique => hHash ∧ hX ∧ hYC ∧ hYU
  | .yUseful => hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF
  | .zCompat => hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC
  | .zUnique => hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU
  | .zUseful => hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU ∧ hZF

noncomputable def globalFinalKeep {w : ℕ} (q : ℕ) (g : GlobalSpec w) (b m : ℕ)
    (ξ : ExactGrid g (b*m)) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side) (x : (topZ q w (b*m)).leg W) : Prop :=
  ∀ r, (globalPopulation g (b*m) ξ r).n = 0 ∨
    globalPartKeep g (b*m) ξ r (M r) (B r) (ω r) .zUseful W
      (globalPhysicalPart q g (b*m) ξ r W (globalRegionWord q g (b*m) ξ r W x))

noncomputable def globalCandidateWord {w : ℕ} (q : ℕ) (g : GlobalSpec w) (b m : ℕ)
    (ξ : ExactGrid g (b*m)) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side) (x : (topZ q w (b*m)).leg W) : Prop :=
  ∀ r,
    let P := globalPopulation g (b*m) ξ r
    let S := selected (rolePopulation P (g.perm r)) (M r) (B r) (ω r)
    P.n = 0 ∨ ∃ (j : P.Label) (v : GlobalPhysicalWord q g (b*m) ξ r),
      j ∈ S ∧ v = globalRegionWord q g (b*m) ξ r W x ∧
      P.incidence W j (globalPhysicalPart q g (b*m) ξ r W v) ∧
      (W = g.perm r .Y → ∀ k ∈ S,
        globalCoarseContains g (b*m) ξ r W k (globalPhysicalPart q g (b*m) ξ r W v) →
        globalCompatible g (b*m) ξ r 0 k (globalPhysicalPart q g (b*m) ξ r W v) → k = j) ∧
      (W = g.perm r .Z → ∀ k ∈ S,
        globalCoarseContains g (b*m) ξ r W k (globalPhysicalPart q g (b*m) ξ r W v) →
        globalCompatible g (b*m) ξ r 1 k (globalPhysicalPart q g (b*m) ξ r W v) → k = j)

noncomputable def globalBrokenCopyZ {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (globalPopulation g n ξ r) M)
    (j : (globalPopulation g n ξ r).Label) : ITensor := by
  classical
  let P := globalPopulation g n ξ r
  let L := fun W => {x : GlobalPhysicalWord q g n ξ r //
    P.incidence W j (globalPhysicalPart q g n ξ r W x) ∧
      globalPartKeep g n ξ r M B ω .zUseful W (globalPhysicalPart q g n ξ r W x)}
  exact
    { X := L .X
      Y := L .Y
      Z := L .Z
      tensor := fun x y z => ∏ i : Fin P.n,
        conZ q w (coord .X (j.val i)) (coord .Y (j.val i)) (coord .Z (j.val i))
          (x.val i) (y.val i) (z.val i) }

noncomputable def globalBrokenFamilyZ {w : ℕ} (q : ℕ) (g : GlobalSpec w) (b m : ℕ)
    (ξ : ExactGrid g (b*m)) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r)) : ITensor := by
  classical
  exact if ValidGlobalHashes g (b*m) ξ M B then
    regionProductZ fun r =>
      if (globalPopulation g (b*m) ξ r).n = 0 then unitFamilyZ else
        dependentSumZ fun j : {j //
          j ∈ selected (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
            (M r) (B r) (ω r)} =>
          globalBrokenCopyZ q g (b*m) ξ r (M r) (B r) (ω r) j.val
  else emptyFamilyZ

end
end OmegaBound.ADVXXZGeneral

