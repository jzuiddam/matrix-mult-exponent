import OmegaBound.ADVXXZGeneralPCompEntropy
import Mathlib.Algebra.Order.Chebyshev

/- Contract definitions: the `Prop` definitions below are statements, not proofs. -/
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral.Parent25
noncomputable section

-- Shared by constituent (parent, boundary/residual) keys and global cell keys.
def PartitionProductCardinality : Prop :=
  ∀ {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ),
    Nat.card {x : ι → α // ∀ c a,
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card = k c a} =
    ∏ c, Nat.card {x : Fin (Nat.card {i : ι // g i = c}) → α //
      ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k c a}

def alphaCount {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b*m*p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

def parentCount {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (t : Fin s) : ℕ := ∑ u, alphaCount p d b m r t u

abbrev Pos {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) :=
  (t : Fin s) × (Fin (parentCount p d b m r t) × Fin 2)

abbrev Pop {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) := stagePopulationAt 0 p d b m r

def side {w s : ℕ} {p : ConstituentInput w s} (d : ConstituentSpec p)
    (r : Fin 6) (W : Fin 2) := d.perm r (if W = 0 then .Y else .Z)

def coordFin {w : ℕ} (W : Side) (u : Shape w) : Fin (2*w+1) :=
  match W with | .X => u.val.1 | .Y => u.val.2.1 | .Z => u.val.2.2

def grade {w : ℕ} (σ : Chunk w) : Fin (2*w+1) :=
  ⟨chunkLvl σ, by
    have h : chunkLvl σ ≤ ∑ _i : Fin w, 2 :=
      Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (σ i).isLt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega⟩

def paired {w s : ℕ} {p : ConstituentInput w s} {d : ConstituentSpec p}
    {b m : ℕ} {r : Fin 6} (a : Pos p d b m r → Chunk w) (t : Fin s)
    (i : Fin (parentCount p d b m r t)) : Chunk (w+w) :=
  fun c => if hc : c.val < w then a ⟨t, i, 0⟩ ⟨c.val, hc⟩
    else a ⟨t, i, 1⟩ ⟨c.val-w, by omega⟩

def contains {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2) (j : (Pop p d b m r).Label)
    (a : (Pop p d b m r).Part (side d r W)) : Prop :=
  ∀ z, chunkLvl (a z) = coord (side d r W) (j.val z).val

def empirical {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2)
    (a : (Pop p d b m r).Part (side d r W)) (t : Fin s) (σ : Chunk (w+w)) : ℚ :=
  (OmegaBound.ADVXXZ.typeCnt (fun i => paired a t i) σ : ℚ) / parentCount p d b m r t

def betaCount {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (t : Fin s) (σ : Chunk (w+w)) : ℕ :=
  (β.val t σ * parentCount p d b m r t).floor.toNat

def cellCount {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2) (j : (Pop p d b m r).Label)
    (a : (Pop p d b m r).Part (side d r W)) (t : Fin s)
    (cell : Shape w → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun z => z.1 = t ∧ cell (j.val z).val ∧ a z = σ).card

def childCount {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (r : Fin 6) (W : Fin 2) (t : Fin s) (u : ChildShape p t)
    (σ : Chunk w) : ℕ :=
  ((m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild (side d r W) t r u).prob σ).floor.toNat

def boundary {w s : ℕ} {p : ConstituentInput w s} (d : ConstituentSpec p)
    (r : Fin 6) (W : Fin 2) (u : Shape w) : Prop :=
  if W = 0 then coord (d.perm r .Z) u = 0
    else coord (d.perm r .X) u = 0 ∨ coord (d.perm r .Y) u = 0

def compatible {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2) (j : (Pop p d b m r).Label)
    (a : (Pop p d b m r).Part (side d r W)) : Prop :=
  (∀ t (u : ChildShape p t), boundary d r W u.val → ∀ σ,
    cellCount p d b m r W j a t (fun v => v = u.val) σ = childCount p d m r W t u σ) ∧
  ∀ t (k : Fin (2*w+1)) σ,
    cellCount p d b m r W j a t (fun u => coord (side d r W) u = k.val) σ =
      ∑ u : ChildShape p t, if coord (side d r W) u.val = k.val
        then childCount p d m r W t u σ else 0

def containsSide {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Side) (j : (Pop p d b m r).Label)
    (a : (Pop p d b m r).Part W) : Prop :=
  ∀ z, chunkLvl (a z) = coord W (j.val z).val

def inputPartKeep {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (ε : ℚ) (r : Fin 6) (W : Side) (a : (Pop p d b m r).Part W) : Prop :=
  ∀ t : Fin s, parentCount p d b m r t = 0 ∨
    (ApproxConsistent ε (d.betaRegion W t r) (fun i => paired a t i) ∧
     (∀ i, (d.betaRegion W t r).num (paired a t i) ≠ 0) ∧
     ∀ i, chunkLvl (paired a t i) =
       match W with | .X => p.i t | .Y => p.j t | .Z => p.k t)

def compatibleAtSide {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Side) (j : (Pop p d b m r).Label)
    (a : (Pop p d b m r).Part W) : Prop :=
  if W = side d r 0 then compatible p d b m r 0 j a
  else if W = side d r 1 then compatible p d b m r 1 j a else True

def compatibleLabels {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Side) (a : (Pop p d b m r).Part W) :
    Finset (AlphaLabel p d b m r) := by
  classical
  exact Finset.univ.filter fun j =>
    containsSide p d b m r W j.val a ∧ compatibleAtSide p d b m r W j.val a

def compatibleDegree {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) {r : Fin 6} (J : AlphaLabel p d b m r) (W : Side)
    (x : RepresentedParts p d b m J W) : ℕ :=
  (compatibleLabels p d b m r W x.val).card

abbrev Cell {w s : ℕ} (p : ConstituentInput w s) (t : Fin s) :=
  ChildShape p t ⊕ Fin (2*w+1)

def key {w s : ℕ} {p : ConstituentInput w s} (d : ConstituentSpec p)
    (r : Fin 6) (W : Fin 2) {t : Fin s} (u : ChildShape p t) : Cell p t := by
  classical
  exact if boundary d r W u.val then .inl u else .inr (coordFin (side d r W) u.val)

abbrev CellPos {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2) (j : (Pop p d b m r).Label)
    (t : Fin s) (c : Cell p t) :=
  {ih : Fin (parentCount p d b m r t) × Fin 2 // key d r W (j.val ⟨t,ih⟩) = c}

def cellHistogram {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (r : Fin 6) (W : Fin 2) (t : Fin s) (c : Cell p t) (σ : Chunk w) : ℕ := by
  classical
  exact ∑ u : ChildShape p t, if key d r W u = c then childCount p d m r W t u σ else 0

def PFiber {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (j : (Pop p d b m r).Label) :=
  {a : (Pop p d b m r).Part (side d r W) //
    contains p d b m r W j a ∧ empirical p d b m r W a = β.val}

def QFiber {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b m : ℕ) (r : Fin 6) (W : Fin 2) (j : (Pop p d b m r).Label) :=
  {a : (Pop p d b m r).Part (side d r W) //
    contains p d b m r W j a ∧ compatible p d b m r W j a}

-- The raw P-word fibre is a PRODUCT of projection fibres, with the correct projected type.
def PProjectionBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∀ ε m r W (β : RepresentedLaw p d b ε m r W) (j : AlphaLabel p d b m r),
      Nonempty (PFiber p d b ε m r W β j.val ≃
        ((t : Fin s) → ProjectionFiber (parentCount p d b m r t)
          (fun σ : Chunk (w+w) => grade (leftHalf σ)) (betaCount p d b ε m r W β t)
          (fun i => coordFin (side d r W) (j.val.val ⟨t,i,0⟩).val))) ∧
      ∀ t c, OmegaBound.ADVXXZ.typeCnt
        (fun i => coordFin (side d r W) (j.val.val ⟨t,i,0⟩).val) c =
          projectedCount (fun σ : Chunk (w+w) => grade (leftHalf σ))
            (betaCount p d b ε m r W β t) c

-- Disjoint boundary cells + residual marginal cells, with the parent retained.
def PartitionBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∀ m r W (j : AlphaLabel p d b m r)
      (a : (Pop p d b m r).Part (side d r W)),
      compatible p d b m r W j.val a ↔
        ∀ t c σ,
          (Finset.univ.filter fun ih : Fin (parentCount p d b m r t) × Fin 2 =>
            key d r W (j.val.val ⟨t,ih⟩) = c ∧ a ⟨t,ih⟩ = σ).card =
              cellHistogram p d m r W t c σ

-- The unrestricted corrected Q fibre is an exact product of type classes.
def QTypeClassBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∀ m r W (j : AlphaLabel p d b m r),
      Nonempty (QFiber p d b m r W j.val ≃
        ((t : Fin s) → (c : Cell p t) →
          {x : Fin (Nat.card (CellPos p d b m r W j.val t c)) → Chunk w //
            ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = cellHistogram p d m r W t c σ})) ∧
      ∀ t c, (∑ σ, cellHistogram p d m r W t c σ) =
        Nat.card (CellPos p d b m r W j.val t c)

def qRate {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (W : Fin 2) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
    (if W = 0 then constituentEta d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
     else constituentLambda d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z))

def pRate {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
    (entropy (fun σ => (β.val t σ : ℝ)) - entropy (constituentMarginal d.toPaper t r (side d r W)))

-- Exact entropy identification. No independence of the two halves is assumed in P.
def ExponentBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∀ ε m r W (β : RepresentedLaw p d b ε m r W) (j : AlphaLabel p d b m r),
      (∑ t, ∑ c : Cell p t,
        let n := Nat.card (CellPos p d b m r W j.val t c)
        (n : ℝ) * entropyNats (fun σ => (cellHistogram p d m r W t c σ : ℝ) / n)) =
          qRate p d r W * (b*m : ℕ) ∧
      (∑ t, let n := parentCount p d b m r t
        (n : ℝ) * (entropyNats (fun σ => (betaCount p d b ε m r W β t σ : ℝ) / n) -
          entropyNats (fun c => (projectedCount (fun σ : Chunk (w+w) => grade (leftHalf σ))
            (betaCount p d b ε m r W β t) c : ℝ) / n))) =
          pRate p d b ε m r W β * (b*m : ℕ)

def jointP {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) : ℝ :=
  (Nat.card {z : AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W) //
    contains p d b m r W z.1.val z.2 ∧ empirical p d b m r W z.2 = β.val} : ℝ) /
    Nat.card (AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W))

-- Corrected joint Q uses the same P samples and represented-law tuple.
def jointQ {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) : ℝ :=
  (Nat.card {z : AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W) //
    contains p d b m r W z.1.val z.2 ∧ empirical p d b m r W z.2 = β.val ∧
      compatible p d b m r W z.1.val z.2} : ℝ) /
    Nat.card (AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W))

-- Independent representative fraction; never defined by the desired Q/P identity.
def pcomp {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) : ℝ := by
  classical
  let Ω := AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W)
  letI : Fintype Ω := Fintype.ofFinite Ω
  let samples := (Finset.univ : Finset Ω).filter fun z =>
    contains p d b m r W z.1.val z.2 ∧ empirical p d b m r W z.2 = β.val
  exact if hs : samples.Nonempty then
    let e := Fintype.equivFin Ω
    let codes := samples.image e
    let hcodes : codes.Nonempty := hs.image e
    let a := (e.symm (codes.min' hcodes)).2
    let labels := (Finset.univ : Finset (AlphaLabel p d b m r)).filter fun j =>
      contains p d b m r W j.val a
    let good := labels.filter fun j => compatible p d b m r W j.val a
    (good.card : ℝ) / labels.card
  else 0

def pcompMax {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2) : ℝ := by
  classical
  let values := (Finset.univ : Finset (RepresentedLaw p d b ε m r W)).image
    (pcomp p d b ε m r W)
  exact if h : values.Nonempty then values.max' h else 0

-- A public endpoint, carrying the ambient normalization explicitly.
def FiniteBoundsBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∀ ε m r W (β : RepresentedLaw p d b ε m r W),
      let N := (Nat.card (AlphaLabel p d b m r) : ℝ)
      let ambient := (Nat.card (AlphaLabel p d b m r × (Pop p d b m r).Part (side d r W)) : ℝ)
      let poly := ∏ t, ((parentCount p d b m r t : ℝ) + 1) ^ Fintype.card (Chunk (w+w))
      let coarsePoly := ∏ t, ((parentCount p d b m r t : ℝ) + 1) ^ Fintype.card (Fin (2*w+1))
      ambient * jointP p d b ε m r W β =
        ∑ j : AlphaLabel p d b m r, (Nat.card (PFiber p d b ε m r W β j.val) : ℝ) ∧
      ambient * jointQ p d b ε m r W β =
        ∑ j : AlphaLabel p d b m r,
          (Nat.card {a : PFiber p d b ε m r W β j.val //
            compatible p d b m r W j.val a.val} : ℝ) ∧
      N * Real.exp (pRate p d b ε m r W β * (b*m : ℕ)) / poly ≤
        ambient * jointP p d b ε m r W β ∧
      ambient * jointP p d b ε m r W β ≤
        N * Real.exp (pRate p d b ε m r W β * (b*m : ℕ)) * coarsePoly ∧
      ambient * jointQ p d b ε m r W β ≤ N * Real.exp (qRate p d r W * (b*m : ℕ))

-- Exact rate subtraction + the uniform occupied-parent entropy continuity debit.
def RateContinuityBridge : Prop :=
  ∀ {w s b : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → StepIntegralAt p d b →
    ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
      ∀ ε, 0 < ε → ∀ m, 0 < m → ∀ r W (β : RepresentedLaw p d b ε m r W),
        qRate p d r W - pRate p d b ε m r W β ≤ demandCompatRate p d r W + delta ε

def RawPIdentification : Prop :=
  ∀ {w s : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p)
    (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W),
    jointP p d b ε m r W β = OmegaBound.ADVXXZGeneral.jointP p d b ε m r W β

end
end OmegaBound.ADVXXZGeneral.Parent25
