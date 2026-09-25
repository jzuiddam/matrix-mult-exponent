import OmegaBound.ADVXXZGeneralCExact40Exponents
import OmegaBound.ADVXXZGeneralCExact40PComp

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

namespace Parent25

/-- The Parent25 finite P/Q bounds at one empirical-grid scale. -/
def FiniteBoundsBridge40 : Prop :=
  ∀ {w s b m : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
    ∀ ε r W (β : RepresentedLaw p d b ε m r W),
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

end Parent25

private noncomputable def apq_projectionWord {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (J : AlphaLabel p d b m r) (t : Fin s) :
    {y : Fin (Parent25.parentCount p d b m r t) → Fin (2 * w + 1) //
      ∀ c, OmegaBound.ADVXXZ.typeCnt y c =
        projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
          (Parent25.betaCount p d b ε m r W β t) c} :=
  ⟨fun i => Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t, i, 0⟩).val,
    parent25_projected_beta_count p d ε m r W β J t⟩

private theorem apq_pfiber_card {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    Nat.card (Parent25.PFiber p d b ε m r W β J.val) =
      ∏ t, Nat.card (ProjectionFiber (Parent25.parentCount p d b m r t)
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t)
        (fun i => Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t, i, 0⟩).val)) := by
  have he := (constituent_P_projection_fibres40 p d hd hb ε r W β J).1.some
  exact (Nat.card_congr he).trans Nat.card_pi

private theorem apq_pfiber_lower {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) /
        (∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
          Fintype.card (Chunk (w+w))) ≤
      (Nat.card (Parent25.PFiber p d b ε m r W β J.val) : ℝ) := by
  classical
  let e : Fin s → ℝ := fun t =>
    let n := Parent25.parentCount p d b m r t
    (n : ℝ) *
      (entropyNats (fun σ => (Parent25.betaCount p d b ε m r W β t σ : ℝ) / n) -
        entropyNats (fun c =>
          (projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
            (Parent25.betaCount p d b ε m r W β t) c : ℝ) / n))
  have he : ∑ t, e t = Parent25.pRate p d b ε m r W β * (b*m : ℕ) :=
    parent25_p_exponent_identity40 p d hd m hb ε r W β J
  have hfactor : ∀ t, Real.exp (e t) /
        ((Parent25.parentCount p d b m r t : ℝ) + 1) ^ Fintype.card (Chunk (w+w)) ≤
      (Nat.card (ProjectionFiber (Parent25.parentCount p d b m r t)
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t)
        (fun i => Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t, i, 0⟩).val)) : ℝ) := by
    intro t
    let y := apq_projectionWord p d ε m r W β J t
    have h := projectionFiber_entropy_lower
      (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
      (Parent25.betaCount p d b ε m r W β t)
      (parent25_betaCount_sum40 p d ε m r W β t) y
    simpa only [e, y, Nat.card_eq_fintype_card] using h
  rw [← he, Real.exp_sum, ← Finset.prod_div_distrib,
    apq_pfiber_card p d hd m hb ε r W β J, Nat.cast_prod]
  apply Finset.prod_le_prod
  · intro t _
    positivity
  · intro t _
    exact hfactor t

private theorem apq_pfiber_upper {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    (Nat.card (Parent25.PFiber p d b ε m r W β J.val) : ℝ) ≤
      Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) *
        ∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
          Fintype.card (Fin (2*w+1)) := by
  classical
  let e : Fin s → ℝ := fun t =>
    let n := Parent25.parentCount p d b m r t
    (n : ℝ) *
      (entropyNats (fun σ => (Parent25.betaCount p d b ε m r W β t σ : ℝ) / n) -
        entropyNats (fun c =>
          (projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
            (Parent25.betaCount p d b ε m r W β t) c : ℝ) / n))
  have he : ∑ t, e t = Parent25.pRate p d b ε m r W β * (b*m : ℕ) :=
    parent25_p_exponent_identity40 p d hd m hb ε r W β J
  have hfactor : ∀ t,
      (Nat.card (ProjectionFiber (Parent25.parentCount p d b m r t)
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t)
        (fun i => Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t, i, 0⟩).val)) : ℝ) ≤
        Real.exp (e t) *
          ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
            Fintype.card (Fin (2*w+1)) := by
    intro t
    let y := apq_projectionWord p d ε m r W β J t
    have h := projectionFiber_entropy_upper
      (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
      (Parent25.betaCount p d b ε m r W β t)
      (parent25_betaCount_sum40 p d ε m r W β t) y
    simpa only [e, y, Nat.card_eq_fintype_card] using h
  rw [apq_pfiber_card p d hd m hb ε r W β J, Nat.cast_prod,
    ← he, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro t _
    exact Nat.cast_nonneg _
  · intro t _
    exact hfactor t

private theorem apq_qfiber_upper {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    (Nat.card {a : Parent25.PFiber p d b ε m r W β J.val //
      Parent25.compatible p d b m r W J.val a.val} : ℝ) ≤
        Real.exp (Parent25.qRate p d r W * (b*m : ℕ)) := by
  classical
  let Family := (t : Fin s) → (c : Parent25.Cell p t) →
    {x : Fin (Nat.card (Parent25.CellPos p d b m r W J.val t c)) → Chunk w //
      ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = Parent25.cellHistogram p d m r W t c σ}
  have he := (constituent_Q_type_classes40 p d hd hb r W J).1.some
  have hcardQ : Nat.card (Parent25.QFiber p d b m r W J.val) =
      ∏ t, ∏ c : Parent25.Cell p t,
        Nat.card {x : Fin (Nat.card (Parent25.CellPos p d b m r W J.val t c)) → Chunk w //
          ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = Parent25.cellHistogram p d m r W t c σ} := by
    calc
      _ = Nat.card Family := Nat.card_congr he
      _ = _ := Nat.card_pi.trans (by
        apply Finset.prod_congr rfl
        intro t _
        exact Nat.card_pi)
  have hfactor : ∀ t (c : Parent25.Cell p t),
      (Nat.card {x : Fin (Nat.card (Parent25.CellPos p d b m r W J.val t c)) → Chunk w //
        ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = Parent25.cellHistogram p d m r W t c σ} : ℝ) ≤
      Real.exp ((Nat.card (Parent25.CellPos p d b m r W J.val t c) : ℝ) *
        entropyNats (fun σ => (Parent25.cellHistogram p d m r W t c σ : ℝ) /
          Nat.card (Parent25.CellPos p d b m r W J.val t c))) := by
    intro t c
    have h := type_class_bounds
      (Nat.card (Parent25.CellPos p d b m r W J.val t c))
      (Parent25.cellHistogram p d m r W t c)
      ((constituent_Q_type_classes40 p d hd hb r W J).2 t c)
    simpa only [Nat.card_eq_fintype_card] using h.2
  calc
    (Nat.card {a : Parent25.PFiber p d b ε m r W β J.val //
      Parent25.compatible p d b m r W J.val a.val} : ℝ) ≤
        (Nat.card (Parent25.QFiber p d b m r W J.val) : ℝ) := by
          exact_mod_cast Nat.card_le_card_of_injective
            (fun a : {a : Parent25.PFiber p d b ε m r W β J.val //
              Parent25.compatible p d b m r W J.val a.val} =>
                (⟨a.val.val, a.val.property.1, a.property⟩ :
                  Parent25.QFiber p d b m r W J.val))
            (fun a z h => by
              apply Subtype.ext
              apply Subtype.ext
              exact congrArg
                (fun q : Parent25.QFiber p d b m r W J.val => q.val) h)
    _ = ∏ t, ∏ c : Parent25.Cell p t,
      (Nat.card {x : Fin (Nat.card (Parent25.CellPos p d b m r W J.val t c)) → Chunk w //
        ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = Parent25.cellHistogram p d m r W t c σ} : ℝ) := by
          rw [hcardQ, Nat.cast_prod]
          simp_rw [Nat.cast_prod]
    _ ≤
      ∏ t, ∏ c : Parent25.Cell p t,
        Real.exp ((Nat.card (Parent25.CellPos p d b m r W J.val t c) : ℝ) *
          entropyNats (fun σ => (Parent25.cellHistogram p d m r W t c σ : ℝ) /
            Nat.card (Parent25.CellPos p d b m r W J.val t c))) := by
          apply Finset.prod_le_prod
          · intro t _
            positivity
          · intro t _
            apply Finset.prod_le_prod
            · intro c _
              exact Nat.cast_nonneg _
            · intro c _
              exact hfactor t c
    _ = Real.exp (∑ t, ∑ c : Parent25.Cell p t,
        (Nat.card (Parent25.CellPos p d b m r W J.val t c) : ℝ) *
          entropyNats (fun σ => (Parent25.cellHistogram p d m r W t c σ : ℝ) /
            Nat.card (Parent25.CellPos p d b m r W J.val t c))) := by
          simp_rw [Real.exp_sum]
    _ = _ := by rw [parent25_q_exponent_identity40 p d hd m hb ε r W β J]

/-- All three normalized finite bounds, separated from the raw-P identification `parent25_rawP_identification40`. -/
theorem parent25_finite_bounds_bridge40 : Parent25.FiniteBoundsBridge40 := by
  intro w s b m p d hd hb ε r W β
  dsimp only
  let N := (Nat.card (AlphaLabel p d b m r) : ℝ)
  let ambient := (Nat.card (AlphaLabel p d b m r ×
    (Parent25.Pop p d b m r).Part (Parent25.side d r W)) : ℝ)
  let poly := ∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
    Fintype.card (Chunk (w+w))
  let coarsePoly := ∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
    Fintype.card (Fin (2*w+1))
  have hcards := parent25_joint_cardinality_identities p d ε m r W β
  refine ⟨hcards.1, hcards.2, ?_, ?_, ?_⟩
  · rw [hcards.1]
    calc
      N * Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) / poly =
          ∑ _J : AlphaLabel p d b m r,
            (Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) / poly) := by
            simp only [Finset.sum_const, nsmul_eq_mul, N, Nat.card_eq_fintype_card,
              Finset.card_univ]
            ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro J _
        exact apq_pfiber_lower p d hd m hb ε r W β J
  · rw [hcards.1]
    calc
      (∑ J : AlphaLabel p d b m r,
          (Nat.card (Parent25.PFiber p d b ε m r W β J.val) : ℝ)) ≤
        ∑ _J : AlphaLabel p d b m r,
          (Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) * coarsePoly) := by
            apply Finset.sum_le_sum
            intro J _
            exact apq_pfiber_upper p d hd m hb ε r W β J
      _ = N * Real.exp (Parent25.pRate p d b ε m r W β * (b*m : ℕ)) * coarsePoly := by
        simp only [Finset.sum_const, nsmul_eq_mul, N, Nat.card_eq_fintype_card,
          Finset.card_univ]
        ring
  · rw [hcards.2]
    calc
      (∑ J : AlphaLabel p d b m r,
          (Nat.card {a : Parent25.PFiber p d b ε m r W β J.val //
            Parent25.compatible p d b m r W J.val a.val} : ℝ)) ≤
        ∑ _J : AlphaLabel p d b m r,
          Real.exp (Parent25.qRate p d r W * (b*m : ℕ)) := by
            apply Finset.sum_le_sum
            intro J _
            exact apq_qfiber_upper p d hd m hb ε r W β J
      _ = N * Real.exp (Parent25.qRate p d r W * (b*m : ℕ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, N, Nat.card_eq_fintype_card,
          Finset.card_univ]

private def apqStageAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def apqStageParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, apqStageAlphaCount b m p d r t u

private abbrev APQStagePos {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (apqStageParentCount b m p d r t) × Fin 2)

private noncomputable abbrev apqStageP {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : RawPopulation :=
  stagePopulationAt 0 p d b m r

private noncomputable def apqStageWord {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (apqStageP p d b m r).Part S) :
    APQStagePos b m p d r → Chunk w := by
  classical
  dsimp [apqStageP, stagePopulationAt, APQStagePos, apqStageParentCount,
    apqStageAlphaCount] at a ⊢
  exact a

private def apqPairedChunk {w s : ℕ} {b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (a : APQStagePos b m p d r → Chunk w) (t : Fin s)
    (i : Fin (apqStageParentCount b m p d r t)) : Chunk (w+w) :=
  fun c => if hc : c.val < w then
    a ⟨t, (i, ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
  else a ⟨t, (i, ⟨1, by omega⟩)⟩ ⟨c.val-w, by omega⟩

private noncomputable def apqPartChunk {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (apqStageP p d b m r).Part S)
    (i : Fin (apqStageP p d b m r).n) : Chunk w := by
  classical
  let code := (apqStageP p d b m r).fine S a i
  have hcode : code < Fintype.card (Chunk w) := by
    dsimp [code, apqStageP, stagePopulationAt]
    exact (Fintype.equivFin (Chunk w) _).isLt
  exact (Fintype.equivFin (Chunk w)).symm ⟨code, hcode⟩

private noncomputable def apqCoarseContains {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (j : (apqStageP p d b m r).Label)
    (a : (apqStageP p d b m r).Part S) : Prop :=
  ∀ i, chunkLvl (apqPartChunk b m p d r S a i) =
    ((apqStageP p d b m r).coarse j S i).val

private def apqRepresentedSide {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) : Side :=
  if W = 0 then d.perm r .Y else d.perm r .Z

private theorem apqRepresentedSide_eq_parent {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) :
    apqRepresentedSide d r W = Parent25.side d r W := by
  by_cases h : W = 0
  · simp only [apqRepresentedSide, Parent25.side, h, if_pos]
  · simp [apqRepresentedSide, Parent25.side, h]

private abbrev APQEmpiricalLaw (w s : ℕ) := Fin s → Chunk (w+w) → ℚ

private noncomputable def apqEmpiricalLaw {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (apqStageP p d b m r).Part S) : APQEmpiricalLaw w s :=
  let x := apqStageWord b m p d r S a
  fun t σ =>
    ((OmegaBound.ADVXXZ.typeCnt (fun i => apqPairedChunk x t i) σ : ℕ) : ℚ) /
      apqStageParentCount b m p d r t

private abbrev APQLawSample {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (S : Side) :=
  AlphaLabel p d b m r × (apqStageP p d b m r).Part S

private noncomputable def apqContainingSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (r : Fin 6) (S : Side) : Finset (APQLawSample p d b m r S) := by
  classical
  exact Finset.univ.filter fun z => apqCoarseContains b m p d r S z.1.val z.2

private noncomputable def apqLawSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (epsilon : ℚ)
    (m : ℕ) (r : Fin 6) (W : Fin 2)
    (beta : RepresentedLaw p d b epsilon m r W) :
    Finset (APQLawSample p d b m r (apqRepresentedSide d r W)) := by
  classical
  let S := apqRepresentedSide d r W
  exact (apqContainingSamples p d b m r S).filter fun z =>
    apqEmpiricalLaw b m p d r S z.2 = beta.val

private noncomputable def apqPositionEncoding {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    APQStagePos b m p d r ≃ Fin (apqStageP p d b m r).n := by
  classical
  dsimp only [APQStagePos, apqStageParentCount, apqStageAlphaCount, apqStageP,
    stagePopulationAt]
  exact @Fintype.equivFin _ (Fintype.ofFinite _)

private theorem apqCoordFin_val {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem apqPartChunk_eq_word {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (apqStageP p d b m r).Part S)
    (i : Fin (apqStageP p d b m r).n) :
    apqPartChunk b m p d r S a i = a ((apqPositionEncoding p d r).symm i) := by
  classical
  unfold apqPartChunk
  dsimp only [apqStageP, stagePopulationAt]
  simp only [apqPositionEncoding, id_eq]
  convert (Fintype.equivFin (Chunk w)).symm_apply_apply
    (a ((apqPositionEncoding p d r).symm i)) using 1

private theorem apqCoarse_at_encoding {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (S : Side) (t : Fin s)
    (ih : Fin (apqStageParentCount b m p d r t) × Fin 2) :
    (apqStageP p d b m r).coarse J.val S (apqPositionEncoding p d r ⟨t, ih⟩) =
      Parent25.coordFin S (J.val.val ⟨t, ih⟩).val := by
  classical
  change Parent25.coordFin S
      (J.val.val ((apqPositionEncoding p d r).symm
        (apqPositionEncoding p d r ⟨t, ih⟩))).val =
    Parent25.coordFin S (J.val.val ⟨t, ih⟩).val
  rw [Equiv.symm_apply_apply]

private theorem apqParentContains_iff_coarse {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Fin 2) (J : AlphaLabel p d b m r)
    (a : (apqStageP p d b m r).Part (Parent25.side d r W)) :
    Parent25.contains p d b m r W J.val a ↔
      apqCoarseContains b m p d r (Parent25.side d r W) J.val a := by
  constructor
  · intro h i
    generalize hz : (apqPositionEncoding p d r).symm i = z
    rcases z with ⟨t, ih⟩
    have hi : apqPositionEncoding p d r ⟨t, ih⟩ = i := by
      rw [← hz, Equiv.apply_symm_apply]
    have hw := apqPartChunk_eq_word p d r (Parent25.side d r W) a i
    have hc := apqCoarse_at_encoding p d r J (Parent25.side d r W) t ih
    have hh := h ⟨t, ih⟩
    have hwI : apqPartChunk b m p d r (Parent25.side d r W) a i = a ⟨t, ih⟩ := by
      simpa [hz] using hw
    have hcI : (apqStageP p d b m r).coarse J.val (Parent25.side d r W) i =
        Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t, ih⟩).val := by
      simpa [hi] using hc
    rw [hwI, hcI]
    simpa only [apqCoordFin_val] using hh
  · intro h
    rintro ⟨t, ih⟩
    have hh := h (apqPositionEncoding p d r ⟨t, ih⟩)
    rw [apqPartChunk_eq_word, Equiv.symm_apply_apply, apqCoarse_at_encoding] at hh
    simpa only [apqCoordFin_val] using hh

private theorem apqParentEmpirical_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Fin 2) (a : (apqStageP p d b m r).Part (Parent25.side d r W)) :
    Parent25.empirical p d b m r W a =
      apqEmpiricalLaw b m p d r (Parent25.side d r W) a := by
  rfl

private theorem apq_jointP_copied {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (epsilon : ℚ) (m : ℕ) (r : Fin 6)
    (W : Fin 2) (beta : RepresentedLaw p d b epsilon m r W) :
    jointP p d b epsilon m r W beta =
      ((apqLawSamples p d b epsilon m r W beta).card : ℝ) /
        (Fintype.card (APQLawSample p d b m r (apqRepresentedSide d r W)) : ℝ) := by
  rfl

theorem parent25_rawP_identification40 : Parent25.RawPIdentification := by
  intro w s p d b ε m r W β
  classical
  rw [apq_jointP_copied]
  unfold Parent25.jointP
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold apqLawSamples apqContainingSamples
  dsimp only
  rw [apqRepresentedSide_eq_parent]
  simp only [Finset.filter_filter, and_assoc]
  apply congrArg (fun n : ℕ => (n : ℝ) /
    (Fintype.card (AlphaLabel p d b m r ×
      (Parent25.Pop p d b m r).Part (Parent25.side d r W)) : ℝ))
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← apqParentContains_iff_coarse, ← apqParentEmpirical_eq]

theorem constituent_PQ_finite_bounds40 :
    Parent25.RawPIdentification ∧ Parent25.FiniteBoundsBridge40 :=
  ⟨parent25_rawP_identification40, parent25_finite_bounds_bridge40⟩

end OmegaBound.ADVXXZGeneral
end
