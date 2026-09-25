import OmegaBound.ADVXXZGeneralAmend25Parent
import OmegaBound.ADVXXZGeneralCExact36Defs

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def pqStageAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def pqStageParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, pqStageAlphaCount b m p d r t u

private abbrev PQStagePos {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (pqStageParentCount b m p d r t) × Fin 2)

private noncomputable abbrev pqStageP {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : RawPopulation :=
  stagePopulationAt 0 p d b m r

private noncomputable def pqStageWord {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (pqStageP p d b m r).Part S) :
    PQStagePos b m p d r → Chunk w := by
  classical
  dsimp [pqStageP, stagePopulationAt, PQStagePos, pqStageParentCount,
    pqStageAlphaCount] at a ⊢
  exact a

private def pqPairedChunk {w s : ℕ} {b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (a : PQStagePos b m p d r → Chunk w) (t : Fin s)
    (i : Fin (pqStageParentCount b m p d r t)) : Chunk (w + w) :=
  fun c => if hc : c.val < w then
    a ⟨t, (i, ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
  else
    a ⟨t, (i, ⟨1, by omega⟩)⟩ ⟨c.val - w, by omega⟩

private noncomputable def pqPartChunk {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (pqStageP p d b m r).Part S)
    (i : Fin (pqStageP p d b m r).n) : Chunk w := by
  classical
  let code := (pqStageP p d b m r).fine S a i
  have hcode : code < Fintype.card (Chunk w) := by
    dsimp [code, pqStageP, stagePopulationAt]
    exact (Fintype.equivFin (Chunk w) _).isLt
  exact (Fintype.equivFin (Chunk w)).symm ⟨code, hcode⟩

private noncomputable def pqCoarseContains {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (j : (pqStageP p d b m r).Label)
    (a : (pqStageP p d b m r).Part S) : Prop :=
  ∀ i, chunkLvl (pqPartChunk b m p d r S a i) =
    ((pqStageP p d b m r).coarse j S i).val

private noncomputable def pqFineCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (pqStageP p d b m r).Part S)
    (cell : Fin (pqStageP p d b m r).n → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun i =>
    cell i ∧ pqPartChunk b m p d r S a i = σ).card

private noncomputable def pqJointCell {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (pqStageP p d b m r).Label) (X Y Z : Side)
    (gx gy gz : Fin ((pqStageP p d b m r).grade + 1))
    (i : Fin (pqStageP p d b m r).n) : Prop :=
  (pqStageP p d b m r).coarse j X i = gx ∧
  (pqStageP p d b m r).coarse j Y i = gy ∧
  (pqStageP p d b m r).coarse j Z i = gz

private noncomputable def pqMarginalCell {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (pqStageP p d b m r).Label) (S : Side)
    (g : Fin ((pqStageP p d b m r).grade + 1))
    (i : Fin (pqStageP p d b m r).n) : Prop :=
  (pqStageP p d b m r).coarse j S i = g

private noncomputable def pqCompatibleY {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (j : (pqStageP p d b m r).Label)
    (a : (pqStageP p d b m r).Part S) : Prop := by
  classical
  let P := pqStageP p d b m r
  let sideX := d.perm r .X
  let sideY := d.perm r .Y
  let sideZ := d.perm r .Z
  exact ∃ a₀ : P.Part S, P.incidence S j a₀ ∧
    (∀ gx gy gz σ, gz.val = 0 →
      pqFineCount b m p d r S a (pqJointCell b m p d r j sideX sideY sideZ gx gy gz) σ =
      pqFineCount b m p d r S a₀ (pqJointCell b m p d r j sideX sideY sideZ gx gy gz) σ) ∧
    ∀ gy σ,
      pqFineCount b m p d r S a (pqMarginalCell b m p d r j sideY gy) σ =
      pqFineCount b m p d r S a₀ (pqMarginalCell b m p d r j sideY gy) σ

private noncomputable def pqCompatibleZ {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (j : (pqStageP p d b m r).Label)
    (a : (pqStageP p d b m r).Part S) : Prop := by
  classical
  let P := pqStageP p d b m r
  let sideX := d.perm r .X
  let sideY := d.perm r .Y
  let sideZ := d.perm r .Z
  exact ∃ a₀ : P.Part S, P.incidence S j a₀ ∧
    (∀ gx gy gz σ, (gx.val = 0 ∨ gy.val = 0) →
      pqFineCount b m p d r S a (pqJointCell b m p d r j sideX sideY sideZ gx gy gz) σ =
      pqFineCount b m p d r S a₀ (pqJointCell b m p d r j sideX sideY sideZ gx gy gz) σ) ∧
    ∀ gz σ,
      pqFineCount b m p d r S a (pqMarginalCell b m p d r j sideZ gz) σ =
      pqFineCount b m p d r S a₀ (pqMarginalCell b m p d r j sideZ gz) σ

private def pqSide {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (which : Fin 2) : Side :=
  if which = 0 then d.perm r .Y else d.perm r .Z

private theorem pqSide_eq_parent {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (which : Fin 2) :
    pqSide d r which = Parent25.side d r which := by
  by_cases h : which = 0
  · simp only [pqSide, Parent25.side, h, if_pos]
  · simp [pqSide, Parent25.side, h]

private noncomputable def pqCompatibleForWhich {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : (pqStageP p d b m r).Label)
    (a : (pqStageP p d b m r).Part (pqSide d r which)) : Prop :=
  if which = 0 then
    pqCompatibleY b m p d r (pqSide d r which) j a
  else
    pqCompatibleZ b m p d r (pqSide d r which) j a

private abbrev PQEmpiricalLaw (w s : ℕ) := Fin s → Chunk (w + w) → ℚ

private noncomputable def pqEmpiricalLaw {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a : (pqStageP p d b m r).Part S) : PQEmpiricalLaw w s :=
  let x := pqStageWord b m p d r S a
  fun t σ =>
    ((OmegaBound.ADVXXZ.typeCnt (fun i => pqPairedChunk x t i) σ : ℕ) : ℚ) /
      pqStageParentCount b m p d r t

private def pqHistogram {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (f : I → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => f i = a).card

private theorem pq_exists_perm_of_histogram {I A : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq A] (f g : I → A)
    (h : ∀ a, pqHistogram f a = pqHistogram g a) :
    ∃ e : Equiv.Perm I, ∀ i, g (e i) = f i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // f i = a} ≃ {i // g i = a}) :=
    ⟨fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), fun i => ?_⟩
  exact (e (f i) ⟨i, rfl⟩).2

private theorem pq_empirical_histogram_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (t : Fin s) (σ : Chunk (w + w)) :
    pqHistogram (fun i => pqPairedChunk (pqStageWord b m p d r S a) t i) σ =
      pqHistogram (fun i => pqPairedChunk (pqStageWord b m p d r S c) t i) σ := by
  by_cases hn : pqStageParentCount b m p d r t = 0
  · apply congrArg Finset.card
    ext i
    exact (hn ▸ i).elim0
  · have hnQ : (pqStageParentCount b m p d r t : ℚ) ≠ 0 := by
      exact_mod_cast hn
    have ht := congrFun (congrFun hLaw t) σ
    dsimp only [pqEmpiricalLaw] at ht
    rw [div_left_inj' hnQ] at ht
    exact_mod_cast ht

private noncomputable def pqPairPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (t : Fin s) : Equiv.Perm (Fin (pqStageParentCount b m p d r t)) :=
  Classical.choose (pq_exists_perm_of_histogram
    (fun i => pqPairedChunk (pqStageWord b m p d r S a) t i)
    (fun i => pqPairedChunk (pqStageWord b m p d r S c) t i)
    (pq_empirical_histogram_eq p d r S a c hLaw t))

private theorem pqPairPerm_spec {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (t : Fin s) (i : Fin (pqStageParentCount b m p d r t)) :
    pqPairedChunk (pqStageWord b m p d r S c) t
        (pqPairPerm p d r S a c hLaw t i) =
      pqPairedChunk (pqStageWord b m p d r S a) t i :=
  Classical.choose_spec (pq_exists_perm_of_histogram
    (fun i => pqPairedChunk (pqStageWord b m p d r S a) t i)
    (fun i => pqPairedChunk (pqStageWord b m p d r S c) t i)
    (pq_empirical_histogram_eq p d r S a c hLaw t)) i

private theorem pqPairPerm_half_spec {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (t : Fin s) (i : Fin (pqStageParentCount b m p d r t)) (h : Fin 2) :
    pqStageWord b m p d r S c ⟨t, (pqPairPerm p d r S a c hLaw t i, h)⟩ =
      pqStageWord b m p d r S a ⟨t, (i, h)⟩ := by
  funext j
  fin_cases h
  · have hs := congrFun (pqPairPerm_spec p d r S a c hLaw t i)
        ⟨j.val, by omega⟩
    simpa only [pqPairedChunk, dif_pos j.isLt] using hs
  · have hs := congrFun (pqPairPerm_spec p d r S a c hLaw t i)
        ⟨w + j.val, by omega⟩
    have hn : ¬ w + j.val < w := by omega
    simpa only [pqPairedChunk, dif_neg hn, Nat.add_sub_cancel_left] using hs

private irreducible_def pqAlphaShape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (pqStageParentCount b m p d r t) × Fin 2) : ChildShape p t :=
  J.1.1 ⟨t, ih⟩

private irreducible_def pqAlphaZero {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (pqStageParentCount b m p d r t)) : ChildShape p t :=
  pqAlphaShape p d r J t (i, ⟨0, by omega⟩)

private theorem pqAlphaLabel_target {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    pqHistogram (pqAlphaZero p d r J t) u = pqStageAlphaCount b m p d r t u := by
  classical
  have hJ : J.1 ∈ (stagePopulationAt 0 p d b m r).target := J.2
  have h := (Finset.mem_filter.mp hJ).2 t u
  simpa only [pqHistogram, pqAlphaZero, pqAlphaShape, pqStageAlphaCount] using h

private theorem pqAlphaLabel_complementary {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (pqStageParentCount b m p d r t)) :
    pqAlphaShape p d r J t (i, ⟨1, by omega⟩) =
      complement p t (pqAlphaShape p d r J t (i, ⟨0, by omega⟩)) := by
  simpa only [pqAlphaShape] using J.1.2.2 t i

private def pqCoordFin {w : ℕ} (S : Side) (u : Shape w) : Fin (2 * w + 1) :=
  match S with
  | .X => u.1.1
  | .Y => u.1.2.1
  | .Z => u.1.2.2

private theorem pqCoordFin_val {w : ℕ} (S : Side) (u : Shape w) :
    (pqCoordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem pqAlphaLabel_marginal {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (h : Fin 2)
    (S : Side) (g : Fin (2 * w + 1)) :
    pqHistogram (fun i : Fin (pqStageParentCount b m p d r t) =>
      pqCoordFin S (pqAlphaShape p d r J t (i, h)).1) g =
      ∑ u : ChildShape p t,
        if pqCoordFin S ((if h = 0 then u else complement p t u).1) = g
        then pqStageAlphaCount b m p d r t u else 0 := by
  classical
  have hJ := J.1.2.1 t h S g
  simpa only [pqHistogram, pqAlphaShape, pqCoordFin, pqStageAlphaCount] using hJ

private theorem pq_filter_card_eq_of_perm {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ => e i) (fun i _ => e.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (h (e.symm i)).mpr (by simpa using (Finset.mem_filter.mp hi).2)
  · intro i _
    exact e.symm_apply_apply i
  · intro i _
    exact e.apply_symm_apply i

private def pqRelabelShape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) :
    (z : PQStagePos b m p d r) → ChildShape p z.1 :=
  fun z => J.1.1 ⟨z.1, (E z.1 z.2.1, z.2.2)⟩

set_option maxHeartbeats 1000000 in
-- Constructing the nested target-label subtype unfolds the population carrier once.
private noncomputable def pqRelabelAlpha {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) : AlphaLabel p d b m r := by
  classical
  unfold AlphaLabel
  refine ⟨⟨pqRelabelShape p d r E J, ?_, ?_⟩, ?_⟩
  · intro t h S g
    have hm := pqAlphaLabel_marginal p d r J t h S g
    have hcard := pq_filter_card_eq_of_perm (E t).symm
      (fun i => pqCoordFin S (pqAlphaShape p d r J t (i, h)).1 = g)
      (fun i => pqCoordFin S (pqRelabelShape p d r E J ⟨t, (i, h)⟩).1 = g)
      (fun i => by
        simp only [pqAlphaShape, pqRelabelShape]
        constructor
        · intro hi
          rwa [(E t).apply_symm_apply]
        · intro hi
          rwa [(E t).apply_symm_apply] at hi)
    exact hcard.symm.trans hm
  · intro t i
    change pqRelabelShape p d r E J ⟨t, (i, ⟨1, by omega⟩)⟩ =
      complement p t (pqRelabelShape p d r E J ⟨t, (i, ⟨0, by omega⟩)⟩)
    simpa only [pqRelabelShape, pqAlphaShape] using
      pqAlphaLabel_complementary p d r J t (E t i)
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t u
    have ht := pqAlphaLabel_target p d r J t u
    have hcard := pq_filter_card_eq_of_perm (E t).symm
      (fun i => pqAlphaShape p d r J t (i, ⟨0, by omega⟩) = u)
      (fun i => pqRelabelShape p d r E J ⟨t, (i, ⟨0, by omega⟩)⟩ = u)
      (fun i => by
        change (pqAlphaShape p d r J t (i, ⟨0, by omega⟩) = u) ↔
          (pqRelabelShape p d r E J
            ⟨t, ((E t).symm i, ⟨0, by omega⟩)⟩ = u)
        rw [pqRelabelShape, pqAlphaShape, (E t).apply_symm_apply])
    exact hcard.symm.trans (by
      simpa only [pqHistogram, pqAlphaZero] using ht)

private theorem pqRelabelAlpha_shape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (z : PQStagePos b m p d r) :
    (pqRelabelAlpha p d r E J).1.1 z = pqRelabelShape p d r E J z := by
  rfl

private theorem pqRelabelAlpha_symm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) :
    pqRelabelAlpha p d r (fun t => (E t).symm) (pqRelabelAlpha p d r E J) = J := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  rcases z with ⟨t, i, h⟩
  rw [pqRelabelAlpha_shape, pqRelabelShape, pqRelabelAlpha_shape, pqRelabelShape]
  have he := congrArg (fun j => (j, h)) ((E t).apply_symm_apply i)
  simpa only [pqAlphaShape] using congrArg (pqAlphaShape p d r J t) he

private noncomputable def pqRelabelAlphaEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t))) :
    Equiv.Perm (AlphaLabel p d b m r) where
  toFun := pqRelabelAlpha p d r E
  invFun := pqRelabelAlpha p d r (fun t => (E t).symm)
  left_inv := pqRelabelAlpha_symm p d r E
  right_inv := by
    intro J
    simpa only [Equiv.symm_symm] using
      pqRelabelAlpha_symm p d r (fun t => (E t).symm) J

private noncomputable def pqPositionEncoding {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    PQStagePos b m p d r ≃ Fin (pqStageP p d b m r).n := by
  classical
  dsimp only [PQStagePos, pqStageParentCount, pqStageAlphaCount, pqStageP,
    stagePopulationAt]
  exact @Fintype.equivFin _ (Fintype.ofFinite _)

private def pqRowHalfPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (t : Fin s) : Equiv.Perm (Fin (pqStageParentCount b m p d r t) × Fin 2) :=
  Equiv.prodCongr (E t) (Equiv.refl (Fin 2))

private def pqPositionPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t))) :
    Equiv.Perm (PQStagePos b m p d r) :=
  Equiv.sigmaCongrRight fun t => pqRowHalfPerm p d r E t

private noncomputable def pqEncodedPositionPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t))) :
    Equiv.Perm (Fin (pqStageP p d b m r).n) :=
  (pqPositionEncoding p d r).symm.trans
    ((pqPositionPerm p d r E).trans (pqPositionEncoding p d r))

private theorem pqEncodedPositionPerm_raw {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (i : Fin (pqStageP p d b m r).n) :
    (pqPositionEncoding p d r).symm (pqEncodedPositionPerm p d r E i) =
      pqPositionPerm p d r E ((pqPositionEncoding p d r).symm i) := by
  change (pqPositionEncoding p d r).symm
      (pqPositionEncoding p d r
        (pqPositionPerm p d r E ((pqPositionEncoding p d r).symm i))) = _
  exact (pqPositionEncoding p d r).symm_apply_apply _

private theorem pqPartChunk_eq_word {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (x : (pqStageP p d b m r).Part S)
    (i : Fin (pqStageP p d b m r).n) :
    pqPartChunk b m p d r S x i = x ((pqPositionEncoding p d r).symm i) := by
  classical
  unfold pqPartChunk
  dsimp only [pqStageP, stagePopulationAt]
  simp only [pqPositionEncoding, id_eq]
  convert (Fintype.equivFin (Chunk w)).symm_apply_apply
    (x ((pqPositionEncoding p d r).symm i)) using 1

private theorem pqPartChunk_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (i : Fin (pqStageP p d b m r).n) :
    pqPartChunk b m p d r S c
        (pqEncodedPositionPerm p d r (pqPairPerm p d r S a c hLaw) i) =
      pqPartChunk b m p d r S a i := by
  rw [pqPartChunk_eq_word, pqPartChunk_eq_word, pqEncodedPositionPerm_raw]
  rcases (pqPositionEncoding p d r).symm i with ⟨t, ih⟩
  exact pqPairPerm_half_spec p d r S a c hLaw t ih.1 ih.2

private theorem pqCoarse_at_encoding {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (S : Side) (t : Fin s)
    (ih : Fin (pqStageParentCount b m p d r t) × Fin 2) :
    (pqStageP p d b m r).coarse J.1 S (pqPositionEncoding p d r ⟨t, ih⟩) =
      pqCoordFin S (pqAlphaShape p d r J t ih).1 := by
  classical
  change pqCoordFin S
      (J.1.1 ((pqPositionEncoding p d r).symm
        (pqPositionEncoding p d r ⟨t, ih⟩))).1 =
    pqCoordFin S (pqAlphaShape p d r J t ih).1
  rw [Equiv.symm_apply_apply, pqAlphaShape]

private theorem pqCoarse_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (i : Fin (pqStageP p d b m r).n) :
    (pqStageP p d b m r).coarse (pqRelabelAlpha p d r E J).1 S i =
      (pqStageP p d b m r).coarse J.1 S (pqEncodedPositionPerm p d r E i) := by
  classical
  generalize hz : (pqPositionEncoding p d r).symm i = z
  rcases z with ⟨t, ih⟩
  have hi : pqPositionEncoding p d r ⟨t, ih⟩ = i := by
    rw [← hz]
    exact (pqPositionEncoding p d r).apply_symm_apply i
  have hei : pqEncodedPositionPerm p d r E i =
      pqPositionEncoding p d r ⟨t, (E t ih.1, ih.2)⟩ := by
    apply (pqPositionEncoding p d r).symm.injective
    rw [pqEncodedPositionPerm_raw, Equiv.symm_apply_apply, hz]
    rfl
  calc
    (pqStageP p d b m r).coarse (pqRelabelAlpha p d r E J).1 S i =
        pqCoordFin S (pqAlphaShape p d r (pqRelabelAlpha p d r E J) t ih).1 := by
      rw [← hi, pqCoarse_at_encoding]
    _ = pqCoordFin S (pqAlphaShape p d r J t (E t ih.1, ih.2)).1 := by
      rw [pqAlphaShape, pqRelabelAlpha_shape, pqRelabelShape, pqAlphaShape]
    _ = (pqStageP p d b m r).coarse J.1 S
        (pqEncodedPositionPerm p d r E i) := by
      rw [hei, pqCoarse_at_encoding]

private theorem pqCoarseContains_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hLaw : pqEmpiricalLaw b m p d r S a = pqEmpiricalLaw b m p d r S c)
    (J : AlphaLabel p d b m r) :
    pqCoarseContains b m p d r S J.1 c ↔
      pqCoarseContains b m p d r S
        (pqRelabelAlpha p d r (pqPairPerm p d r S a c hLaw) J).1 a := by
  classical
  let E := pqPairPerm p d r S a c hLaw
  let e := pqEncodedPositionPerm p d r E
  constructor
  · intro hc i
    have hp := pqPartChunk_forward p d r S a c hLaw i
    have hcoarse := pqCoarse_forward p d r E J S i
    calc
      chunkLvl (pqPartChunk b m p d r S a i) =
          chunkLvl (pqPartChunk b m p d r S c (e i)) :=
        congrArg chunkLvl hp.symm
      _ = ((pqStageP p d b m r).coarse J.1 S (e i)).val := hc (e i)
      _ = ((pqStageP p d b m r).coarse
          (pqRelabelAlpha p d r E J).1 S i).val :=
        congrArg Fin.val hcoarse.symm
  · intro ha j
    let i := e.symm j
    have hp := pqPartChunk_forward p d r S a c hLaw i
    have hcoarse := pqCoarse_forward p d r E J S i
    have hej : e i = j := e.apply_symm_apply j
    calc
      chunkLvl (pqPartChunk b m p d r S c j) =
          chunkLvl (pqPartChunk b m p d r S c (e i)) := by rw [hej]
      _ = chunkLvl (pqPartChunk b m p d r S a i) := congrArg chunkLvl hp
      _ = ((pqStageP p d b m r).coarse
          (pqRelabelAlpha p d r E J).1 S i).val := ha i
      _ = ((pqStageP p d b m r).coarse J.1 S (e i)).val :=
        congrArg Fin.val hcoarse
      _ = ((pqStageP p d b m r).coarse J.1 S j).val := by rw [hej]

private noncomputable def pqPermutePart {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (S : Side) : (pqStageP p d b m r).Part S ≃ (pqStageP p d b m r).Part S := by
  classical
  dsimp only [pqStageP, stagePopulationAt]
  let e := pqPositionPerm p d r E
  exact
    { toFun := fun x z => x (e z)
      invFun := fun x z => x (e.symm z)
      left_inv := fun x => by
        funext z
        exact congrArg x (e.apply_symm_apply z)
      right_inv := fun x => by
        funext z
        exact congrArg x (e.symm_apply_apply z) }

private theorem pqPermutePart_apply {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (S : Side) (x : (pqStageP p d b m r).Part S)
    (z : PQStagePos b m p d r) :
    pqPermutePart p d r E S x z = x (pqPositionPerm p d r E z) := by
  rfl

private theorem pqPermutePart_chunk {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (S : Side) (x : (pqStageP p d b m r).Part S)
    (i : Fin (pqStageP p d b m r).n) :
    pqPartChunk b m p d r S (pqPermutePart p d r E S x) i =
      pqPartChunk b m p d r S x (pqEncodedPositionPerm p d r E i) := by
  rw [pqPartChunk_eq_word, pqPartChunk_eq_word, pqEncodedPositionPerm_raw,
    pqPermutePart_apply]

private theorem pqIncidence_relabel {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (x : (pqStageP p d b m r).Part S)
    (hx : (pqStageP p d b m r).incidence S J.1 x) :
    (pqStageP p d b m r).incidence S (pqRelabelAlpha p d r E J).1
      (pqPermutePart p d r E S x) := by
  classical
  change
    (∀ z : PQStagePos b m p d r,
      chunkLvl (pqPermutePart p d r E S x z) =
        coord S ((pqRelabelAlpha p d r E J).1.1 z).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (pqStageParentCount b m p d r t) × Fin 2 =>
        (pqRelabelAlpha p d r E J).1.1 ⟨t, ih⟩ = u ∧
          pqPermutePart p d r E S x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild S t r u).prob σ).floor.toNat
  change
    (∀ z : PQStagePos b m p d r,
      chunkLvl (x z) = coord S (J.1.1 z).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (pqStageParentCount b m p d r t) × Fin 2 =>
        J.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild S t r u).prob σ).floor.toNat at hx
  constructor
  · rintro ⟨t, i, h⟩
    rw [pqPermutePart_apply, pqRelabelAlpha_shape, pqRelabelShape]
    exact hx.1 ⟨t, (E t i, h)⟩
  · intro t u σ
    have hcard := pq_filter_card_eq_of_perm (pqRowHalfPerm p d r E t).symm
      (fun ih => J.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)
      (fun ih => (pqRelabelAlpha p d r E J).1.1 ⟨t, ih⟩ = u ∧
        pqPermutePart p d r E S x ⟨t, ih⟩ = σ)
      (fun ih => by
        rcases ih with ⟨i, h⟩
        simp only [pqRowHalfPerm, pqRelabelAlpha_shape, pqRelabelShape,
          pqPermutePart_apply, pqPositionPerm]
        change (J.1.1 ⟨t, (i, h)⟩ = u ∧ x ⟨t, (i, h)⟩ = σ) ↔
          (J.1.1 ⟨t, (E t ((E t).symm i), h)⟩ = u ∧
            x ⟨t, (E t ((E t).symm i), h)⟩ = σ)
        rw [(E t).apply_symm_apply])
    exact hcard.symm.trans (hx.2 t u σ)

private theorem pqJointCell_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (X Y Z : Side)
    (gx gy gz : Fin ((pqStageP p d b m r).grade + 1))
    (i : Fin (pqStageP p d b m r).n) :
    pqJointCell b m p d r (pqRelabelAlpha p d r E J).1 X Y Z gx gy gz i ↔
      pqJointCell b m p d r J.1 X Y Z gx gy gz
        (pqEncodedPositionPerm p d r E i) := by
  unfold pqJointCell
  rw [pqCoarse_forward, pqCoarse_forward, pqCoarse_forward]

private theorem pqMarginalCell_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (T : Side)
    (g : Fin ((pqStageP p d b m r).grade + 1))
    (i : Fin (pqStageP p d b m r).n) :
    pqMarginalCell b m p d r (pqRelabelAlpha p d r E J).1 T g i ↔
      pqMarginalCell b m p d r J.1 T g
        (pqEncodedPositionPerm p d r E i) := by
  unfold pqMarginalCell
  rw [pqCoarse_forward]

private theorem pqFineCount_of_relabel {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (S : Side) (a c : (pqStageP p d b m r).Part S)
    (hpart : ∀ i, pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) =
      pqPartChunk b m p d r S a i)
    (cellNew cellOld : Fin (pqStageP p d b m r).n → Prop)
    (hcell : ∀ i, cellNew i ↔ cellOld (pqEncodedPositionPerm p d r E i))
    (σ : Chunk w) :
    pqFineCount b m p d r S a cellNew σ =
      pqFineCount b m p d r S c cellOld σ := by
  classical
  unfold pqFineCount
  exact pq_filter_card_eq_of_perm (pqEncodedPositionPerm p d r E)
    (fun i => cellNew i ∧ pqPartChunk b m p d r S a i = σ)
    (fun i => cellOld i ∧ pqPartChunk b m p d r S c i = σ)
    (fun i => by
      change (cellNew i ∧ pqPartChunk b m p d r S a i = σ) ↔
        (cellOld (pqEncodedPositionPerm p d r E i) ∧
          pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) = σ)
      rw [hcell i, hpart i])

private theorem pqCompatibleY_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (a c : (pqStageP p d b m r).Part S)
    (hpart : ∀ i, pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) =
      pqPartChunk b m p d r S a i)
    (hc : pqCompatibleY b m p d r S J.1 c) :
    pqCompatibleY b m p d r S (pqRelabelAlpha p d r E J).1 a := by
  classical
  rcases hc with ⟨x, hx, hjoint, hmarg⟩
  let y := pqPermutePart p d r E S x
  refine ⟨y, pqIncidence_relabel p d r E J S x hx, ?_, ?_⟩
  · intro gx gy gz σ hz
    calc
      pqFineCount b m p d r S a
          (pqJointCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ =
          pqFineCount b m p d r S c
            (pqJointCell b m p d r J.1
              (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ :=
        pqFineCount_of_relabel p d r E S a c hpart _ _
          (pqJointCell_iff p d r E J _ _ _ gx gy gz) σ
      _ = pqFineCount b m p d r S x
            (pqJointCell b m p d r J.1
              (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ :=
        hjoint gx gy gz σ hz
      _ = pqFineCount b m p d r S y
          (pqJointCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ := by
        symm
        exact pqFineCount_of_relabel p d r E S y x
          (fun i => (pqPermutePart_chunk p d r E S x i).symm) _ _
          (pqJointCell_iff p d r E J _ _ _ gx gy gz) σ
  · intro gy σ
    calc
      pqFineCount b m p d r S a
          (pqMarginalCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .Y) gy) σ =
          pqFineCount b m p d r S c
            (pqMarginalCell b m p d r J.1 (d.perm r .Y) gy) σ :=
        pqFineCount_of_relabel p d r E S a c hpart _ _
          (pqMarginalCell_iff p d r E J _ gy) σ
      _ = pqFineCount b m p d r S x
            (pqMarginalCell b m p d r J.1 (d.perm r .Y) gy) σ := hmarg gy σ
      _ = pqFineCount b m p d r S y
          (pqMarginalCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .Y) gy) σ := by
        symm
        exact pqFineCount_of_relabel p d r E S y x
          (fun i => (pqPermutePart_chunk p d r E S x i).symm) _ _
          (pqMarginalCell_iff p d r E J _ gy) σ

private theorem pqCompatibleZ_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (a c : (pqStageP p d b m r).Part S)
    (hpart : ∀ i, pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) =
      pqPartChunk b m p d r S a i)
    (hc : pqCompatibleZ b m p d r S J.1 c) :
    pqCompatibleZ b m p d r S (pqRelabelAlpha p d r E J).1 a := by
  classical
  rcases hc with ⟨x, hx, hjoint, hmarg⟩
  let y := pqPermutePart p d r E S x
  refine ⟨y, pqIncidence_relabel p d r E J S x hx, ?_, ?_⟩
  · intro gx gy gz σ hxy
    calc
      pqFineCount b m p d r S a
          (pqJointCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ =
          pqFineCount b m p d r S c
            (pqJointCell b m p d r J.1
              (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ :=
        pqFineCount_of_relabel p d r E S a c hpart _ _
          (pqJointCell_iff p d r E J _ _ _ gx gy gz) σ
      _ = pqFineCount b m p d r S x
            (pqJointCell b m p d r J.1
              (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ :=
        hjoint gx gy gz σ hxy
      _ = pqFineCount b m p d r S y
          (pqJointCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .X) (d.perm r .Y) (d.perm r .Z) gx gy gz) σ := by
        symm
        exact pqFineCount_of_relabel p d r E S y x
          (fun i => (pqPermutePart_chunk p d r E S x i).symm) _ _
          (pqJointCell_iff p d r E J _ _ _ gx gy gz) σ
  · intro gz σ
    calc
      pqFineCount b m p d r S a
          (pqMarginalCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .Z) gz) σ =
          pqFineCount b m p d r S c
            (pqMarginalCell b m p d r J.1 (d.perm r .Z) gz) σ :=
        pqFineCount_of_relabel p d r E S a c hpart _ _
          (pqMarginalCell_iff p d r E J _ gz) σ
      _ = pqFineCount b m p d r S x
            (pqMarginalCell b m p d r J.1 (d.perm r .Z) gz) σ := hmarg gz σ
      _ = pqFineCount b m p d r S y
          (pqMarginalCell b m p d r (pqRelabelAlpha p d r E J).1
            (d.perm r .Z) gz) σ := by
        symm
        exact pqFineCount_of_relabel p d r E S y x
          (fun i => (pqPermutePart_chunk p d r E S x i).symm) _ _
          (pqMarginalCell_iff p d r E J _ gz) σ

private theorem pqEncodedPositionPerm_symm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t))) :
    pqEncodedPositionPerm p d r (fun t => (E t).symm) =
      (pqEncodedPositionPerm p d r E).symm := by
  rfl

private theorem pqCompatibleY_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (a c : (pqStageP p d b m r).Part S)
    (hpart : ∀ i, pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) =
      pqPartChunk b m p d r S a i) :
    pqCompatibleY b m p d r S J.1 c ↔
      pqCompatibleY b m p d r S (pqRelabelAlpha p d r E J).1 a := by
  constructor
  · exact pqCompatibleY_forward p d r E J S a c hpart
  · intro ha
    let K := pqRelabelAlpha p d r E J
    have hpart' : ∀ i,
        pqPartChunk b m p d r S a
            (pqEncodedPositionPerm p d r (fun t => (E t).symm) i) =
          pqPartChunk b m p d r S c i := by
      intro i
      rw [pqEncodedPositionPerm_symm]
      have hi := hpart ((pqEncodedPositionPerm p d r E).symm i)
      rw [(pqEncodedPositionPerm p d r E).apply_symm_apply] at hi
      exact hi.symm
    have hback := pqCompatibleY_forward p d r (fun t => (E t).symm)
      K S c a hpart' ha
    simpa only [K, pqRelabelAlpha_symm] using hback

private theorem pqCompatibleZ_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : ∀ t : Fin s, Equiv.Perm (Fin (pqStageParentCount b m p d r t)))
    (J : AlphaLabel p d b m r) (S : Side)
    (a c : (pqStageP p d b m r).Part S)
    (hpart : ∀ i, pqPartChunk b m p d r S c (pqEncodedPositionPerm p d r E i) =
      pqPartChunk b m p d r S a i) :
    pqCompatibleZ b m p d r S J.1 c ↔
      pqCompatibleZ b m p d r S (pqRelabelAlpha p d r E J).1 a := by
  constructor
  · exact pqCompatibleZ_forward p d r E J S a c hpart
  · intro ha
    let K := pqRelabelAlpha p d r E J
    have hpart' : ∀ i,
        pqPartChunk b m p d r S a
            (pqEncodedPositionPerm p d r (fun t => (E t).symm) i) =
          pqPartChunk b m p d r S c i := by
      intro i
      rw [pqEncodedPositionPerm_symm]
      have hi := hpart ((pqEncodedPositionPerm p d r E).symm i)
      rw [(pqEncodedPositionPerm p d r E).apply_symm_apply] at hi
      exact hi.symm
    have hback := pqCompatibleZ_forward p d r (fun t => (E t).symm)
      K S c a hpart' ha
    simpa only [K, pqRelabelAlpha_symm] using hback

private theorem pqCompatibleForWhich_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a c : (pqStageP p d b m r).Part (pqSide d r which))
    (hLaw : pqEmpiricalLaw b m p d r (pqSide d r which) a =
      pqEmpiricalLaw b m p d r (pqSide d r which) c)
    (J : AlphaLabel p d b m r) :
    pqCompatibleForWhich b m p d r which J.1 c ↔
      pqCompatibleForWhich b m p d r which
        (pqRelabelAlpha p d r
          (pqPairPerm p d r (pqSide d r which) a c hLaw) J).1 a := by
  let E := pqPairPerm p d r (pqSide d r which) a c hLaw
  have hpart := pqPartChunk_forward p d r (pqSide d r which) a c hLaw
  by_cases hwhich : which = 0
  · simp only [pqCompatibleForWhich, if_pos hwhich]
    exact pqCompatibleY_iff p d r E J _ a c hpart
  · simp only [pqCompatibleForWhich, if_neg hwhich]
    exact pqCompatibleZ_iff p d r E J _ a c hpart

private theorem pqParentEmpirical_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r which)) :
    Parent25.empirical p d b m r which a =
      pqEmpiricalLaw b m p d r (pqSide d r which) a := by
  rfl

private theorem pqParentContains_iff_coarse {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (J : AlphaLabel p d b m r)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r which)) :
    Parent25.contains p d b m r which J.1 a ↔
      pqCoarseContains b m p d r (pqSide d r which) J.1 a := by
  classical
  constructor
  · intro h i
    generalize hz : (pqPositionEncoding p d r).symm i = z
    rcases z with ⟨t, ih⟩
    have hi : pqPositionEncoding p d r ⟨t, ih⟩ = i := by
      rw [← hz]
      exact (pqPositionEncoding p d r).apply_symm_apply i
    have hw := pqPartChunk_eq_word p d r (pqSide d r which) a i
    have hc := pqCoarse_at_encoding p d r J (pqSide d r which) t ih
    have hh := h ⟨t, ih⟩
    have hwI : pqPartChunk b m p d r (pqSide d r which) a i = a ⟨t, ih⟩ := by
      simpa only [hz] using hw
    have hcI : (pqStageP p d b m r).coarse J.1 (pqSide d r which) i =
        pqCoordFin (pqSide d r which) (pqAlphaShape p d r J t ih).1 := by
      simpa only [hi] using hc
    rw [hwI, hcI]
    rw [← pqSide_eq_parent d r which] at hh
    rw [pqCoordFin_val]
    simpa only [pqAlphaShape] using hh
  · intro h
    rintro ⟨t, ih⟩
    have hh := h (pqPositionEncoding p d r ⟨t, ih⟩)
    rw [pqPartChunk_eq_word, Equiv.symm_apply_apply,
      pqCoarse_at_encoding] at hh
    rw [pqCoordFin_val] at hh
    rw [← pqSide_eq_parent d r which]
    simpa only [pqAlphaShape] using hh

private theorem pqParentCellCount_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2)
    (a c : (Parent25.Pop p d b m r).Part (Parent25.side d r which))
    (hLaw : Parent25.empirical p d b m r which a =
      Parent25.empirical p d b m r which c)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (cell : Shape w → Prop) (σ : Chunk w) :
    Parent25.cellCount p d b m r which
        (pqRelabelAlpha p d r
          (pqPairPerm p d r (pqSide d r which) a c hLaw) J).1 a t cell σ =
      Parent25.cellCount p d b m r which J.1 c t cell σ := by
  classical
  unfold Parent25.cellCount
  let E := pqPairPerm p d r (pqSide d r which) a c hLaw
  have hcard := pq_filter_card_eq_of_perm (pqPositionPerm p d r E)
    (fun z : PQStagePos b m p d r =>
      z.1 = t ∧ cell ((pqRelabelAlpha p d r E J).1.1 z).1 ∧ a z = σ)
    (fun z : PQStagePos b m p d r =>
      z.1 = t ∧ cell (J.1.1 z).1 ∧ c z = σ)
    (fun z => by
      rcases z with ⟨t₀, i, h⟩
      change (t₀ = t ∧ cell ((pqRelabelAlpha p d r E J).1.1
          ⟨t₀, (i, h)⟩).1 ∧ a ⟨t₀, (i, h)⟩ = σ) ↔
        (t₀ = t ∧ cell (J.1.1 ⟨t₀, (E t₀ i, h)⟩).1 ∧
          c ⟨t₀, (E t₀ i, h)⟩ = σ)
      have hw := pqPairPerm_half_spec p d r (pqSide d r which)
        a c hLaw t₀ i h
      have hwRaw : c ⟨t₀, (E t₀ i, h)⟩ = a ⟨t₀, (i, h)⟩ := by
        simpa only [E, pqStageWord] using hw
      simp only [pqPositionPerm, pqRowHalfPerm,
        pqRelabelAlpha_shape, pqRelabelShape]
      rw [hwRaw])
  exact hcard

private theorem pqParentCompatible_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2)
    (a c : (Parent25.Pop p d b m r).Part (Parent25.side d r which))
    (hLaw : Parent25.empirical p d b m r which a =
      Parent25.empirical p d b m r which c)
    (J : AlphaLabel p d b m r) :
    Parent25.compatible p d b m r which J.1 c ↔
      Parent25.compatible p d b m r which
        (pqRelabelAlpha p d r
          (pqPairPerm p d r (pqSide d r which) a c hLaw) J).1 a := by
  constructor
  · rintro ⟨hboundary, hmarginal⟩
    constructor
    · intro t u hu σ
      exact (pqParentCellCount_eq p d r which a c hLaw J t
        (fun v => v = u.val) σ).trans (hboundary t u hu σ)
    · intro t k σ
      exact (pqParentCellCount_eq p d r which a c hLaw J t
        (fun u => coord (Parent25.side d r which) u = k.val) σ).trans
          (hmarginal t k σ)
  · rintro ⟨hboundary, hmarginal⟩
    constructor
    · intro t u hu σ
      exact (pqParentCellCount_eq p d r which a c hLaw J t
        (fun v => v = u.val) σ).symm.trans (hboundary t u hu σ)
    · intro t k σ
      exact (pqParentCellCount_eq p d r which a c hLaw J t
        (fun u => coord (Parent25.side d r which) u = k.val) σ).symm.trans
          (hmarginal t k σ)

private noncomputable def pqIncidentLabels {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a : (pqStageP p d b m r).Part (pqSide d r which)) :
    Finset (AlphaLabel p d b m r) := by
  classical
  exact Finset.univ.filter fun J =>
    Parent25.contains p d b m r which J.1 a

private noncomputable def pqCompatibleLabels {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a : (pqStageP p d b m r).Part (pqSide d r which)) :
    Finset (AlphaLabel p d b m r) := by
  classical
  exact (pqIncidentLabels p d r which a).filter fun J =>
    Parent25.compatible p d b m r which J.1 a

private theorem pqIncidentLabels_card_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a c : (pqStageP p d b m r).Part (pqSide d r which))
    (hLaw : pqEmpiricalLaw b m p d r (pqSide d r which) a =
      pqEmpiricalLaw b m p d r (pqSide d r which) c) :
    (pqIncidentLabels p d r which c).card =
      (pqIncidentLabels p d r which a).card := by
  classical
  let E := pqPairPerm p d r (pqSide d r which) a c hLaw
  unfold pqIncidentLabels
  exact pq_filter_card_eq_of_perm (pqRelabelAlphaEquiv p d r E)
    (fun J => Parent25.contains p d b m r which J.1 c)
    (fun J => Parent25.contains p d b m r which J.1 a)
    (fun J => by
      exact (pqParentContains_iff_coarse p d r which J c).trans
        ((pqCoarseContains_iff p d r _ a c hLaw J).trans
          (pqParentContains_iff_coarse p d r which
            (pqRelabelAlpha p d r E J) a).symm))

private theorem pqCompatibleLabels_card_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a c : (pqStageP p d b m r).Part (pqSide d r which))
    (hLaw : pqEmpiricalLaw b m p d r (pqSide d r which) a =
      pqEmpiricalLaw b m p d r (pqSide d r which) c) :
    (pqCompatibleLabels p d r which c).card =
      (pqCompatibleLabels p d r which a).card := by
  classical
  let E := pqPairPerm p d r (pqSide d r which) a c hLaw
  simp only [pqCompatibleLabels, pqIncidentLabels, Finset.filter_filter]
  exact pq_filter_card_eq_of_perm (pqRelabelAlphaEquiv p d r E)
    (fun J => Parent25.contains p d b m r which J.1 c ∧
      Parent25.compatible p d b m r which J.1 c)
    (fun J => Parent25.contains p d b m r which J.1 a ∧
      Parent25.compatible p d b m r which J.1 a)
    (fun J => and_congr
      ((pqParentContains_iff_coarse p d r which J c).trans
        ((pqCoarseContains_iff p d r _ a c hLaw J).trans
          (pqParentContains_iff_coarse p d r which
            (pqRelabelAlpha p d r E J) a).symm))
      (pqParentCompatible_iff p d r which a c hLaw J))

private theorem pq_card_filter_prod_eq {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (P : A → X → Prop) (B : X → Prop)
    [DecidablePred B] [∀ x, DecidablePred (P · x)] (c : ℕ)
    (hcard : ∀ x, B x → (Finset.univ.filter fun a => P a x).card = c) :
    (Finset.univ.filter fun z : A × X => P z.1 z.2 ∧ B z.2).card =
      (Finset.univ.filter B).card * c := by
  classical
  let e : {z : A × X // P z.1 z.2 ∧ B z.2} ≃
      (x : {x : X // B x}) × {a : A // P a x.1} :=
    { toFun := fun z => ⟨⟨z.1.2, z.2.2⟩, ⟨z.1.1, z.2.1⟩⟩
      invFun := fun z => ⟨(z.2.1, z.1.1), z.2.2, z.1.2⟩
      left_inv := fun z => by rfl
      right_inv := fun z => by rfl }
  calc
    (Finset.univ.filter fun z : A × X => P z.1 z.2 ∧ B z.2).card =
        Fintype.card {z : A × X // P z.1 z.2 ∧ B z.2} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card ((x : {x : X // B x}) × {a : A // P a x.1}) :=
      Fintype.card_congr e
    _ = ∑ x : {x : X // B x}, Fintype.card {a : A // P a x.1} :=
      Fintype.card_sigma
    _ = ∑ _x : {x : X // B x}, c := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.card_subtype]
      exact hcard x.1 x.2
    _ = Fintype.card {x : X // B x} * c := by simp
    _ = (Finset.univ.filter B).card * c := by rw [Fintype.card_subtype]

private abbrev PQLawSample {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (S : Side) :=
  AlphaLabel p d b m r × (pqStageP p d b m r).Part S

private noncomputable def pqContainingSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (r : Fin 6) (S : Side) : Finset (PQLawSample p d b m r S) := by
  classical
  exact Finset.univ.filter fun z => pqCoarseContains b m p d r S z.1.1 z.2

private noncomputable def pqLawSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    Finset (PQLawSample p d b m r (pqSide d r which)) := by
  classical
  exact Finset.univ.filter fun z =>
    Parent25.contains p d b m r which z.1.1 z.2 ∧
      Parent25.empirical p d b m r which z.2 = β.1

private noncomputable def pqFirstLawSample {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    PQLawSample p d b m r (pqSide d r which) := by
  classical
  let candidates := pqLawSamples p d b ε m r which β
  have hcandidates : candidates.Nonempty := by
    have hmem := β.2
    change β.1 ∈ _ at hmem
    have himage := (Finset.mem_filter.mp hmem).1
    rcases Finset.mem_image.mp himage with ⟨z, hz, hzeq⟩
    have hzContains : Parent25.contains p d b m r which z.1.1 z.2 :=
      (pqParentContains_iff_coarse p d r which z.1 z.2).mpr
        (Finset.mem_filter.mp hz).2
    have hzLaw : Parent25.empirical p d b m r which z.2 = β.1 := by
      rw [pqParentEmpirical_eq]
      exact hzeq
    exact ⟨z, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hzContains, hzLaw⟩⟩
  let e := Fintype.equivFin (PQLawSample p d b m r (pqSide d r which))
  let codes := candidates.image e
  let hcodes : codes.Nonempty := hcandidates.image e
  exact e.symm (codes.min' hcodes)

private noncomputable def pqCompatibilityRatioAtWord {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (a : (pqStageP p d b m r).Part (pqSide d r which)) : ℝ := by
  classical
  let incident := (Finset.univ : Finset (AlphaLabel p d b m r)).filter fun K =>
    Parent25.contains p d b m r which K.1 a
  let compatible := incident.filter fun K =>
    Parent25.compatible p d b m r which K.1 a
  exact (compatible.card : ℝ) / incident.card

private theorem pqLawSamples_nonempty {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) :
    (pqLawSamples p d b ε m r which β).Nonempty := by
  classical
  have hmem := β.2
  change β.1 ∈ _ at hmem
  have himage := (Finset.mem_filter.mp hmem).1
  rcases Finset.mem_image.mp himage with ⟨z, hz, hzeq⟩
  have hzContains : Parent25.contains p d b m r which z.1.1 z.2 :=
    (pqParentContains_iff_coarse p d r which z.1 z.2).mpr
      (Finset.mem_filter.mp hz).2
  have hzLaw : Parent25.empirical p d b m r which z.2 = β.1 := by
    rw [pqParentEmpirical_eq]
    exact hzeq
  exact ⟨z, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hzContains, hzLaw⟩⟩

private theorem pqFirstLawSample_mem {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) :
    pqFirstLawSample p d b ε m r which β ∈ pqLawSamples p d b ε m r which β := by
  classical
  let candidates := pqLawSamples p d b ε m r which β
  let e := Fintype.equivFin (PQLawSample p d b m r (pqSide d r which))
  let codes := candidates.image e
  let hcodes : codes.Nonempty := (pqLawSamples_nonempty p d b ε m r which β).image e
  change e.symm (codes.min' hcodes) ∈ candidates
  have hmin : codes.min' hcodes ∈ codes := Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmin with ⟨z, hz, heq⟩
  have : e.symm (codes.min' hcodes) = z := by
    rw [← heq, Equiv.symm_apply_apply]
  rwa [this]

private noncomputable def pqParentFirstLawSample {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    {z : AlphaLabel p d b m r ×
        (Parent25.Pop p d b m r).Part (Parent25.side d r which) //
      Parent25.contains p d b m r which z.1.1 z.2 ∧
        Parent25.empirical p d b m r which z.2 = β.1} := by
  classical
  let Ω := AlphaLabel p d b m r ×
    (Parent25.Pop p d b m r).Part (Parent25.side d r which)
  letI : Fintype Ω := Fintype.ofFinite Ω
  let samples := (Finset.univ : Finset Ω).filter fun z =>
    Parent25.contains p d b m r which z.1.1 z.2 ∧
      Parent25.empirical p d b m r which z.2 = β.1
  have hs : samples.Nonempty := by
    rcases pqLawSamples_nonempty p d b ε m r which β with ⟨z, hz⟩
    exact ⟨z, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩⟩
  let e := Fintype.equivFin Ω
  let codes := samples.image e
  let hcodes : codes.Nonempty := hs.image e
  let z := e.symm (codes.min' hcodes)
  refine ⟨z, ?_⟩
  have hmin : codes.min' hcodes ∈ codes := Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmin with ⟨y, hy, heq⟩
  have hzy : z = y := by
    simp only [z]
    rw [← heq, Equiv.symm_apply_apply]
  rw [hzy]
  exact (Finset.mem_filter.mp hy).2

private theorem pqLawSamples_card_factor {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (which : Fin 2) (β : RepresentedLaw p d b ε m r which) :
    (pqLawSamples p d b ε m r which β).card =
      (Finset.univ.filter fun a : (pqStageP p d b m r).Part (pqSide d r which) =>
        pqEmpiricalLaw b m p d r (pqSide d r which) a = β.1).card *
      (pqIncidentLabels p d r which
        (pqFirstLawSample p d b ε m r which β).2).card := by
  classical
  let a := (pqFirstLawSample p d b ε m r which β).2
  have haMem := pqFirstLawSample_mem p d b ε m r which β
  have haLaw : Parent25.empirical p d b m r which a = β.1 :=
    (Finset.mem_filter.mp haMem).2.2
  have hcard := pq_card_filter_prod_eq
    (fun J : AlphaLabel p d b m r => fun x =>
      Parent25.contains p d b m r which J.1 x)
    (fun x => Parent25.empirical p d b m r which x = β.1)
    (pqIncidentLabels p d r which a).card
    (fun x hx => pqIncidentLabels_card_eq p d r which a x (haLaw.trans hx.symm))
  simpa only [a, pqLawSamples, pqIncidentLabels, Finset.filter_filter,
    and_left_comm, and_assoc, and_comm] using hcard

private noncomputable def pqCompatibleLawSamples {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    Finset (PQLawSample p d b m r (pqSide d r which)) := by
  classical
  exact (pqLawSamples p d b ε m r which β).filter fun z =>
    Parent25.compatible p d b m r which z.1.1 z.2

private theorem pqCompatibleSamples_card_factor {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (which : Fin 2)
    (β : RepresentedLaw p d b ε m r which) :
    (pqCompatibleLawSamples p d b ε m r which β).card =
      (Finset.univ.filter fun a : (pqStageP p d b m r).Part (pqSide d r which) =>
        pqEmpiricalLaw b m p d r (pqSide d r which) a = β.1).card *
      (pqCompatibleLabels p d r which
        (pqFirstLawSample p d b ε m r which β).2).card := by
  classical
  let a := (pqFirstLawSample p d b ε m r which β).2
  have haMem := pqFirstLawSample_mem p d b ε m r which β
  have haLaw : Parent25.empirical p d b m r which a = β.1 :=
    (Finset.mem_filter.mp haMem).2.2
  have hcard := pq_card_filter_prod_eq
    (fun J : AlphaLabel p d b m r => fun x =>
      Parent25.contains p d b m r which J.1 x ∧
        Parent25.compatible p d b m r which J.1 x)
    (fun x => Parent25.empirical p d b m r which x = β.1)
    (pqCompatibleLabels p d r which a).card
    (fun x hx => by
      simpa only [pqCompatibleLabels, pqIncidentLabels, Finset.filter_filter] using
        pqCompatibleLabels_card_eq p d r which a x (haLaw.trans hx.symm))
  simpa only [a, pqCompatibleLawSamples, pqLawSamples, pqCompatibleLabels,
    pqIncidentLabels, Finset.filter_filter, and_left_comm, and_assoc, and_comm] using hcard

private theorem pqParentJointP_eq {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    Parent25.jointP p d b ε m r W β =
      ((pqLawSamples p d b ε m r W β).card : ℝ) /
        Fintype.card (PQLawSample p d b m r (pqSide d r W)) := by
  classical
  unfold Parent25.jointP
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

private theorem pqParentJointQ_eq {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    Parent25.jointQ p d b ε m r W β =
      ((pqCompatibleLawSamples p d b ε m r W β).card : ℝ) /
        Fintype.card (PQLawSample p d b m r (pqSide d r W)) := by
  classical
  unfold Parent25.jointQ
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [pqCompatibleLawSamples, pqLawSamples, Finset.filter_filter]
  apply congrArg (fun S : Finset _ => (S.card : ℝ) / _)
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

private theorem compatibility_jointP_parent25_pos {w s b : ℕ}
    (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) :
    0 < Parent25.jointP p d b ε m r W β := by
  classical
  rw [pqParentJointP_eq]
  apply div_pos
  · exact_mod_cast Finset.card_pos.mpr (pqLawSamples_nonempty p d b ε m r W β)
  · exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(pqLawSamples_nonempty p d b ε m r W β).choose⟩

theorem compatibility_quotient_parent40 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) :
  0 < Parent25.jointP p d b ε m r W β ∧
    Parent25.pcomp p d b ε m r W β =
      Parent25.jointQ p d b ε m r W β / Parent25.jointP p d b ε m r W β := by
  constructor
  · exact compatibility_jointP_parent25_pos p d hd m hb ε r W β
  · classical
    let a := (pqFirstLawSample p d b ε m r W β).2
    let aP := (pqParentFirstLawSample p d b ε m r W β).1.2
    let words := (Finset.univ.filter fun x :
      (pqStageP p d b m r).Part (pqSide d r W) =>
        Parent25.empirical p d b m r W x = β.1)
    let incident := pqIncidentLabels p d r W a
    let compatible := pqCompatibleLabels p d r W a
    let total := Fintype.card (PQLawSample p d b m r (pqSide d r W))
    have haMem := pqFirstLawSample_mem p d b ε m r W β
    have haLaw : Parent25.empirical p d b m r W a = β.1 :=
      (Finset.mem_filter.mp haMem).2.2
    have haPLaw : Parent25.empirical p d b m r W aP = β.1 :=
      (pqParentFirstLawSample p d b ε m r W β).2.2
    have haCoarse : Parent25.contains p d b m r W
        (pqFirstLawSample p d b ε m r W β).1.1 a :=
      (Finset.mem_filter.mp haMem).2.1
    have hwordsNat : 0 < words.card := Finset.card_pos.mpr ⟨a, by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haLaw⟩⟩
    have hincidentNat : 0 < incident.card := Finset.card_pos.mpr
      ⟨(pqFirstLawSample p d b ε m r W β).1, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haCoarse⟩⟩
    have htotalNat : 0 < total := Fintype.card_pos_iff.mpr
      ⟨pqFirstLawSample p d b ε m r W β⟩
    have hwords : (words.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hwordsNat
    have hincident : (incident.card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hincidentNat
    have htotal : (total : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt htotalNat
    have hincidentRep : (pqIncidentLabels p d r W aP).card = incident.card := by
      exact pqIncidentLabels_card_eq p d r W a aP (haLaw.trans haPLaw.symm)
    have hcompatibleRep : (pqCompatibleLabels p d r W aP).card = compatible.card := by
      exact pqCompatibleLabels_card_eq p d r W a aP (haLaw.trans haPLaw.symm)
    rw [pqParentJointP_eq, pqParentJointQ_eq]
    let Ω := AlphaLabel p d b m r ×
      (Parent25.Pop p d b m r).Part (Parent25.side d r W)
    letI : Fintype Ω := Fintype.ofFinite Ω
    unfold Parent25.pcomp
    dsimp only
    split
    · change pqCompatibilityRatioAtWord b m p d r W aP =
        ((pqCompatibleLawSamples p d b ε m r W β).card : ℝ) / total /
          (((pqLawSamples p d b ε m r W β).card : ℝ) / total)
      unfold pqCompatibilityRatioAtWord
      dsimp only
      change ((pqCompatibleLabels p d r W aP).card : ℝ) /
          (pqIncidentLabels p d r W aP).card = _
      rw [hincidentRep, hcompatibleRep]
      rw [pqLawSamples_card_factor, pqCompatibleSamples_card_factor]
      change (compatible.card : ℝ) / incident.card =
        ((words.card * compatible.card : ℕ) : ℝ) / total /
          (((words.card * incident.card : ℕ) : ℝ) / total)
      push_cast
      field_simp
    · rename_i hs
      apply (hs ?_).elim
      exact ⟨(pqParentFirstLawSample p d b ε m r W β).1,
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (pqParentFirstLawSample p d b ε m r W β).2⟩⟩

/-- Every exact-alpha label has the prescribed first-half child-shape histogram. -/
theorem parent25_alphaLabel_target_count40 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    (Finset.univ.filter fun i : Fin (Parent25.parentCount p d b m r t) =>
      J.val.val ⟨t, i, 0⟩ = u).card = Parent25.alphaCount p d b m r t u := by
  classical
  simpa only [pqHistogram, pqAlphaZero, pqAlphaShape, pqStageAlphaCount,
    Parent25.alphaCount, Parent25.parentCount] using
      pqAlphaLabel_target p d r J t u

/-- The second child shape at every exact-alpha occurrence is the complement of the first. -/
theorem parent25_alphaLabel_complementary40 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (Parent25.parentCount p d b m r t)) :
    J.val.val ⟨t, i, 1⟩ = complement p t (J.val.val ⟨t, i, 0⟩) := by
  exact J.val.property.2 t i

/-- A represented law comes with an actual corrected containing sample realizing it. -/
theorem parent25_representedLaw_witness40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    ∃ (J : AlphaLabel p d b m r)
      (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W)),
      Parent25.contains p d b m r W J.val a ∧
        Parent25.empirical p d b m r W a = β.val := by
  classical
  rcases pqLawSamples_nonempty p d b ε m r W β with ⟨z, hz⟩
  exact ⟨z.1, z.2, (Finset.mem_filter.mp hz).2⟩

end OmegaBound.ADVXXZGeneral
end
