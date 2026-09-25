import OmegaBound.ADVXXZGeneralAmend25Parent

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def realizeAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def realizeParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, realizeAlphaCount b m p d r t u

private abbrev RealizePos {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (realizeParentCount b m p d r t) × Fin 2)

private irreducible_def alphaShape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) : ChildShape p t :=
  J.1.1 ⟨t, ih⟩

private irreducible_def alphaZero {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (realizeParentCount b m p d r t)) : ChildShape p t :=
  alphaShape p d r J t (i, ⟨0, by omega⟩)

private def histogram {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (f : I → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => f i = a).card

private theorem exists_perm_of_histogram {I A : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq A] (f g : I → A)
    (h : ∀ a, histogram f a = histogram g a) :
    ∃ e : Equiv.Perm I, ∀ i, g (e i) = f i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // f i = a} ≃ {i // g i = a}) :=
    ⟨fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), fun i => ?_⟩
  exact (e (f i) ⟨i, rfl⟩).2

private noncomputable def matchingPerm {I A : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq A] (f g : I → A)
    (h : ∀ a, histogram f a = histogram g a) : Equiv.Perm I :=
  Classical.choose (exists_perm_of_histogram f g h)

private theorem matchingPerm_spec {I A : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq A] (f g : I → A)
    (h : ∀ a, histogram f a = histogram g a) (i : I) :
    g (matchingPerm f g h i) = f i :=
  Classical.choose_spec (exists_perm_of_histogram f g h) i

private theorem alphaLabel_target {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t) :
    histogram (alphaZero p d r J t) u =
      realizeAlphaCount b m p d r t u := by
  classical
  have hJ : J.1 ∈ (stagePopulationAt 0 p d b m r).target := J.2
  have h := (Finset.mem_filter.mp hJ).2 t u
  simpa only [histogram, alphaZero, alphaShape, realizeAlphaCount] using h

private theorem alphaLabel_complementary {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (realizeParentCount b m p d r t)) :
    alphaShape p d r J t (i, ⟨1, by omega⟩) =
      complement p t (alphaShape p d r J t (i, ⟨0, by omega⟩)) := by
  simpa only [alphaShape] using J.1.2.2 t i

private theorem alphaLabels_same_target {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s) :
    ∀ u : ChildShape p t,
      histogram (alphaZero p d r J t) u =
        histogram (alphaZero p d r K t) u := by
  intro u
  exact (alphaLabel_target p d r J t u).trans
    (alphaLabel_target p d r K t u).symm

set_option maxHeartbeats 1000000 in
-- The reducible population carrier needs extra elaboration budget at this opaque boundary.
private noncomputable def rowPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s) :
    Equiv.Perm (Fin (realizeParentCount b m p d r t)) :=
  matchingPerm (alphaZero p d r J t) (alphaZero p d r K t)
    (alphaLabels_same_target p d r J K t)

set_option maxHeartbeats 1000000 in
-- Its specification elaborates against the same dependent carrier as `rowPerm`.
private theorem rowPerm_spec {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s)
    (i : Fin (realizeParentCount b m p d r t)) :
    alphaZero p d r K t (rowPerm p d r J K t i) =
      alphaZero p d r J t i :=
  matchingPerm_spec (alphaZero p d r J t) (alphaZero p d r K t)
    (alphaLabels_same_target p d r J K t) i

private noncomputable def rowHalfPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s) :
    Equiv.Perm (Fin (realizeParentCount b m p d r t) × Fin 2) :=
  Equiv.prodCongr (rowPerm p d r J K t) (Equiv.refl _)

private noncomputable def positionPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) :
    Equiv.Perm (RealizePos b m p d r) :=
  Equiv.sigmaCongrRight (rowHalfPerm p d r J K)

private theorem rowHalfPerm_spec {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    alphaShape p d r K t (rowHalfPerm p d r J K t ih) =
      alphaShape p d r J t ih := by
  rcases ih with ⟨i, h⟩
  fin_cases h
  · simpa only [rowHalfPerm, alphaZero] using rowPerm_spec p d r J K t i
  · calc
      alphaShape p d r K t
          (rowPerm p d r J K t i, ⟨1, by omega⟩) =
          complement p t
            (alphaShape p d r K t
              (rowPerm p d r J K t i, ⟨0, by omega⟩)) :=
        alphaLabel_complementary p d r K t _
      _ = complement p t
          (alphaShape p d r J t (i, ⟨0, by omega⟩)) :=
        congrArg (complement p t) (by
          simpa only [alphaZero] using rowPerm_spec p d r J K t i)
      _ = alphaShape p d r J t (i, ⟨1, by omega⟩) :=
        (alphaLabel_complementary p d r J t i).symm

private theorem rowHalfPerm_symm_spec {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    alphaShape p d r K t ih =
      alphaShape p d r J t ((rowHalfPerm p d r J K t).symm ih) := by
  calc
    alphaShape p d r K t ih = alphaShape p d r K t
        (rowHalfPerm p d r J K t
          ((rowHalfPerm p d r J K t).symm ih)) :=
      congrArg (alphaShape p d r K t)
        ((rowHalfPerm p d r J K t).apply_symm_apply ih).symm
    _ = alphaShape p d r J t ((rowHalfPerm p d r J K t).symm ih) :=
      rowHalfPerm_spec p d r J K t _

private theorem filter_card_eq_of_perm {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ i, P i ↔ Q (e i)) :
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

private noncomputable def ambientPartEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side) :
    (stagePopulationAt 0 p d b m r).Part W ≃
      (stagePopulationAt 0 p d b m r).Part W := by
  classical
  dsimp only [stagePopulationAt]
  let e := positionPerm p d r J K
  exact
    { toFun := fun x a => x (e.symm a)
      invFun := fun x a => x (e a)
      left_inv := fun x => by
        funext a
        exact congrArg x (e.symm_apply_apply a)
      right_inv := fun x => by
        funext a
        exact congrArg x (e.apply_symm_apply a) }

private theorem ambientPartEquiv_apply {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    ambientPartEquiv p d r J K W x ⟨t, rowHalfPerm p d r J K t ih⟩ =
      x ⟨t, ih⟩ := by
  change x ((positionPerm p d r J K).symm
    ⟨t, rowHalfPerm p d r J K t ih⟩) = x ⟨t, ih⟩
  rw [show ⟨t, rowHalfPerm p d r J K t ih⟩ =
      positionPerm p d r J K ⟨t, ih⟩ by rfl,
    Equiv.symm_apply_apply]

private theorem ambientPartEquiv_symm_apply {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    (ambientPartEquiv p d r J K W).symm x ⟨t, ih⟩ =
      x ⟨t, rowHalfPerm p d r J K t ih⟩ := by
  rfl

private theorem incidence_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W)
    (hx : (stagePopulationAt 0 p d b m r).incidence W J.1 x) :
    (stagePopulationAt 0 p d b m r).incidence W K.1
      (ambientPartEquiv p d r J K W x) := by
  classical
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl (ambientPartEquiv p d r J K W x a) = coord W (K.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        K.1.1 ⟨t, ih⟩ = u ∧
          ambientPartEquiv p d r J K W x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl (x a) = coord W (J.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        J.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat at hx
  refine ⟨?_, ?_⟩
  · rintro ⟨t, ih⟩
    let ih₀ := (rowHalfPerm p d r J K t).symm ih
    have hshape := rowHalfPerm_symm_spec p d r J K t ih
    have hshapeRaw : K.1.1 ⟨t, ih⟩ = J.1.1 ⟨t, ih₀⟩ := by
      simpa only [ih₀, alphaShape] using hshape
    have hword := ambientPartEquiv_apply p d r J K W x t ih₀
    have hlevel := hx.1 ⟨t, ih₀⟩
    simp only [ih₀, Equiv.apply_symm_apply] at hword
    rw [hword, hshapeRaw]
    exact hlevel
  · intro t u σ
    have hcard := filter_card_eq_of_perm (rowHalfPerm p d r J K t)
      (fun ih => J.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)
      (fun ih => K.1.1 ⟨t, ih⟩ = u ∧
        ambientPartEquiv p d r J K W x ⟨t, ih⟩ = σ)
      (fun ih => by
        change (J.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ) ↔
          (K.1.1 ⟨t, rowHalfPerm p d r J K t ih⟩ = u ∧
            ambientPartEquiv p d r J K W x
              ⟨t, rowHalfPerm p d r J K t ih⟩ = σ)
        have hs := rowHalfPerm_spec p d r J K t ih
        have hsRaw : K.1.1 ⟨t, rowHalfPerm p d r J K t ih⟩ =
            J.1.1 ⟨t, ih⟩ := by
          simpa only [alphaShape] using hs
        rw [hsRaw, ambientPartEquiv_apply p d r J K W x t ih])
    exact hcard.symm.trans (hx.2 t u σ)

private theorem incidence_backward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W)
    (hx : (stagePopulationAt 0 p d b m r).incidence W K.1 x) :
    (stagePopulationAt 0 p d b m r).incidence W J.1
      ((ambientPartEquiv p d r J K W).symm x) := by
  classical
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl ((ambientPartEquiv p d r J K W).symm x a) =
        coord W (J.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        J.1.1 ⟨t, ih⟩ = u ∧
          (ambientPartEquiv p d r J K W).symm x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl (x a) = coord W (K.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        K.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat at hx
  refine ⟨?_, ?_⟩
  · rintro ⟨t, ih⟩
    have hs := rowHalfPerm_spec p d r J K t ih
    have hsRaw : K.1.1 ⟨t, rowHalfPerm p d r J K t ih⟩ =
        J.1.1 ⟨t, ih⟩ := by
      simpa only [alphaShape] using hs
    rw [ambientPartEquiv_symm_apply p d r J K W x t ih, ← hsRaw]
    exact hx.1 ⟨t, rowHalfPerm p d r J K t ih⟩
  · intro t u σ
    have hcard := filter_card_eq_of_perm (rowHalfPerm p d r J K t)
      (fun ih => J.1.1 ⟨t, ih⟩ = u ∧
        (ambientPartEquiv p d r J K W).symm x ⟨t, ih⟩ = σ)
      (fun ih => K.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)
      (fun ih => by
        change (J.1.1 ⟨t, ih⟩ = u ∧
            (ambientPartEquiv p d r J K W).symm x ⟨t, ih⟩ = σ) ↔
          (K.1.1 ⟨t, rowHalfPerm p d r J K t ih⟩ = u ∧
            x ⟨t, rowHalfPerm p d r J K t ih⟩ = σ)
        have hs := rowHalfPerm_spec p d r J K t ih
        have hsRaw : K.1.1 ⟨t, rowHalfPerm p d r J K t ih⟩ =
            J.1.1 ⟨t, ih⟩ := by
          simpa only [alphaShape] using hs
        rw [hsRaw, ambientPartEquiv_symm_apply p d r J K W x t ih])
    exact hcard.trans (hx.2 t u σ)


private noncomputable def representedPartsEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side) :
    RepresentedParts p d b m J W ≃ RepresentedParts p d b m K W := by
  classical
  let E := ambientPartEquiv p d r J K W
  refine
    { toFun := fun x => ⟨E x.1, ?_⟩
      invFun := fun x => ⟨E.symm x.1, ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact E.left_inv x.1
      right_inv := fun x => by
        apply Subtype.ext
        exact E.right_inv x.1 }
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, incidence_forward p d r J K W x.1 ?_⟩
    exact (Finset.mem_filter.mp x.2).2
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, incidence_backward p d r J K W x.1 ?_⟩
    exact (Finset.mem_filter.mp x.2).2

private def realizeCoordFin {w : ℕ} (W : Side) (u : Shape w) :
    Fin (2 * w + 1) :=
  match W with
  | .X => u.1.1
  | .Y => u.1.2.1
  | .Z => u.1.2.2

private theorem alphaLabel_marginal {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (L : AlphaLabel p d b m r) (t : Fin s) (h : Fin 2)
    (W : Side) (a : Fin (2 * w + 1)) :
    histogram (fun i : Fin (realizeParentCount b m p d r t) =>
      realizeCoordFin W (alphaShape p d r L t (i, h)).1) a =
      ∑ u : ChildShape p t,
        if realizeCoordFin W ((if h = 0 then u else complement p t u).1) = a
        then realizeAlphaCount b m p d r t u else 0 := by
  classical
  have hL := L.1.2.1 t h W a
  simpa only [histogram, alphaShape, realizeCoordFin, realizeAlphaCount] using hL

private noncomputable irreducible_def relabelShape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) :
    (a : RealizePos b m p d r) → ChildShape p a.1 :=
  fun a => match a with
  | ⟨t, ih⟩ => alphaShape p d r L t ((rowHalfPerm p d r J K t).symm ih)

private theorem relabelShape_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    relabelShape p d r J K L ⟨t, rowHalfPerm p d r J K t ih⟩ =
      alphaShape p d r L t ih := by
  rw [relabelShape]
  exact congrArg (alphaShape p d r L t)
    ((rowHalfPerm p d r J K t).symm_apply_apply ih)

set_option maxHeartbeats 1000000 in
-- Constructing the nested target/label subtype unfolds the population carrier once.
private noncomputable def relabelAlpha {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) : AlphaLabel p d b m r := by
  classical
  unfold AlphaLabel
  refine ⟨⟨relabelShape p d r J K L, ?_, ?_⟩, ?_⟩
  · intro t h W a
    have hm := alphaLabel_marginal p d r L t h W a
    have hcard := filter_card_eq_of_perm (rowPerm p d r J K t)
      (fun i => realizeCoordFin W (alphaShape p d r L t (i, h)).1 = a)
      (fun i => realizeCoordFin W
        (relabelShape p d r J K L ⟨t, (i, h)⟩).1 = a)
      (fun i => by
        change (realizeCoordFin W (alphaShape p d r L t (i, h)).1 = a) ↔
          (realizeCoordFin W
            (relabelShape p d r J K L
              ⟨t, (rowPerm p d r J K t i, h)⟩).1 = a)
        rw [show (rowPerm p d r J K t i, h) =
            rowHalfPerm p d r J K t (i, h) by rfl,
          relabelShape_forward p d r J K L t (i, h)])
    exact hcard.symm.trans hm
  · intro t i
    change relabelShape p d r J K L ⟨t, (i, ⟨1, by omega⟩)⟩ =
      complement p t
        (relabelShape p d r J K L ⟨t, (i, ⟨0, by omega⟩)⟩)
    simp only [relabelShape, rowHalfPerm]
    exact alphaLabel_complementary p d r L t
      ((rowPerm p d r J K t).symm i)
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t u
    have ht := alphaLabel_target p d r L t u
    have hcard := filter_card_eq_of_perm (rowPerm p d r J K t)
      (fun i => alphaShape p d r L t (i, ⟨0, by omega⟩) = u)
      (fun i => relabelShape p d r J K L
        ⟨t, (i, ⟨0, by omega⟩)⟩ = u)
      (fun i => by
        change (alphaShape p d r L t (i, ⟨0, by omega⟩) = u) ↔
          (relabelShape p d r J K L
            ⟨t, (rowPerm p d r J K t i, ⟨0, by omega⟩)⟩ = u)
        rw [show (rowPerm p d r J K t i, ⟨0, by omega⟩) =
            rowHalfPerm p d r J K t (i, ⟨0, by omega⟩) by rfl,
          relabelShape_forward p d r J K L t (i, ⟨0, by omega⟩)])
    have ht' :
        (Finset.univ.filter (fun i :
            Fin (realizeParentCount b m p d r t) =>
          alphaShape p d r L t (i, ⟨0, by omega⟩) = u)).card =
          realizeAlphaCount b m p d r t u := by
      simpa only [histogram, alphaZero] using ht
    exact hcard.symm.trans ht'

private theorem relabelAlpha_shape {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    alphaShape p d r (relabelAlpha p d r J K L) t ih =
      relabelShape p d r J K L ⟨t, ih⟩ := by
  simp only [alphaShape, relabelAlpha, id_eq]

private theorem relabelAlpha_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    alphaShape p d r (relabelAlpha p d r J K L) t
        (rowHalfPerm p d r J K t ih) =
      alphaShape p d r L t ih := by
  rw [relabelAlpha_shape, relabelShape_forward]

private theorem relabelAlpha_symm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (t : Fin s)
    (ih : Fin (realizeParentCount b m p d r t) × Fin 2) :
    alphaShape p d r (relabelAlpha p d r J K L) t ih =
      alphaShape p d r L t ((rowHalfPerm p d r J K t).symm ih) := by
  calc
    alphaShape p d r (relabelAlpha p d r J K L) t ih =
        alphaShape p d r (relabelAlpha p d r J K L) t
          (rowHalfPerm p d r J K t
            ((rowHalfPerm p d r J K t).symm ih)) :=
      congrArg (alphaShape p d r (relabelAlpha p d r J K L) t)
        ((rowHalfPerm p d r J K t).apply_symm_apply ih).symm
    _ = alphaShape p d r L t ((rowHalfPerm p d r J K t).symm ih) :=
      relabelAlpha_forward p d r J K L t _

private theorem relabelAlpha_injective {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) :
    Function.Injective (relabelAlpha p d r J K) := by
  intro L₁ L₂ hL
  apply Subtype.ext
  apply Subtype.ext
  funext a
  rcases a with ⟨t, ih⟩
  have hshape := congrArg
    (fun L : AlphaLabel p d b m r =>
      alphaShape p d r L t (rowHalfPerm p d r J K t ih)) hL
  change alphaShape p d r (relabelAlpha p d r J K L₁) t
      (rowHalfPerm p d r J K t ih) =
    alphaShape p d r (relabelAlpha p d r J K L₂) t
      (rowHalfPerm p d r J K t ih) at hshape
  rw [relabelAlpha_forward p d r J K L₁ t ih,
    relabelAlpha_forward p d r J K L₂ t ih] at hshape
  simpa only [alphaShape] using hshape

private noncomputable def alphaLabelEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) :
    Equiv.Perm (AlphaLabel p d b m r) :=
  Equiv.ofBijective (relabelAlpha p d r J K)
    ⟨relabelAlpha_injective p d r J K,
      Finite.surjective_of_injective (relabelAlpha_injective p d r J K)⟩

private theorem alphaLabelEquiv_apply {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) :
    alphaLabelEquiv p d r J K L = relabelAlpha p d r J K L :=
  rfl

private theorem incidence_transport {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (L L' : AlphaLabel p d b m r) (W : Side)
    (e : ∀ t : Fin s,
      Equiv.Perm (Fin (realizeParentCount b m p d r t) × Fin 2))
    (E : (stagePopulationAt 0 p d b m r).Part W ≃
      (stagePopulationAt 0 p d b m r).Part W)
    (hshape : ∀ (t : Fin s)
      (ih : Fin (realizeParentCount b m p d r t) × Fin 2),
      alphaShape p d r L' t (e t ih) = alphaShape p d r L t ih)
    (hword : ∀ (x : (stagePopulationAt 0 p d b m r).Part W)
      (t : Fin s) (ih : Fin (realizeParentCount b m p d r t) × Fin 2),
      E x ⟨t, e t ih⟩ = x ⟨t, ih⟩)
    (x : (stagePopulationAt 0 p d b m r).Part W)
    (hx : (stagePopulationAt 0 p d b m r).incidence W L.1 x) :
    (stagePopulationAt 0 p d b m r).incidence W L'.1 (E x) := by
  classical
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl (E x a) = coord W (L'.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        L'.1.1 ⟨t, ih⟩ = u ∧ E x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat
  change
    (∀ a : RealizePos b m p d r,
      chunkLvl (x a) = coord W (L.1.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih :
          Fin (realizeParentCount b m p d r t) × Fin 2 =>
        L.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)).card =
        (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ).floor.toNat at hx
  refine ⟨?_, ?_⟩
  · rintro ⟨t, ih⟩
    let ih₀ := (e t).symm ih
    have hs : alphaShape p d r L' t ih = alphaShape p d r L t ih₀ := by
      calc
        alphaShape p d r L' t ih = alphaShape p d r L' t (e t ih₀) :=
          congrArg (alphaShape p d r L' t) ((e t).apply_symm_apply ih).symm
        _ = alphaShape p d r L t ih₀ := hshape t ih₀
    have hsRaw : L'.1.1 ⟨t, ih⟩ = L.1.1 ⟨t, ih₀⟩ := by
      simpa only [alphaShape] using hs
    have hw := hword x t ih₀
    have hl := hx.1 ⟨t, ih₀⟩
    simp only [ih₀, Equiv.apply_symm_apply] at hw
    rw [hw, hsRaw]
    exact hl
  · intro t u σ
    have hcard := filter_card_eq_of_perm (e t)
      (fun ih => L.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)
      (fun ih => L'.1.1 ⟨t, ih⟩ = u ∧ E x ⟨t, ih⟩ = σ)
      (fun ih => by
        change (L.1.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ) ↔
          (L'.1.1 ⟨t, e t ih⟩ = u ∧ E x ⟨t, e t ih⟩ = σ)
        have hsRaw : L'.1.1 ⟨t, e t ih⟩ = L.1.1 ⟨t, ih⟩ := by
          simpa only [alphaShape] using hshape t ih
        rw [hsRaw, hword x t ih])
    exact hcard.symm.trans (hx.2 t u σ)

private theorem incidence_relabel_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W)
    (hx : (stagePopulationAt 0 p d b m r).incidence W L.1 x) :
    (stagePopulationAt 0 p d b m r).incidence W
      (relabelAlpha p d r J K L).1 (ambientPartEquiv p d r J K W x) := by
  apply incidence_transport p d r L (relabelAlpha p d r J K L) W
    (rowHalfPerm p d r J K) (ambientPartEquiv p d r J K W)
  · intro t ih
    exact relabelAlpha_forward p d r J K L t ih
  · exact ambientPartEquiv_apply p d r J K W
  · exact hx

private theorem incidence_relabel_backward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Side)
    (x : (stagePopulationAt 0 p d b m r).Part W)
    (hx : (stagePopulationAt 0 p d b m r).incidence W
      (relabelAlpha p d r J K L).1 x) :
    (stagePopulationAt 0 p d b m r).incidence W L.1
      ((ambientPartEquiv p d r J K W).symm x) := by
  apply incidence_transport p d r (relabelAlpha p d r J K L) L W
    (fun t => (rowHalfPerm p d r J K t).symm)
    (ambientPartEquiv p d r J K W).symm
  · intro t ih
    exact (relabelAlpha_symm p d r J K L t ih).symm
  · intro y t ih
    have hw := ambientPartEquiv_symm_apply p d r J K W y t
      ((rowHalfPerm p d r J K t).symm ih)
    simpa only [Equiv.apply_symm_apply] using hw
  · exact hx

private theorem parentCellCount_forward {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Fin 2)
    (x : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : Shape w → Prop) (σ : Chunk w) :
    Parent25.cellCount p d b m r W (relabelAlpha p d r J K L).1
        (ambientPartEquiv p d r J K (Parent25.side d r W) x) t cell σ =
      Parent25.cellCount p d b m r W L.1 x t cell σ := by
  classical
  unfold Parent25.cellCount
  have hcard := filter_card_eq_of_perm (positionPerm p d r J K)
    (fun z : RealizePos b m p d r =>
      z.1 = t ∧ cell (L.1.1 z).1 ∧ x z = σ)
    (fun z : RealizePos b m p d r =>
      z.1 = t ∧ cell ((relabelAlpha p d r J K L).1.1 z).1 ∧
        ambientPartEquiv p d r J K (Parent25.side d r W) x z = σ)
    (fun z => by
      rcases z with ⟨t₀, ih⟩
      change (t₀ = t ∧ cell (L.1.1 ⟨t₀, ih⟩).1 ∧ x ⟨t₀, ih⟩ = σ) ↔
        (t₀ = t ∧ cell ((relabelAlpha p d r J K L).1.1
            ⟨t₀, rowHalfPerm p d r J K t₀ ih⟩).1 ∧
          ambientPartEquiv p d r J K (Parent25.side d r W) x
            ⟨t₀, rowHalfPerm p d r J K t₀ ih⟩ = σ)
      have hs := relabelAlpha_forward p d r J K L t₀ ih
      have hsRaw : (relabelAlpha p d r J K L).1.1
          ⟨t₀, rowHalfPerm p d r J K t₀ ih⟩ = L.1.1 ⟨t₀, ih⟩ := by
        simpa only [alphaShape] using hs
      rw [hsRaw, ambientPartEquiv_apply p d r J K
        (Parent25.side d r W) x t₀ ih])
  exact hcard.symm

private theorem parentContainsSide_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Side)
    (x : (Parent25.Pop p d b m r).Part W) :
    Parent25.containsSide p d b m r W L.1 x ↔
      Parent25.containsSide p d b m r W
        (relabelAlpha p d r J K L).1 (ambientPartEquiv p d r J K W x) := by
  constructor
  · intro h
    rintro ⟨t, ih⟩
    let ih₀ := (rowHalfPerm p d r J K t).symm ih
    have hs := relabelAlpha_symm p d r J K L t ih
    have hsRaw : (relabelAlpha p d r J K L).1.1 ⟨t, ih⟩ =
        L.1.1 ⟨t, ih₀⟩ := by
      simpa only [ih₀, alphaShape] using hs
    have hw := ambientPartEquiv_apply p d r J K W x t ih₀
    simp only [ih₀, Equiv.apply_symm_apply] at hw
    rw [hw, hsRaw]
    exact h ⟨t, ih₀⟩
  · intro h
    rintro ⟨t, ih⟩
    have hs := relabelAlpha_forward p d r J K L t ih
    have hsRaw : (relabelAlpha p d r J K L).1.1
        ⟨t, rowHalfPerm p d r J K t ih⟩ = L.1.1 ⟨t, ih⟩ := by
      simpa only [alphaShape] using hs
    have hw := ambientPartEquiv_apply p d r J K W x t ih
    rw [← hw, ← hsRaw]
    exact h ⟨t, rowHalfPerm p d r J K t ih⟩

private theorem parentCompatible_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Fin 2)
    (x : (Parent25.Pop p d b m r).Part (Parent25.side d r W)) :
    Parent25.compatible p d b m r W
        (relabelAlpha p d r J K L).1
        (ambientPartEquiv p d r J K (Parent25.side d r W) x) ↔
      Parent25.compatible p d b m r W L.1 x := by
  constructor
  · rintro ⟨hboundary, hmarginal⟩
    constructor
    · intro t u hu σ
      exact (parentCellCount_forward p d r J K L W x t
        (fun v => v = u.val) σ).symm.trans (hboundary t u hu σ)
    · intro t k σ
      exact (parentCellCount_forward p d r J K L W x t
        (fun u => coord (Parent25.side d r W) u = k.val) σ).symm.trans
          (hmarginal t k σ)
  · rintro ⟨hboundary, hmarginal⟩
    constructor
    · intro t u hu σ
      exact (parentCellCount_forward p d r J K L W x t
        (fun v => v = u.val) σ).trans (hboundary t u hu σ)
    · intro t k σ
      exact (parentCellCount_forward p d r J K L W x t
        (fun u => coord (Parent25.side d r W) u = k.val) σ).trans
          (hmarginal t k σ)

private theorem parentCompatibleAtSide_iff {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K L : AlphaLabel p d b m r) (W : Side)
    (x : (Parent25.Pop p d b m r).Part W) :
    Parent25.compatibleAtSide p d b m r W
        (relabelAlpha p d r J K L).1 (ambientPartEquiv p d r J K W x) ↔
      Parent25.compatibleAtSide p d b m r W L.1 x := by
  by_cases hY : W = Parent25.side d r 0
  · subst W
    simp only [Parent25.compatibleAtSide, if_pos]
    exact parentCompatible_iff p d r J K L 0 x
  · by_cases hZ : W = Parent25.side d r 1
    · subst W
      simp only [Parent25.compatibleAtSide, if_neg hY, if_pos]
      exact parentCompatible_iff p d r J K L 1 x
    · simp only [Parent25.compatibleAtSide, if_neg hY, if_neg hZ]

private theorem parentCompatibleLabels_card {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J K : AlphaLabel p d b m r) (W : Side)
    (x : (Parent25.Pop p d b m r).Part W) :
    (Parent25.compatibleLabels p d b m r W
        (ambientPartEquiv p d r J K W x)).card =
      (Parent25.compatibleLabels p d b m r W x).card := by
  classical
  have hcard := filter_card_eq_of_perm (alphaLabelEquiv p d r J K)
    (fun L : AlphaLabel p d b m r =>
      Parent25.containsSide p d b m r W L.1 x ∧
        Parent25.compatibleAtSide p d b m r W L.1 x)
    (fun L : AlphaLabel p d b m r =>
      Parent25.containsSide p d b m r W L.1
          (ambientPartEquiv p d r J K W x) ∧
        Parent25.compatibleAtSide p d b m r W L.1
          (ambientPartEquiv p d r J K W x))
    (fun L => by
      rw [alphaLabelEquiv_apply]
      constructor
      · rintro ⟨hcontains, hcompatible⟩
        exact ⟨(parentContainsSide_iff p d r J K L W x).mp hcontains,
          (parentCompatibleAtSide_iff p d r J K L W x).mpr hcompatible⟩
      · rintro ⟨hcontains, hcompatible⟩
        exact ⟨(parentContainsSide_iff p d r J K L W x).mpr hcontains,
          (parentCompatibleAtSide_iff p d r J K L W x).mp hcompatible⟩)
  simpa only [Parent25.compatibleLabels] using hcard.symm

theorem coarse_transport_parent25 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (r : Fin 6) (J K : AlphaLabel p d b m r) (W : Side) :
  ∃ e : RepresentedParts p d b m J W ≃ RepresentedParts p d b m K W,
    ∀ x, Parent25.compatibleDegree p d b m K W (e x) =
      Parent25.compatibleDegree p d b m J W x := by
  classical
  let e := representedPartsEquiv p d r J K W
  refine ⟨e, ?_⟩
  intro x
  change (Parent25.compatibleLabels p d b m r W
      (ambientPartEquiv p d r J K W x.1)).card =
    (Parent25.compatibleLabels p d b m r W x.1).card
  exact parentCompatibleLabels_card p d r J K W x.1

end OmegaBound.ADVXXZGeneral
end
