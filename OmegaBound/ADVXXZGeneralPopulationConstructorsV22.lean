import OmegaBound.ADVXXZGeneralPopulation
import OmegaBound.ADVXXZGeneralCertComplete

set_option autoImplicit false
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable def stagePopulationAt {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    RawPopulation := by
  classical
  let coordFin : Side → Shape w → Fin (2 * w + 1) := fun W u =>
    match W with
    | .X => u.1.1
    | .Y => u.1.2.1
    | .Z => u.1.2.2
  let alphaCount := fun (t : Fin s) (u : ChildShape p t) =>
    (((b * m * p.baseN t : ℕ) : ℚ) *
      (d.A t).prob r * (d.alpha t r).prob u).floor.toNat
  let parentCount := fun t => ∑ u : ChildShape p t, alphaCount t u
  let Pos := (t : Fin s) × (Fin (parentCount t) × Fin 2)
  let ShapeWord := (a : Pos) → ChildShape p a.1
  let marginals : ShapeWord → Prop := fun J =>
    ∀ (t : Fin s) (h : Fin 2) (W : Side) (a : Fin (2 * w + 1)),
      (Finset.univ.filter (fun i : Fin (parentCount t) =>
        coordFin W (J ⟨t, (i, h)⟩).1 = a)).card =
        ∑ u : ChildShape p t,
          if coordFin W ((if h = 0 then u else complement p t u).1) = a
          then alphaCount t u else 0
  let complementary : ShapeWord → Prop := fun J =>
    ∀ (t : Fin s) (i : Fin (parentCount t)),
      J ⟨t, (i, 1)⟩ = complement p t (J ⟨t, (i, 0)⟩)
  let Label := {J : ShapeWord // marginals J ∧ complementary J}
  let targetTest : Label → Prop := fun J =>
    ∀ (t : Fin s) (u : ChildShape p t),
      (Finset.univ.filter (fun i : Fin (parentCount t) =>
        J.1 ⟨t, (i, 0)⟩ = u)).card = alphaCount t u
  let Word := Pos → Chunk w
  let chunkCount := fun (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) =>
    (((m * d.outBase ⟨t, r, u⟩ : ℕ) : ℚ) *
      (d.betaChild W t r u).prob σ).floor.toNat
  let incident : Side → Label → Word → Prop := fun W J x =>
    (∀ a : Pos, chunkLvl (x a) = coord W (J.1 a).1) ∧
    ∀ (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
      (Finset.univ.filter (fun ih : Fin (parentCount t) × Fin 2 =>
        J.1 ⟨t, ih⟩ = u ∧ x ⟨t, ih⟩ = σ)).card = chunkCount W t u σ
  letI : Fintype Pos := Fintype.ofFinite _
  letI : Fintype Label := Fintype.ofFinite _
  exact
    { n := Fintype.card Pos
      grade := 2 * w
      Label := Label
      target := Finset.univ.filter targetTest
      coarse := fun J W i => coordFin W (J.1 ((Fintype.equivFin Pos).symm i)).1
      Part := fun _ => Word
      partFinite := fun _ => Fintype.ofFinite _
      fine := fun _ x i =>
        ((Fintype.equivFin (Chunk w)) (x ((Fintype.equivFin Pos).symm i))).val
      incidence := incident }

end OmegaBound.ADVXXZGeneral
