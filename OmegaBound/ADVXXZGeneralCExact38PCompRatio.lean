import OmegaBound.ADVXXZGeneralCExact38CollisionStructural
import OmegaBound.ADVXXZGeneralCompatibilityQuotientParent25

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

/- Expose the already kernel-checked representation and quotient invariance helpers.  This
is the same declaration-alias technique used by `ADVXXZGeneralCExact36Repair`; no proof is bypassed. -/
open Lean Elab Command in
private def findPrivate38 (env : Environment) (file suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains ("_private.OmegaBound." ++ file ++ ".") ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one declaration in {file} ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_private38 " id:ident " from " file:str " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findPrivate38 env file.getString suffix.getString
  let newName := (← getCurrNamespace) ++ id.getId
  let some info := env.find? oldName | throwError "private declaration vanished"
  let value := mkConst oldName (info.levelParams.map Level.param)
  match info with
  | .defnInfo d => liftCoreM <| addDecl <| .defnDecl {
      name := newName, levelParams := d.levelParams, type := d.type, value := d.value,
      hints := d.hints, safety := d.safety }
  | .thmInfo d => liftCoreM <| addDecl <| .thmDecl {
      name := newName, levelParams := d.levelParams, type := d.type, value }
  | _ => throwError "unsupported declaration kind for {oldName}"

/-- Public spelling of the physical side represented by a Parent25 Y/Z law. -/
def representedSide38 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (which : Fin 2) : Side :=
  if which = 0 then d.perm r .Y else d.perm r .Z
expose_private38 empiricalLaw38 from
  "ADVXXZGeneralPopulationFiniteAPI" := ".OmegaBound.ADVXXZGeneral.empiricalLaw"
expose_private38 lawTypical38 from
  "ADVXXZGeneralPopulationFiniteAPI" := ".OmegaBound.ADVXXZGeneral.lawTypical"
expose_private38 containingSamples38 from
  "ADVXXZGeneralPopulationFiniteAPI" := ".OmegaBound.ADVXXZGeneral.containingSamples"
expose_private38 representedLawFinset38 from
  "ADVXXZGeneralPopulationFiniteAPI" := ".OmegaBound.ADVXXZGeneral.representedLawFinset"

expose_private38 pqParentContains_iff_coarse38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqParentContains_iff_coarse"
expose_private38 pqParentEmpirical_eq38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqParentEmpirical_eq"
expose_private38 pqIncidentLabels38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqIncidentLabels"
expose_private38 pqCompatibleLabels38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqCompatibleLabels"
expose_private38 pqIncidentLabels_card_eq38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqIncidentLabels_card_eq"
expose_private38 pqCompatibleLabels_card_eq38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqCompatibleLabels_card_eq"
expose_private38 pqParentFirstLawSample38 from
  "ADVXXZGeneralCompatibilityQuotientParent25" :=
    ".OmegaBound.ADVXXZGeneral.pqParentFirstLawSample"

/-- An input-typical exact part carries a represented Parent25 empirical law. -/
noncomputable def stageExactRepresentedLaw38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (epsilon : ℚ)
    (r : Fin 6) (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which))
    (hinput : Parent25.inputPartKeep p d b m epsilon r
      (Parent25.side d r which) a.val) :
    RepresentedLaw p d b epsilon m r which := by
  classical
  let beta := Parent25.empirical p d b m r which a.val
  refine ⟨beta, ?_⟩
  change beta ∈ representedLawFinset38 p d b epsilon m r which
  unfold representedLawFinset38
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_image.mpr
    let J : AlphaLabel p d b m r := ⟨j.val, j.property⟩
    refine ⟨(J, a.val), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (pqParentContains_iff_coarse38 p d r which J a.val).mp
      have hinc : (stagePopulationAt q p d b m r).incidence
          (Parent25.side d r which) j.val a.val := by
        simpa only [exactPartsAt, Finset.mem_filter, Finset.mem_univ,
          true_and] using a.property
      simpa only [Parent25.contains, Parent25.side] using hinc.1
    · funext t sigma
      have heq := pqParentEmpirical_eq38 p d r which a.val
      exact (congrFun (congrFun heq t) sigma).symm
  · change lawTypical38 d b m r (representedSide38 d r which) epsilon beta
    unfold lawTypical38
    intro t ht sigma
    have ht' : Parent25.parentCount p d b m r t ≠ 0 := by
      exact Nat.ne_of_gt ht
    have hkeep := (hinput t).resolve_left ht'
    have hh := hkeep.1 sigma
    change |Parent25.empirical p d b m r which a.val t sigma -
      (d.betaRegion (Parent25.side d r which) t r).prob sigma| ≤ epsilon at hh
    rw [show representedSide38 d r which = Parent25.side d r which by
      by_cases hwhich : which = 0 <;>
        simp [representedSide38, Parent25.side, hwhich]]
    simpa only [beta] using hh

/-- Parent25 `pcomp` is the compatible/incident target-label ratio at any word
realizing the represented law, not merely at its internally chosen representative. -/
theorem parent25_pcomp_eq_word_ratio38 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (epsilon : ℚ)
    (r : Fin 6) (which : Fin 2) (beta : RepresentedLaw p d b epsilon m r which)
    (J : AlphaLabel p d b m r)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r which))
    (hcontains : Parent25.contains p d b m r which J.val a)
    (hlaw : Parent25.empirical p d b m r which a = beta.val) :
    Parent25.pcomp p d b epsilon m r which beta =
      ((pqCompatibleLabels38 p d r which a).card : ℝ) /
        (pqIncidentLabels38 p d r which a).card := by
  classical
  let Omega := AlphaLabel p d b m r ×
    (Parent25.Pop p d b m r).Part (Parent25.side d r which)
  letI : Fintype Omega := Fintype.ofFinite Omega
  let aP := (pqParentFirstLawSample38 p d b epsilon m r which beta).1.2
  have haPLaw : Parent25.empirical p d b m r which aP = beta.val :=
    (pqParentFirstLawSample38 p d b epsilon m r which beta).2.2
  have hincident : (pqIncidentLabels38 p d r which aP).card =
      (pqIncidentLabels38 p d r which a).card :=
    pqIncidentLabels_card_eq38 p d r which a aP (hlaw.trans haPLaw.symm)
  have hcompatible : (pqCompatibleLabels38 p d r which aP).card =
      (pqCompatibleLabels38 p d r which a).card :=
    pqCompatibleLabels_card_eq38 p d r which a aP (hlaw.trans haPLaw.symm)
  unfold Parent25.pcomp
  dsimp only
  split
  · change ((pqCompatibleLabels38 p d r which aP).card : ℝ) /
      (pqIncidentLabels38 p d r which aP).card = _
    rw [hincident, hcompatible]
  · rename_i hs
    apply (hs ?_).elim
    refine ⟨(J, a), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontains, hlaw⟩

/-- Every represented-law value is bounded by the stored Parent25 maximum. -/
theorem parent25_pcomp_le_max38 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (epsilon : ℚ)
    (r : Fin 6) (which : Fin 2) (beta : RepresentedLaw p d b epsilon m r which) :
    Parent25.pcomp p d b epsilon m r which beta ≤
      Parent25.pcompMax p d b epsilon m r which := by
  classical
  unfold Parent25.pcompMax
  dsimp only
  let values := (Finset.univ : Finset (RepresentedLaw p d b epsilon m r which)).image
    (Parent25.pcomp p d b epsilon m r which)
  have hmem : Parent25.pcomp p d b epsilon m r which beta ∈ values :=
    Finset.mem_image.mpr ⟨beta, Finset.mem_univ _, rfl⟩
  have hvalues : values.Nonempty := ⟨_, hmem⟩
  rw [dif_pos hvalues]
  exact Finset.le_max' values _ hmem

/-- Parent25 compatible rivals of an input-typical exact part have the promised
per-parent `pcompMax` density among containing exact target labels. -/
theorem stageExactRivals_card_le_pcompMax38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (epsilon : ℚ)
    (r : Fin 6) (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which))
    (hinput : Parent25.inputPartKeep p d b m epsilon r
      (Parent25.side d r which) a.val) :
    ((stageExactRivals38 q p d r which j a).card : ℝ) ≤
      Parent25.pcompMax p d b epsilon m r which *
        (pqIncidentLabels38 p d r which a.val).card := by
  classical
  let J : AlphaLabel p d b m r := ⟨j.val, j.property⟩
  have hinc : (stagePopulationAt q p d b m r).incidence
      (Parent25.side d r which) j.val a.val := by
    simpa only [exactPartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] using a.property
  have hcontains : Parent25.contains p d b m r which J.val a.val := by
    simpa only [Parent25.contains, Parent25.side] using hinc.1
  let beta := stageExactRepresentedLaw38 q p d epsilon r which j a hinput
  have hlaw : Parent25.empirical p d b m r which a.val = beta.val := rfl
  have hratioEq := parent25_pcomp_eq_word_ratio38 p d epsilon r which beta J a.val
    hcontains hlaw
  have hratio := hratioEq ▸ parent25_pcomp_le_max38 p d epsilon r which beta
  have hincidentPos : 0 < (pqIncidentLabels38 p d r which a.val).card := by
    apply Finset.card_pos.mpr
    refine ⟨J, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontains⟩
  have hcompatible : ((pqCompatibleLabels38 p d r which a.val).card : ℝ) ≤
      Parent25.pcompMax p d b epsilon m r which *
        (pqIncidentLabels38 p d r which a.val).card := by
    have hpos : (0 : ℝ) < (pqIncidentLabels38 p d r which a.val).card := by
      exact_mod_cast hincidentPos
    apply (div_le_iff₀ hpos).mp
    simpa only using hratio
  have hcard : (stageExactRivals38 q p d r which j a).card ≤
      (pqCompatibleLabels38 p d r which a.val).card := by
    let f : ↥(stageExactRivals38 q p d r which j a) →
        ↥(pqCompatibleLabels38 p d r which a.val) := fun k =>
      ⟨⟨k.val, (Finset.mem_filter.mp k.property).1⟩, by
        apply Finset.mem_filter.mpr
        have hk := (Finset.mem_filter.mp k.property).2
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2.1⟩, hk.2.2⟩⟩
    have hinj : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z => z.val.val) h
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  exact (Nat.cast_le.mpr hcard).trans hcompatible

end
end OmegaBound.ADVXXZGeneral
end
