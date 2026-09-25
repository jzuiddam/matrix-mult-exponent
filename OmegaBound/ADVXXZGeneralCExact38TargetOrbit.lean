import OmegaBound.ADVXXZGeneralCExact38PCompRatio

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

open Lean Elab Command in
private def findPrivateTarget38 (env : Environment) (file suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains ("_private.OmegaBound." ++ file ++ ".") ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one declaration in {file} ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_private_target38 " id:ident " from " file:str " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findPrivateTarget38 env file.getString suffix.getString
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

expose_private_target38 filter_card_eq_of_perm38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.filter_card_eq_of_perm37"
expose_private_target38 exists_perm_of_typeCnt38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.exists_perm_of_typeCnt37"
expose_private_target38 stageLabelReindex38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stageLabelReindex37"
expose_private_target38 coord_complement_eq38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.coord_complement_eq37"
expose_private_target38 stage_half_typeCnt_eq38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stage_half_typeCnt_eq37"
expose_private_target38 stageLabelReindex38_apply from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stageLabelReindex37_apply"
expose_private_target38 stage_label_complement38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stage_label_complement37"

private theorem target_filter_card_eq_of_equiv38 {A : Type*} [DecidableEq A]
    (S : Finset A) (e : {x // x ∈ S} ≃ {x // x ∈ S})
    (P Q : A → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x.val ↔ Q (e x).val) :
    (S.filter P).card = (S.filter Q).card := by
  refine Finset.card_bij'
    (fun x hx => (e ⟨x, (Finset.mem_filter.mp hx).1⟩).val)
    (fun x hx => (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h ⟨x, (Finset.mem_filter.mp hx).1⟩).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩)).mpr (by
        simpa using (Finset.mem_filter.mp hx).2)⟩
  · intro x hx
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)
  · intro x hx
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)

set_option maxHeartbeats 2000000 in
private theorem stageLabelReindex_target38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (e : ∀ t : Fin s,
      Equiv.Perm (Fin (StageCandidateRaw.stageParentCount b m p d r t)))
    (j : (stagePopulationAt q p d b m r).Label) :
    j ∈ (stagePopulationAt q p d b m r).target ↔
      stageLabelReindex38 q p d r e j ∈
        (stagePopulationAt q p d b m r).target := by
  classical
  unfold stagePopulationAt at j ⊢
  dsimp only at j ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj t u
    exact (filter_card_eq_of_perm38 (e t) _ _ (fun i => by
      change j.val ⟨t, (i, 0)⟩ = u ↔
        j.val ⟨t, ((e t).symm ((e t) i), 0)⟩ = u
      rw [(e t).symm_apply_apply])).symm.trans (hj t u)
  · intro hj t u
    exact (filter_card_eq_of_perm38 (e t) _ _ (fun i => by
      change j.val ⟨t, (i, 0)⟩ = u ↔
        j.val ⟨t, ((e t).symm ((e t) i), 0)⟩ = u
      rw [(e t).symm_apply_apply])).trans (hj t u)

private noncomputable def stageTargetLabelReindex38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (e : ∀ t : Fin s,
      Equiv.Perm (Fin (StageCandidateRaw.stageParentCount b m p d r t))) :
    StageTargetLabel37 q p d b m r ≃ StageTargetLabel37 q p d b m r :=
  (stageLabelReindex38 q p d r e).subtypeEquiv
    (stageLabelReindex_target38 q p d r e)

/-- The target-label fibre over a physical stage side. -/
def stageRoleTargetFiber38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label) :
    Finset (stagePopulationAt q p d b m r).Label :=
  (stagePopulationAt q p d b m r).target.filter fun k =>
    (stagePopulationAt q p d b m r).coarse k W =
      (stagePopulationAt q p d b m r).coarse j W

/-- All raw coarse words on a physical stage side. -/
def stageRoleCoarseImage38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side) :
    Finset (Fin (stagePopulationAt q p d b m r).n →
      Fin ((stagePopulationAt q p d b m r).grade + 1)) :=
  (Finset.univ : Finset (stagePopulationAt q p d b m r).Label).image fun k =>
    (stagePopulationAt q p d b m r).coarse k W

/-- Coarse words on a physical side represented by target stage labels. -/
def stageRoleTargetCoarseImage38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side) :
    Finset (Fin (stagePopulationAt q p d b m r).n →
      Fin ((stagePopulationAt q p d b m r).grade + 1)) :=
  (stagePopulationAt q p d b m r).target.image fun k =>
    (stagePopulationAt q p d b m r).coarse k W

end
end OmegaBound.ADVXXZGeneral
