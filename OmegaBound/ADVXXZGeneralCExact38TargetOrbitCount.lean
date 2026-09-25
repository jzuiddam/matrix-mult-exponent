import OmegaBound.ADVXXZGeneralCExact38TargetOrbit

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

open Lean Elab Command in
private def findPrivateOrbitCount38 (env : Environment) (file suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains ("_private.OmegaBound." ++ file ++ ".") ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one declaration in {file} ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_private_orbit_count38 " id:ident " from " file:str " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findPrivateOrbitCount38 env file.getString suffix.getString
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

expose_private_orbit_count38 exists_perm_of_typeCntOC38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.exists_perm_of_typeCnt37"
expose_private_orbit_count38 coord_complement_eqOC38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.coord_complement_eq37"
expose_private_orbit_count38 stage_half_typeCnt_eqOC38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stage_half_typeCnt_eq37"
expose_private_orbit_count38 stage_coarse_eq_iff_of_equivOC38 from
  "ADVXXZGeneralCExact37Orbit" :=
    ".OmegaBound.ADVXXZGeneral.stage_coarse_eq_iff_of_equiv37"
expose_private_orbit_count38 stageLabelReindexOC38_apply from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stageLabelReindex37_apply"
expose_private_orbit_count38 stage_label_complementOC38 from
  "ADVXXZGeneralCExact37Orbit" := ".OmegaBound.ADVXXZGeneral.stage_label_complement37"
expose_private_orbit_count38 stageTargetLabelReindexOC38 from
  "ADVXXZGeneralCExact38TargetOrbit" :=
    ".OmegaBound.ADVXXZGeneral.stageTargetLabelReindex38"
expose_private_orbit_count38 target_filter_card_eq_of_equivOC38 from
  "ADVXXZGeneralCExact38TargetOrbit" :=
    ".OmegaBound.ADVXXZGeneral.target_filter_card_eq_of_equiv38"

set_option maxHeartbeats 2000000 in
-- The fibre bijection normalizes dependent paired-parent positions and target subtypes.
/-- Target fibres have equal cardinality on every physical stage side. -/
theorem stageRoleTargetFiber_card_eq38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j k : StageTargetLabel37 q p d b m r) :
    (stageRoleTargetFiber38 q p d r W j.val).card =
      (stageRoleTargetFiber38 q p d r W k.val).card := by
  classical
  have htypes : ∀ t : Fin s, ∀ a : Fin (2 * w + 1),
      typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          Parent25.coordFin W (j.val.val ⟨t, (i, 0)⟩).val) a =
        typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          Parent25.coordFin W (k.val.val ⟨t, (i, 0)⟩).val) a :=
    fun t a => stage_half_typeCnt_eqOC38 q p d r j.val k.val t W a
  choose e he using fun t => exists_perm_of_typeCntOC38
    (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      Parent25.coordFin W (j.val.val ⟨t, (i, 0)⟩).val)
    (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      Parent25.coordFin W (k.val.val ⟨t, (i, 0)⟩).val) (htypes t)
  let phi := stageTargetLabelReindexOC38 q p d r e
  have hpair (t : Fin s)
      (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) (h : Fin 2) :
      coord W (j.val.val ⟨t, ((e t).symm i, h)⟩).val =
        coord W (k.val.val ⟨t, (i, h)⟩).val := by
    fin_cases h
    · change coord W (j.val.val ⟨t, ((e t).symm i, (0 : Fin 2))⟩).val =
        coord W (k.val.val ⟨t, (i, (0 : Fin 2))⟩).val
      have hi := he t ((e t).symm i)
      rw [(e t).apply_symm_apply] at hi
      have hi' := congrArg Fin.val hi.symm
      generalize hS : W = S at hi' ⊢
      cases S <;> simpa [Parent25.coordFin, coord] using hi'
    · change coord W (j.val.val ⟨t, ((e t).symm i, (1 : Fin 2))⟩).val =
        coord W (k.val.val ⟨t, (i, (1 : Fin 2))⟩).val
      rw [stage_label_complementOC38 q p d r j.val t,
        stage_label_complementOC38 q p d r k.val t]
      apply coord_complement_eqOC38
      have hi := he t ((e t).symm i)
      rw [(e t).apply_symm_apply] at hi
      have hi' := congrArg Fin.val hi.symm
      generalize hS : W = S at hi' ⊢
      cases S <;> simpa [Parent25.coordFin, coord] using hi'
  have hmem (l : StageTargetLabel37 q p d b m r) :
      (stagePopulationAt q p d b m r).coarse l.val W =
          (stagePopulationAt q p d b m r).coarse j.val W ↔
        (stagePopulationAt q p d b m r).coarse (phi l).val W =
          (stagePopulationAt q p d b m r).coarse k.val W := by
    have hleft :
        (stagePopulationAt q p d b m r).coarse l.val W =
            (stagePopulationAt q p d b m r).coarse j.val W ↔
          ∀ z : Parent25.Pos p d b m r,
            coord W (l.val.val z).val = coord W (j.val.val z).val := by
      dsimp [stagePopulationAt]
      exact stage_coarse_eq_iff_of_equivOC38 p d r _ _ _ W
    have hright :
        (stagePopulationAt q p d b m r).coarse (phi l).val W =
            (stagePopulationAt q p d b m r).coarse k.val W ↔
          ∀ z : Parent25.Pos p d b m r,
            coord W ((phi l).val.val z).val = coord W (k.val.val z).val := by
      dsimp [stagePopulationAt]
      exact stage_coarse_eq_iff_of_equivOC38 p d r _ _ _ W
    rw [hleft, hright]
    constructor
    · intro hl z
      change coord W (l.val.val ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩).val =
        coord W (k.val.val z).val
      exact (hl ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩).trans
        (hpair z.1 z.2.1 z.2.2)
    · intro hl z
      have hz := hl ⟨z.1, (e z.1 z.2.1, z.2.2)⟩
      change coord W (l.val.val
          ⟨z.1, ((e z.1).symm ((e z.1) z.2.1), z.2.2)⟩).val =
        coord W (k.val.val ⟨z.1, (e z.1 z.2.1, z.2.2)⟩).val at hz
      rw [(e z.1).symm_apply_apply] at hz
      have hp := hpair z.1 (e z.1 z.2.1) z.2.2
      rw [(e z.1).symm_apply_apply] at hp
      exact hz.trans hp.symm
  unfold stageRoleTargetFiber38
  exact target_filter_card_eq_of_equivOC38
    (stagePopulationAt q p d b m r).target phi _ _ hmem

set_option maxHeartbeats 1000000 in
-- The target-image witness uses the same dependent target reindexing as the fibre theorem.
/-- Every raw physical-side coarse word is represented by a target stage label. -/
theorem stageRoleTargetCoarseImage_eq38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : StageTargetLabel37 q p d b m r) :
    stageRoleTargetCoarseImage38 (b := b) (m := m) q p d r W =
      stageRoleCoarseImage38 (b := b) (m := m) q p d r W := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · intro x hx
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
    have htypes : ∀ t : Fin s, ∀ a : Fin (2 * w + 1),
        typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
            Parent25.coordFin W (j.val.val ⟨t, (i, 0)⟩).val) a =
          typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
            Parent25.coordFin W (k.val ⟨t, (i, 0)⟩).val) a :=
      fun t a => stage_half_typeCnt_eqOC38 q p d r j.val k t W a
    choose e he using fun t => exists_perm_of_typeCntOC38
      (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
        Parent25.coordFin W (j.val.val ⟨t, (i, 0)⟩).val)
      (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
        Parent25.coordFin W (k.val ⟨t, (i, 0)⟩).val) (htypes t)
    let phi := stageTargetLabelReindexOC38 q p d r e
    have hpair (t : Fin s)
        (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) (h : Fin 2) :
        coord W (j.val.val ⟨t, ((e t).symm i, h)⟩).val =
          coord W (k.val ⟨t, (i, h)⟩).val := by
      fin_cases h
      · have hi := he t ((e t).symm i)
        rw [(e t).apply_symm_apply] at hi
        have hi' := congrArg Fin.val hi.symm
        generalize hS : W = S at hi' ⊢
        cases S <;> simpa [Parent25.coordFin, coord] using hi'
      · change coord W (j.val.val ⟨t, ((e t).symm i, (1 : Fin 2))⟩).val =
          coord W (k.val ⟨t, (i, (1 : Fin 2))⟩).val
        rw [stage_label_complementOC38 q p d r j.val t,
          stage_label_complementOC38 q p d r k t]
        apply coord_complement_eqOC38
        have hi := he t ((e t).symm i)
        rw [(e t).apply_symm_apply] at hi
        have hi' := congrArg Fin.val hi.symm
        generalize hS : W = S at hi' ⊢
        cases S <;> simpa [Parent25.coordFin, coord] using hi'
    have hcoords : ∀ z : Parent25.Pos p d b m r,
        coord W ((phi j).val.val z).val = coord W (k.val z).val := by
      intro z
      change coord W (j.val.val ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩).val =
        coord W (k.val z).val
      exact hpair z.1 z.2.1 z.2.2
    have hcoarse : (stagePopulationAt q p d b m r).coarse (phi j).val W =
        (stagePopulationAt q p d b m r).coarse k W := by
      dsimp [stagePopulationAt]
      exact (stage_coarse_eq_iff_of_equivOC38 p d r _ _ _ W).2 hcoords
    exact Finset.mem_image.mpr ⟨(phi j).val, (phi j).property, hcoarse⟩

/-- Uniform target fibres partition the target-label set. -/
theorem stageRoleTargetFiber_mul_image38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : StageTargetLabel37 q p d b m r) :
    (stageRoleTargetFiber38 q p d r W j.val).card *
        (stageRoleCoarseImage38 (b := b) (m := m) q p d r W).card =
      (stagePopulationAt q p d b m r).target.card := by
  classical
  let P := stagePopulationAt q p d b m r
  let image := stageRoleTargetCoarseImage38 (b := b) (m := m) q p d r W
  have hpartition : P.target.card = ∑ x ∈ image,
      (P.target.filter fun k => P.coarse k W = x).card := by
    simpa only using (Finset.card_eq_sum_card_fiberwise
      (s := P.target) (t := image) (f := fun k => P.coarse k W)
      (fun k hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩))
  rw [← stageRoleTargetCoarseImage_eq38 q p d r W j]
  calc
    (stageRoleTargetFiber38 q p d r W j.val).card * image.card =
        ∑ _x ∈ image, (stageRoleTargetFiber38 q p d r W j.val).card := by
          simp [Nat.mul_comm]
    _ = ∑ x ∈ image, (P.target.filter fun k => P.coarse k W = x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
      subst x
      exact stageRoleTargetFiber_card_eq38 q p d r W j ⟨k, hk⟩
    _ = P.target.card := hpartition.symm

end
end OmegaBound.ADVXXZGeneral
