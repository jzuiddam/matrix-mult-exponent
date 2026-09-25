import OmegaBound.ADVXXZGeneralCExact38HoleTails

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

open Lean Elab Command in
private def findPrivateGridTail38 (env : Environment) (file suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains ("_private.OmegaBound." ++ file ++ ".") ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one declaration in {file} ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_private_grid_tail38 " id:ident " from " file:str " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findPrivateGridTail38 env file.getString suffix.getString
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

expose_private_grid_tail38 target_exactPartsAt_card_eqGT38 from
  "ADVXXZGeneralCExact37GoodFamily" :=
    ".OmegaBound.ADVXXZGeneral.target_exactPartsAt_card_eq37"

private theorem stageExactParts_card_pos38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hdInput : InputAdm29 d b) (hbInput : InputInt29 d b m)
    (r : Fin 6) (j : StageTargetLabel37 q p d b m r) (W : Side) :
    0 < (exactPartsAt q b m p d r j.val W).card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_pos_iff.mpr
  exact Grid29.stageExactPart_nonempty27 q m p d hdInput hbInput r
    j.val j.property W

/-- The selected exact X-role tail is zero under the uniform input half-reserve. -/
theorem stageSelectedExactHoles_X_paper_cond38 {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (j0 j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B)
    (hinputHalf : ∀ (k : StageTargetLabel37 q p d b m r) (W : Side),
      (((exactPartsAt q b m p d r k.val W).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r W a).card : ℝ) ≤
        (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
          (exactPartsAt q b m p d r k.val W).card) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (d.perm r .X)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (d.perm r .X)).card) = 0 := by
  have hcard := target_exactPartsAt_card_eqGT38 q m p d r j j0 (d.perm r .X)
  have hN : (0 : ℝ) < (stagePopulationAt q p d b m r).n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  apply stageSelectedExactHoles_X_cond38 q p d hd epsilon r B j0 j z
  calc
    _ ≤ (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
        (exactPartsAt q b m p d r j.val (d.perm r .X)).card :=
      hinputHalf j (d.perm r .X)
    _ = (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
        (exactPartsAt q b m p d r j0.val (d.perm r .X)).card := by rw [hcard]
    _ ≤ (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
        (exactPartsAt q b m p d r j0.val (d.perm r .X)).card := by
      gcongr
      norm_num

/-- The selected exact Y-role tail has paper debit `1/10`. -/
theorem stageSelectedExactHoles_Y_paper_cond38 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hdInput : InputAdm29 d b)
    (hbInput : InputInt29 d b m) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor epsilon m r ≤ M)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hscale : 40 * (stagePopulationAt q p d b m r).n ≤ (cLength p b m) ^ 2)
    (j0 j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B)
    (hinputHalf : ∀ (k : StageTargetLabel37 q p d b m r) (W : Side),
      (((exactPartsAt q b m p d r k.val W).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r W a).card : ℝ) ≤
        (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
          (exactPartsAt q b m p d r k.val W).card) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (d.perm r .Y)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (d.perm r .Y)).card) ≤ (1 / 10 : ℝ) := by
  have hcard := target_exactPartsAt_card_eqGT38 q m p d r j j0 (d.perm r .Y)
  have hbad := hinputHalf j (d.perm r .Y)
  rw [hcard] at hbad
  simpa only [Parent25.side, if_pos rfl] using
    (stageSelectedExactHoles_YZ_cond38 q floor p d hd epsilon r B hprime hodd
      hfloor hdemand hn hscale (0 : Fin 2) j0 j z hbad
        (stageExactParts_card_pos38 q p d hdInput hbInput r j0 (d.perm r .Y)))

/-- The selected exact Z-role tail has paper debit `1/10`. -/
theorem stageSelectedExactHoles_Z_paper_cond38 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hdInput : InputAdm29 d b)
    (hbInput : InputInt29 d b m) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor epsilon m r ≤ M)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hscale : 40 * (stagePopulationAt q p d b m r).n ≤ (cLength p b m) ^ 2)
    (j0 j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B)
    (hinputHalf : ∀ (k : StageTargetLabel37 q p d b m r) (W : Side),
      (((exactPartsAt q b m p d r k.val W).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r W a).card : ℝ) ≤
        (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
          (exactPartsAt q b m p d r k.val W).card) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (d.perm r .Z)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (d.perm r .Z)).card) ≤ (1 / 10 : ℝ) := by
  have hcard := target_exactPartsAt_card_eqGT38 q m p d r j j0 (d.perm r .Z)
  have hbad := hinputHalf j (d.perm r .Z)
  rw [hcard] at hbad
  have hone : (1 : Fin 2) ≠ 0 := by decide +kernel
  simpa only [Parent25.side, if_neg hone] using
    (stageSelectedExactHoles_YZ_cond38 q floor p d hd epsilon r B hprime hodd
      hfloor hdemand hn hscale (1 : Fin 2) j0 j z hbad
        (stageExactParts_card_pos38 q p d hdInput hbInput r j0 (d.perm r .Z)))

end
end OmegaBound.ADVXXZGeneral
