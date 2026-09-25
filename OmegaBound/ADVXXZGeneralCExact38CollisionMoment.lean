import OmegaBound.ADVXXZGeneralCExact38FiberDemand

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

open Lean Elab Command in
private def findPrivateMoment38 (env : Environment) (file suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains ("_private.OmegaBound." ++ file ++ ".") ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one declaration in {file} ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_private_moment38 " id:ident " from " file:str " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findPrivateMoment38 env file.getString suffix.getString
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

expose_private_moment38 target_exactPartsAt_card_eqCM38 from
  "ADVXXZGeneralCExact37GoodFamily" :=
    ".OmegaBound.ADVXXZGeneral.target_exactPartsAt_card_eq37"

private theorem stage_rival_ratio_from_demand38
    (rival containing image target H p demand M : ℝ)
    (himage : 0 < image) (hH : 0 < H) (hM : 0 < M)
    (hrival : rival ≤ p * containing) (hcount : containing * image = target)
    (hdemand : H * target * p / image ≤ demand)
    (hmodulus : 2 * demand ≤ M) :
    rival / M ≤ 1 / (2 * H) := by
  have hrival' : rival * image ≤ p * target := by
    calc
      rival * image ≤ (p * containing) * image :=
        mul_le_mul_of_nonneg_right hrival himage.le
      _ = p * (containing * image) := by ring
      _ = p * target := by rw [hcount]
  have hrivalH : H * (rival * image) ≤ H * (p * target) :=
    mul_le_mul_of_nonneg_left hrival' hH.le
  have hdemand' : H * target * p ≤ demand * image :=
    (div_le_iff₀ himage).mp hdemand
  have hmodulus' : 2 * demand * image ≤ M * image :=
    mul_le_mul_of_nonneg_right hmodulus himage.le
  have hcross : (2 * H * rival) * image ≤ M * image := by
    calc
      (2 * H * rival) * image = 2 * (H * (rival * image)) := by ring
      _ ≤ 2 * (H * (p * target)) := by gcongr
      _ = 2 * (H * target * p) := by ring
      _ ≤ 2 * (demand * image) := by gcongr
      _ = 2 * demand * image := by ring
      _ ≤ M * image := hmodulus'
  have hsmall : 2 * H * rival ≤ M := by nlinarith [hcross]
  apply (div_le_div_iff₀ hM (mul_pos (by norm_num) hH)).2
  nlinarith

private theorem stage_half_collision_debit38 (A E N H : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hN : 0 < N) (hscale : 40 * N ≤ H) :
    A * (1 / (2 * H) * E) ≤
      (1 / 10) * (1 / (8 * N) * A) * E := by
  have hH : 0 < H := lt_of_lt_of_le (mul_pos (by norm_num) hN) hscale
  have hden : 0 < 80 * N := mul_pos (by norm_num) hN
  have hdenle : 80 * N ≤ 2 * H := by nlinarith
  have hinv : 1 / (2 * H) ≤ 1 / (80 * N) :=
    one_div_le_one_div_of_le hden hdenle
  calc
    A * (1 / (2 * H) * E) ≤ A * (1 / (80 * N) * E) := by gcongr
    _ = (1 / 10) * (1 / (8 * N) * A) * E := by ring

set_option maxHeartbeats 1000000 in
-- This retains the input-good guard through the dependent exact-part double count.
private theorem stageSelectedCollisionHoles_sum_le_good_rivals38
    {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B) :
    ∑ omega ∈ stageTargetBucket37 q p d r B j z,
        (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) ≤
      ∑ a : StageExactPart27 q b m p d r j.val (Parent25.side d r which),
        if Parent25.inputPartKeep p d b m epsilon r
            (Parent25.side d r which) a.val then
          ((stageExactRivals38 q p d r which j a).card : ℝ) / M *
            (stageTargetBucket37 q p d r B j z).card
        else 0 := by
  let E := stageTargetBucket37 q p d r B j z
  let A := StageExactPart27 q b m p d r j.val (Parent25.side d r which)
  let event := fun omega (a : A) =>
    j ∈ stageSelectedTargets37 q p d r B omega ∧
      Parent25.inputPartKeep p d b m epsilon r (Parent25.side d r which) a.val ∧
      a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
        (Parent25.side d r which)
  have hcount (omega : HashOutcome (stagePopulationAt q p d b m r) M) :
      (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) =
        ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
    by_cases hj : j ∈ stageSelectedTargets37 q p d r B omega
    · let holes := holesAt25 q b m M epsilon p d r B omega j.val
        (Parent25.side d r which)
      let good : (stagePopulationAt q p d b m r).Part
          (Parent25.side d r which) → Prop := fun a =>
        Parent25.inputPartKeep p d b m epsilon r (Parent25.side d r which) a
      let e : {a : A // good a.val ∧ a.val ∈ holes} ≃ ↥(holes.filter good) :=
        { toFun := fun a => ⟨a.val.val,
            Finset.mem_filter.mpr ⟨a.property.2, a.property.1⟩⟩
          invFun := fun a => ⟨⟨a.val, (holesAt25_subset_exactPartsAt38 q b m M epsilon
              p d r B omega j.val (Parent25.side d r which))
                (by simpa only [holes] using (Finset.mem_filter.mp a.property).1)⟩,
            (Finset.mem_filter.mp a.property).2,
            (Finset.mem_filter.mp a.property).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcard : (holes.filter good).card =
          (Finset.univ.filter fun a : A => good a.val ∧ a.val ∈ holes).card := by
        calc
          (holes.filter good).card = Fintype.card ↥(holes.filter good) :=
            (Fintype.card_coe _).symm
          _ = Fintype.card {a : A // good a.val ∧ a.val ∈ holes} :=
            (Fintype.card_congr e).symm
          _ = (Finset.univ.filter fun a : A => good a.val ∧ a.val ∈ holes).card := by
            rw [Fintype.card_subtype]
      exact_mod_cast (by
        simpa [stageSelectedCollisionHoleCount38, event, hj, holes, good] using hcard)
    · simp [stageSelectedCollisionHoleCount38, event, hj]
  calc
    ∑ omega ∈ E,
        (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) =
      ∑ omega ∈ E, ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro omega _
        exact hcount omega
    _ = ∑ a : A, ((E.filter fun omega => event omega a).card : ℝ) :=
      sum_card_filter_comm27 E event
    _ ≤ ∑ a : A, if Parent25.inputPartKeep p d b m epsilon r
          (Parent25.side d r which) a.val then
        ((stageExactRivals38 q p d r which j a).card : ℝ) / M * E.card
      else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hi : Parent25.inputPartKeep p d b m epsilon r
          (Parent25.side d r which) a.val
      · rw [if_pos hi]
        have hcond' := stageSelectedExactPart_cond_le_rivals38 q p d hd epsilon r B
          hprime hodd hfloor which j z a hi
        have hE : E.Nonempty :=
          stageTargetBucket_nonempty37 q p d hd r B hprime hodd hfloor j z
        have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
        have hfilter : (E.filter fun omega => event omega a) =
            E ∩ (Finset.univ.filter fun omega =>
              j ∈ stageSelectedTargets37 q p d r B omega ∧
                a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
                  (Parent25.side d r which)) := by
          ext omega
          simp [event, hi]
        rw [hfilter]
        apply (div_le_iff₀ hEreal).mp
        simpa only [E, cond] using hcond'
      · rw [if_neg hi]
        have hempty : (E.filter fun omega => event omega a) = ∅ := by
          ext omega
          simp [event, hi]
        rw [hempty]
        simp

set_option maxHeartbeats 1000000 in
-- The dependent exact-part sum and literal constituent demand are normalized together.
/-- The selected input-good Y/Z collision holes consume half the `1/(4N)` allowance
with conditional debit `1/10`. -/
theorem stageSelectedCollisionHoles_paper_moment38 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor epsilon m r ≤ M)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hscale : 40 * (stagePopulationAt q p d b m r).n ≤ (cLength p b m) ^ 2)
    (which : Fin 2) (j0 j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B) :
    ∑ omega ∈ stageTargetBucket37 q p d r B j z,
        (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) ≤
      (1 / 10 : ℝ) *
        ((1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
          (exactPartsAt q b m p d r j0.val (Parent25.side d r which)).card) *
        (stageTargetBucket37 q p d r B j z).card := by
  let P := stagePopulationAt q p d b m r
  let W := Parent25.side d r which
  let image := stageRoleCoarseImage38 (b := b) (m := m) q p d r W
  let H : ℝ := (((cLength p b m) ^ 2 : ℕ) : ℝ)
  let E := stageTargetBucket37 q p d r B j z
  have hbase := stageSelectedCollisionHoles_sum_le_good_rivals38 q p d hd epsilon r B
    hprime hodd hfloor which j z
  have himage : 0 < (image.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨P.coarse j.val W,
      Finset.mem_image.mpr ⟨j.val, Finset.mem_univ _, rfl⟩⟩
  have hN : 0 < P.n := Nat.pos_of_ne_zero hn
  have hL : 0 < cLength p b m := by
    have hpop := stagePopulation_n_le q p d b m r
    omega
  have hH : 0 < H := by
    dsimp only [H]
    positivity
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
  have hdemandReal : (2 : ℝ) * stageDemand25 p d b floor epsilon m r ≤ M := by
    exact_mod_cast hdemand
  have hceil := stageDemand_role_ceiling_le38 (b := b) (m := m)
    p d floor epsilon r which
  let demandTerm : ℝ := H * P.target.card *
    Parent25.pcompMax p d b epsilon m r which / image.card
  have hdemandTerm : demandTerm ≤ stageDemand25 p d b floor epsilon m r := by
    have hleceil : demandTerm ≤ Nat.ceil demandTerm := Nat.le_ceil demandTerm
    have hceil' : Nat.ceil demandTerm ≤ stageDemand25 p d b floor epsilon m r := by
      simpa [demandTerm, H, P, image, W, stageRoleCoarseImage38] using hceil
    have hceilReal : ((Nat.ceil demandTerm : ℕ) : ℝ) ≤
        stageDemand25 p d b floor epsilon m r := by exact_mod_cast hceil'
    exact hleceil.trans hceilReal
  have hpart (a : StageExactPart27 q b m p d r j.val W)
      (hi : Parent25.inputPartKeep p d b m epsilon r W a.val) :
      ((stageExactRivals38 q p d r which j a).card : ℝ) / M ≤ 1 / (2 * H) := by
    have hrival := stageExactRivals_card_le_pcompMax38 q p d epsilon r which j a hi
    have hcountNat := stageRoleTargetFiber_mul_image38 q p d r W j
    rw [← stageIncidentLabels_card_eq_fiber38 q p d r which j a] at hcountNat
    have hcountReal : ((pqIncidentLabels38 p d r which a.val).card : ℝ) *
        image.card = P.target.card := by exact_mod_cast hcountNat
    exact stage_rival_ratio_from_demand38 _ _ _ _ _ _ _ _ himage hH hMreal
      hrival hcountReal hdemandTerm hdemandReal
  have hsum :
      ∑ a : StageExactPart27 q b m p d r j.val W,
          (if Parent25.inputPartKeep p d b m epsilon r W a.val then
            ((stageExactRivals38 q p d r which j a).card : ℝ) / M * (E.card : ℝ)
          else 0) ≤
        ∑ _a : StageExactPart27 q b m p d r j.val W,
          (1 / (2 * H)) * E.card := by
    apply Finset.sum_le_sum
    intro a _
    by_cases hi : Parent25.inputPartKeep p d b m epsilon r W a.val
    · rw [if_pos hi]
      exact mul_le_mul_of_nonneg_right (hpart a hi) (Nat.cast_nonneg _)
    · rw [if_neg hi]
      positivity
  have hcard := target_exactPartsAt_card_eqCM38 q m p d r j j0 W
  calc
    _ ≤ ∑ a : StageExactPart27 q b m p d r j.val W,
        (if Parent25.inputPartKeep p d b m epsilon r W a.val then
          ((stageExactRivals38 q p d r which j a).card : ℝ) / M * (E.card : ℝ)
        else 0) := hbase
    _ ≤ ∑ _a : StageExactPart27 q b m p d r j.val W,
        (1 / (2 * H)) * E.card := hsum
    _ = ((exactPartsAt q b m p d r j.val W).card : ℝ) *
        ((1 / (2 * H)) * E.card) := by simp [StageExactPart27]
    _ = ((exactPartsAt q b m p d r j0.val W).card : ℝ) *
        ((1 / (2 * H)) * E.card) := by rw [hcard]
    _ ≤ (1 / 10 : ℝ) *
        ((1 / (8 * P.n) : ℝ) *
          (exactPartsAt q b m p d r j0.val W).card) * E.card := by
      apply stage_half_collision_debit38
      · positivity
      · positivity
      · exact_mod_cast hN
      · dsimp only [P, H]
        exact_mod_cast hscale

end
end OmegaBound.ADVXXZGeneral
