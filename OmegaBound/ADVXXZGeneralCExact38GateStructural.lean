import OmegaBound.ADVXXZGeneralCExact37GoodFamily

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

/-!
The deterministic part of the constituent exact gate.  Unlike the global gate, input
typicality is an actual deletion at this stage.  Thus a selected exact X part survives
all *ordered non-input* deletions, and every remaining X hole is input-atypical.
-/

/-- A selected, input-typical exact X-role part survives every ordered deletion. -/
theorem stagePartKeep_of_selected_X38 {w s b m M : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : StageTargetLabel37 q p d b m r)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .X))
    (ha : a ∈ exactPartsAt q b m p d r j.val (d.perm r .X))
    (hinput : Parent25.inputPartKeep p d b m epsilon r (d.perm r .X) a)
    (hjselected : j ∈ stageSelectedTargets37 q p d r B omega) :
    stagePartKeepAt25 q b m M epsilon p d r B omega .zUseful
      (d.perm r .X) a := by
  let P := stagePopulationAt q p d b m r
  let S := selected (rolePopulation P (d.perm r)) M B omega
  let matching := S.filter fun k =>
    Parent25.containsSide p d b m r (d.perm r .X) k a
  have hjS : j.val ∈ S := by
    simpa only [S, P, stageSelectedTargets37, Finset.mem_filter,
      Finset.mem_attach, true_and] using hjselected
  have hjinc : P.incidence (d.perm r .X) j.val a := by
    simpa only [P, exactPartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] using ha
  have hjcontains : Parent25.containsSide p d b m r (d.perm r .X) j.val a :=
    hjinc.1
  have hjmatching : j.val ∈ matching :=
    Finset.mem_filter.mpr ⟨hjS, hjcontains⟩
  have hXY : d.perm r .X ≠ d.perm r .Y :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hXZ : d.perm r .X ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  unfold stagePartKeepAt25
  dsimp only
  refine ⟨hinput, ⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    exact ⟨j.val, hjmatching, hjinc⟩
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXZ h).elim
  · intro h
    exact (hXZ h).elim
  · intro h
    exact (hXZ h).elim

/-- For a selected target, exact X holes are contained in the deterministic input-bad set. -/
theorem stageExactHoles_X_subset_inputBad38 {w s b m M : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : StageTargetLabel37 q p d b m r)
    (hjselected : j ∈ stageSelectedTargets37 q p d r B omega) :
    holesAt25 q b m M epsilon p d r B omega j.val (d.perm r .X) ⊆
      (exactPartsAt q b m p d r j.val (d.perm r .X)).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r (d.perm r .X) a := by
  intro a ha
  have ha' := (Finset.mem_filter.mp ha)
  refine Finset.mem_filter.mpr ⟨ha'.1, ?_⟩
  intro hinput
  exact ha'.2 (stagePartKeep_of_selected_X38 q p d hd epsilon r B omega j a
    ha'.1 hinput hjselected)

/-- Once input-atypical exact parts occupy at most the reserved half-threshold, the
selected X-role tail event in the exact premise of `stage_good_family_of_failures37`
is empty. -/
theorem stageSelectedExactHoles_X_cond38 {w s b m M : ℕ} [NeZero M] (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (j0 j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B)
    (hbad : ((exactPartsAt q b m p d r j.val (d.perm r .X)).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r (d.perm r .X) a).card ≤
      (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
        (exactPartsAt q b m p d r j0.val (d.perm r .X)).card) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (d.perm r .X)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (d.perm r .X)).card) = 0 := by
  have hevent :
      (Finset.univ.filter fun omega :
          HashOutcome (stagePopulationAt q p d b m r) M =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (d.perm r .X)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (d.perm r .X)).card) = ∅ := by
    ext omega
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hlt⟩
      have hcard := Finset.card_le_card
        (stageExactHoles_X_subset_inputBad38 q p d hd epsilon r B omega j hj)
      have hle : ((holesAt25 q b m M epsilon p d r B omega j.val
          (d.perm r .X)).card : ℝ) ≤
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
            (exactPartsAt q b m p d r j0.val (d.perm r .X)).card := by
        exact (Nat.cast_le.mpr hcard).trans hbad
      exact ((not_lt_of_ge hle) hlt).elim
    · intro hempty
      exact (by simpa using hempty : False).elim
  rw [hevent]
  simp [cond]

end
end OmegaBound.ADVXXZGeneral
end
