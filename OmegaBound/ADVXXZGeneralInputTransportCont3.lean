import OmegaBound.ADVXXZGeneralInputConcentration

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def inputAlphaCountCont3 {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def inputParentCountCont3 {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, inputAlphaCountCont3 b m p d r t u

private abbrev InputPosCont3 {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) × (Fin (inputParentCountCont3 b m p d r t) × Fin 2)

private noncomputable abbrev inputPopulationCont3 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (r : Fin 6) : RawPopulation :=
  stagePopulationAt 0 p d b m r

private noncomputable def inputStageWordCont3 {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (inputPopulationCont3 p d b m r).Part W) :
    InputPosCont3 b m p d r → Chunk w := by
  classical
  dsimp [inputPopulationCont3, stagePopulationAt, InputPosCont3,
    inputParentCountCont3, inputAlphaCountCont3] at a ⊢
  exact a

private def inputPairedChunkCont3 {w s : ℕ} {b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (a : InputPosCont3 b m p d r → Chunk w) (t : Fin s)
    (i : Fin (inputParentCountCont3 b m p d r t)) : Chunk (w + w) :=
  fun c => if hc : c.val < w then
    a ⟨t, (i, ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
  else
    a ⟨t, (i, ⟨1, by omega⟩)⟩ ⟨c.val - w, by omega⟩

private def inputSideGradeCont3 {w s : ℕ} (p : ConstituentInput w s)
    (W : Side) (t : Fin s) : ℕ :=
  match W with
  | .X => p.i t
  | .Y => p.j t
  | .Z => p.k t

private noncomputable def inputCompatibleCont3 {w s : ℕ} (b m : ℕ)
    (ε : ℚ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (W : Side)
    (a : (inputPopulationCont3 p d b m r).Part W) : Prop :=
  let x := inputStageWordCont3 b m p d r W a
  ∀ t : Fin s,
    inputParentCountCont3 b m p d r t = 0 ∨
      (ApproxConsistent ε (d.betaRegion W t r)
          (fun i => inputPairedChunkCont3 x t i) ∧
       (∀ i, (d.betaRegion W t r).num (inputPairedChunkCont3 x t i) ≠ 0) ∧
       ∀ i, chunkLvl (inputPairedChunkCont3 x t i) =
         inputSideGradeCont3 p W t)

private theorem inputPairedChunkCont3_eq_parent25 {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt 0 p d b m r).Part W)
    (t : Fin s) (i : Fin (inputParentCountCont3 b m p d r t)) :
    inputPairedChunkCont3 (inputStageWordCont3 b m p d r W a) t i =
      Parent25.paired a t i := by
  funext c
  by_cases hc : c.val < w
  · simp [inputPairedChunkCont3, Parent25.paired, inputStageWordCont3, hc]
  · simp [inputPairedChunkCont3, Parent25.paired, inputStageWordCont3, hc]

private theorem inputCompatibleCont3_iff_parent25 {w s : ℕ} (b m : ℕ)
    (ε : ℚ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (W : Side)
    (a : (stagePopulationAt 0 p d b m r).Part W) :
    inputCompatibleCont3 b m ε p d r W a ↔
      Parent25.inputPartKeep p d b m ε r W a := by
  simp only [inputCompatibleCont3, Parent25.inputPartKeep,
    Parent25.parentCount, Parent25.alphaCount, inputParentCountCont3,
    inputAlphaCountCont3, inputPairedChunkCont3_eq_parent25]
  cases W <;> rfl

/-- `InputDensity` is exactly the bad exact-part ratio for the public parent-indexed
input predicate.  This exposes the event used by the density without naming the private
implementation predicate in `ADVXXZGeneralPopulationFiniteAPI`. -/
theorem inputDensity_eq_parent25_filter {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) {r : Fin 6} (J : AlphaLabel p d b m r) (W : Side) :
    InputDensity q p d b ε m J W = by
      classical
      let P := stagePopulationAt 0 p d b m r
      let exactParts : Finset (P.Part W) :=
        Finset.univ.filter (P.incidence W J.1)
      let badParts := exactParts.filter fun x =>
        ¬ Parent25.inputPartKeep p d b m ε r W x
      exact (badParts.card : ℝ) / exactParts.card := by
  unfold InputDensity
  dsimp only
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hinc, hbad⟩
    refine ⟨hinc, ?_⟩
    intro hkeep
    apply hbad
    change inputCompatibleCont3 b m ε p d r W x
    exact (inputCompatibleCont3_iff_parent25 b m ε p d r W x).mpr hkeep
  · rintro ⟨hinc, hbad⟩
    refine ⟨hinc, ?_⟩
    intro hkeep
    apply hbad
    change inputCompatibleCont3 b m ε p d r W x at hkeep
    exact (inputCompatibleCont3_iff_parent25 b m ε p d r W x).mp hkeep

end OmegaBound.ADVXXZGeneral
end
