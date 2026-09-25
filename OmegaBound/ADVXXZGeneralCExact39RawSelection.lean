import OmegaBound.ADVXXZGeneralCExact39GoodFamily
import OmegaBound.ADVXXZGeneralCExact37Target
import OmegaBound.ADVXXZGeneralCExact36Consumer

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

set_option maxHeartbeats 2000000 in
-- Elaborating the six dependent region choices and the production record needs extra heartbeats.
/-- The complete finite selection layer before asymptotic rate bookkeeping.  On a nonzero
grid it constructs the actual production record and retains the exact target/bucket/modulus
lower bound for its selected family in every occupied region. -/
theorem constituent_grid_raw_selection39
    (q : ℕ) {w s b : ℕ} (hq : 0 < q) {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (floor : ℕ) (epsilon : ℚ) (hepsilon : 0 < epsilon)
    (m : ℕ) (h : ConstituentFullGrid27 d m epsilon)
    (hscale : ∀ r : Fin 6,
      40 * (stagePopulationAt q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r).n ≤ (cLength p b m) ^ 2)
    (hinputHalf : ∀ (r : Fin 6)
      (j : StageTargetLabel37 q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r) (W : Side),
      (stagePopulationAt q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 →
      (((exactPartsAt q b m (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) r j.val W).filter fun a =>
            ¬ Parent25.inputPartKeep (constituentGridParent27 d hd m h.val)
              (constituentGridSpec27 d hd m h.val) b m epsilon r W a).card : ℝ) ≤
        (1 / (8 * (stagePopulationAt q (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) b m r).n) : ℝ) *
          (exactPartsAt q b m (constituentGridParent27 d hd m h.val)
            (constituentGridSpec27 d hd m h.val) r j.val W).card) :
    (constituentGridTensorZ27 q d m h.val).tensor = 0 ∨
      ∃ (k : Fin 6 → ℕ)
        (B : (r : Fin 6) → Finset (ZMod (2 * k r + 1)))
        (P : ConstituentGridProduction29 q d hd epsilon m h.val),
        (∀ r,
          2 * stageDemand25 (constituentGridParent27 d hd m h.val)
              (constituentGridSpec27 d hd m h.val) b floor epsilon m r ≤ 2 * k r + 1 ∧
          2 * k r + 1 ≤ 2 * max (max floor (2 * (w + w) + 3))
            (2 * stageDemand25 (constituentGridParent27 d hd m h.val)
              (constituentGridSpec27 d hd m h.val) b floor epsilon m r) ∧
          (B r).card = rothNumberNat (k r)) ∧
        ∀ r,
          (stagePopulationAt q (constituentGridParent27 d hd m h.val)
            (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 →
          (11 / 20 : ℝ) *
              Fintype.card (StageTargetLabel37 q
                (constituentGridParent27 d hd m h.val)
                (constituentGridSpec27 d hd m h.val) b m r) *
              Fintype.card (StageBucketLabel37 (B r)) / ((2 * k r + 1 : ℕ) : ℝ) ^ 2 ≤
            ((P.selected r).card : ℝ) := by
  classical
  rcases constituent_grid_boundary_or_zero28 q d m h.val with hboundary | hzero
  · right
    let pg := constituentGridParent27 d hd m h.val
    let dg := constituentGridSpec27 d hd m h.val
    have hdg : ConstituentAdmissibleAt dg b :=
      constituent_grid_admissible28 d b m hd h.val hboundary
    have hdInput : InputAdm29 dg b := gridInputAdm29 d hd m h.val
    have hbInput : InputInt29 dg b m := gridInputInt29 d hd hb m h.val
    obtain ⟨k, B, j0, bucketIndex, hvalid, hbounds⟩ :=
      stage_demand_valid_hashes_with_targets37 q pg dg floor epsilon m
    have hex : ∀ r : Fin 6,
        ∃ (omega : HashOutcome (stagePopulationAt q pg dg b m r) (2 * k r + 1))
          (J : Finset (stagePopulationAt q pg dg b m r).Label),
          (∀ j, j ∈ J → stageGood25 q pg dg b epsilon m r
            (2 * k r + 1) (B r) omega j) ∧
          ((stagePopulationAt q pg dg b m r).n ≠ 0 →
            (11 / 20 : ℝ) * Fintype.card (StageTargetLabel37 q pg dg b m r) *
                Fintype.card (StageBucketLabel37 (B r)) /
                  ((2 * k r + 1 : ℕ) : ℝ) ^ 2 ≤ (J.card : ℝ)) := by
      intro r
      by_cases hn : (stagePopulationAt q pg dg b m r).n = 0
      · refine ⟨fun _ => 0, ∅, ?_, ?_⟩
        · simp
        · exact fun hn' => (hn' hn).elim
      · letI : NeZero (2 * k r + 1) := ⟨by omega⟩
        obtain ⟨omega, J, hgood, hcount⟩ := stage_good_family_paper39
          q floor pg dg hdg hdInput hbInput epsilon r (B r)
          (hvalid r).1 (hvalid r).2.1 (hvalid r).2.2.1 (hbounds r).1
          (j0 r) hn (by
            simpa only [pg, dg, constituentGridParent27, cLength,
              constituentBaseTotal] using hscale r)
          (fun j W => hinputHalf r j W hn)
        exact ⟨omega, J, hgood, fun _ => hcount⟩
    choose omega J hgood hcount using hex
    obtain ⟨P, hP⟩ := constituent_grid_production_of_selection36 q hq d hd hb
      epsilon hepsilon.le m h hboundary (fun r => 2 * k r + 1) B omega hvalid J
      (fun r => hgood r)
    refine ⟨k, B, P, hbounds, ?_⟩
    intro r hn
    rw [hP]
    exact hcount r hn
  · exact Or.inl hzero

end
end OmegaBound.ADVXXZGeneral
