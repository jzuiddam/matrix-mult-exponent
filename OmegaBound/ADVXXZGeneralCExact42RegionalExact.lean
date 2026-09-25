import Mathlib.Algebra.Order.Floor.Semifield
import OmegaBound.ADVXXZGeneralCExact42TensorBridge
import OmegaBound.ADVXXZGeneralGlobalExactUniformOutput
import PLATFORM.Statements.«V17_C_Exact.3»

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

/-- The exact product of the six displayed regional natural floors. -/
noncomputable def constituentRegionalFloorProduct42 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ) (ε : ℚ) (m : ℕ) : ℕ :=
  ∏ r : Fin 6,
    if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
      Nat.floor (Real.exp
        (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
          - delta ε * (cLength p b m : ℝ) - ell ε m))

theorem constituentRegionalFloorProduct_bound42 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ) :
    RegionalCopyBound33 p d b delta ell
      (constituentRegionalFloorProduct42 p d b delta ell) := by
  intro ε hε
  exact ⟨0, fun m hm => le_rfl⟩

private theorem floor_real_quotient42 (n R : ℕ) (x : ℝ)
    (hx : Real.exp x ≤ (n : ℝ) / R) : Nat.floor (Real.exp x) ≤ n / R := by
  have h := Nat.floor_mono hx
  simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using h

/-- A supplied production record dominates the displayed product of regional floors. -/
theorem constituentRegionalFloorProduct_le_production42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (ε : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m ε)
    (P : ConstituentGridProduction29 q d hd ε m h.val)
    (hguard : ∀ r : Fin 6, (stagePopulationAt q p d b m r).n = 0 →
      ∑ t, (p.baseN t : ℚ) * (d.A t).prob r = 0)
    (hP : ∀ r : Fin 6,
      Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
        - delta ε * (cLength p b m : ℝ) - ell ε m) ≤
      if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
            (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1 else
        ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)) :
    constituentRegionalFloorProduct42 p d b delta ell ε m ≤ P.copies := by
  have hfactor : ∀ r : Fin 6,
      (if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
        Nat.floor (Real.exp
          (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
            - delta ε * (cLength p b m : ℝ) - ell ε m))) ≤
        P.regionalCopies r := by
    intro r
    let x : ℝ := Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
      - delta ε * (cLength p b m : ℝ) - ell ε m
    have hN := gridPopulation_n_eq q d hd m h.val r
    by_cases hmass : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0
    · rw [if_pos hmass, P.regionalCopies_eq r]
      have hN0 := stagePopulation_n_eq_zero_of_mass_zero q p d b m r hmass
      dsimp only
      rw [if_pos (hN.trans hN0)]
    · rw [if_neg hmass, P.regionalCopies_eq r]
      have hN0 : (stagePopulationAt q p d b m r).n ≠ 0 := by
        intro hz
        exact hmass (hguard r hz)
      have hNg : (stagePopulationAt q
          (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 := by
        rw [hN]
        exact hN0
      dsimp only
      rw [if_neg hNg]
      apply floor_real_quotient42
      have hr := hP r
      dsimp only [constituentRegionalReserve33] at hr
      simp only [if_neg hNg] at hr
      simpa only [x] using hr
  calc
    constituentRegionalFloorProduct42 p d b delta ell ε m =
        ∏ r : Fin 6,
          if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
            Nat.floor (Real.exp
              (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
                - delta ε * (cLength p b m : ℝ) - ell ε m)) := rfl
    _ ≤ ∏ r : Fin 6, P.regionalCopies r :=
      Finset.prod_le_prod' (fun r _ => hfactor r)
    _ = P.copies := P.copies_eq.symm

set_option maxHeartbeats 1000000 in
-- The frozen assembly repeats the dependent production record in its regional product.
/-- Frozen `V17_C_Exact.3`: supported positive parent to the original exact child,
with the six regional natural floors packaged before multiplication. -/
theorem constituent_positive_exact_regional33 : S_V17_C_Exact_3 := by
  intro q w s b hq hw p d hd hb
  obtain ⟨delta, ell, hdelta, hfinite, hsupply⟩ :=
    constituent_grid_broken_supply41 q w s b hq hw p d hd hb
  let V := constituentRegionalFloorProduct42 p d b delta ell
  refine ⟨V, delta, ell, hdelta, ?_,
    constituentRegionalFloorProduct_bound42 p d b delta ell, ?_⟩
  · exact hfinite.1
  · intro ε hε
    obtain ⟨Ms, hMs⟩ := hsupply ε hε
    obtain ⟨Mg, hMg⟩ := mass_zero_of_population_zero_eventually q p d b hb.1
    refine ⟨max Ms Mg, fun m hm F _ => ?_⟩
    have hms : Ms ≤ m := le_trans (Nat.le_max_left _ _) hm
    have hmg : Mg ≤ m := le_trans (Nat.le_max_right _ _) hm
    let hcentre : ConstituentFullGrid27 d m ε :=
      constituentCentreFullGrid42 d hd hb m ε hε.le
    rcases hMs m hms hcentre with hzero | ⟨P, hP⟩
    · have hgrid0 :
          (constituentGridTensorZ27 q d m hcentre.val).tensor = 0 := by
        funext x y z
        exact hzero x y z
      have hout0 : (constituentOutputZ q d m 0).tensor = 0 := by
        rw [← constituentCentreGridTensor_eq_output42 q d hd hb m]
        exact hgrid0
      have hcopies0 := copiesZ_tensor_eq_zero (V ε m) (constituentOutputZ q d m 0) hout0
      exact integral_degenerates F _ _
        ⟨0, polyDegeneratesAt_zero_target _ _ hcopies0⟩
    · have hfactor : ∀ r : Fin 6,
          (if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
            Nat.floor (Real.exp
              (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
                - delta ε * (cLength p b m : ℝ) - ell ε m))) ≤
            P.regionalCopies r := by
        intro r
        let x : ℝ := Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
          - delta ε * (cLength p b m : ℝ) - ell ε m
        have hN := gridPopulation_n_eq q d hd m hcentre.val r
        by_cases hmass : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0
        · rw [if_pos hmass, P.regionalCopies_eq r]
          have hN0 := stagePopulation_n_eq_zero_of_mass_zero q p d b m r hmass
          dsimp only
          rw [if_pos (hN.trans hN0)]
        · rw [if_neg hmass, P.regionalCopies_eq r]
          have hN0 : (stagePopulationAt q p d b m r).n ≠ 0 := by
            intro hz
            exact hmass (hMg m hmg r hz)
          have hNg : (stagePopulationAt q
              (constituentGridParent27 d hd m hcentre.val)
              (constituentGridSpec27 d hd m hcentre.val) b m r).n ≠ 0 := by
            rw [hN]
            exact hN0
          dsimp only
          rw [if_neg hNg]
          apply floor_real_quotient42
          have hr := hP r
          dsimp only [constituentRegionalReserve33] at hr
          simp only [if_neg hNg] at hr
          simpa only [x] using hr
      have hVP : V ε m ≤ P.copies := by
        calc
          V ε m = ∏ r : Fin 6,
              if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
                Nat.floor (Real.exp
                  (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
                    - delta ε * (cLength p b m : ℝ) - ell ε m)) := rfl
          _ ≤ ∏ r : Fin 6, P.regionalCopies r :=
            Finset.prod_le_prod' (fun r _ => hfactor r)
          _ = P.copies := P.copies_eq.symm
      have hbase : Restricts
          (copiesZ P.copies (constituentOutputZ q d m 0)).tensor
          (constituentInputZ q p (b*m) ε).tensor := by
        have h := P.repair.trans P.source_to_broken
        change Restricts
          (copiesZ P.copies
            (constituentGridTensorZ27 q d m
              (constituentCentreExactGrid42 d hd hb m))).tensor
          (constituentInputZ q
            (constituentGridParent27 d hd m
              (constituentCentreExactGrid42 d hd hb m)) (b*m) ε).tensor at h
        simpa only [copiesZ,
          constituentCentreGridTensor_eq_output42 q d hd hb m,
          constituentCentreInput_tensor_eq42 q d hd hb m ε] using h
      have hmono : Restricts
          (copiesZ (V ε m) (constituentOutputZ q d m 0)).tensor
          (copiesZ P.copies (constituentOutputZ q d m 0)).tensor := by
        simpa only [copiesZ] using OmegaBound.ADVXXZStage.famDS_copies_mono
          (R := ℤ) hVP (constituentOutputZ q d m 0).tensor
      exact integral_degenerates F _ _
        ⟨0, polyDegeneratesAt_of_restricts (hmono.trans hbase)⟩

example : S_V17_C_Exact_3 := constituent_positive_exact_regional33

end
end OmegaBound.ADVXXZGeneral
end
