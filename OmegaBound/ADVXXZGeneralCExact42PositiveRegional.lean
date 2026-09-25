import OmegaBound.ADVXXZGeneralCExact42RegionalExact
import OmegaBound.ADVXXZGeneralCExact42GridSum
import OmegaBound.ADVXXZGeneralCExact42GridPoolSublinear
import PLATFORM.Statements.«V17_C_Exact.4»

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

private def ConstituentSuppliedProduction42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (ε : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m ε) : Prop :=
  ∃ P : ConstituentGridProduction29 q d hd ε m h.val, ∀ r : Fin 6,
    Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
      - delta ε * (cLength p b m : ℝ) - ell ε m) ≤
    if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1 else
      ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)

/-- Zero grids are harmless; every other supplied grid records its actual repaired capacity. -/
private noncomputable def constituentGridRegionalCapacity42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (ε : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m ε) : ℕ :=
  if ∀ x y z, (constituentGridTensorZ27 q d m h.val).tensor x y z = 0 then
    constituentRegionalFloorProduct42 p d b delta ell ε m
  else if hp : ConstituentSuppliedProduction42 q d hd delta ell ε m h then
    (Classical.choose hp).copies
  else constituentRegionalFloorProduct42 p d b delta ell ε m

private theorem constituentGridRegionalCapacity_lower42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (ε : ℚ) (m : ℕ)
    (hguard : ∀ r : Fin 6, (stagePopulationAt q p d b m r).n = 0 →
      ∑ t, (p.baseN t : ℚ) * (d.A t).prob r = 0)
    (h : ConstituentFullGrid27 d m ε) :
    constituentRegionalFloorProduct42 p d b delta ell ε m ≤
      constituentGridRegionalCapacity42 q d hd delta ell ε m h := by
  unfold constituentGridRegionalCapacity42
  split_ifs with hz hp
  · exact le_rfl
  · let P := Classical.choose hp
    have hP := Classical.choose_spec hp
    exact constituentRegionalFloorProduct_le_production42 q d hd delta ell ε m h
      P hguard hP
  · exact le_rfl

private theorem gridMinimum27_le_value42 {ι : Type} [Fintype ι]
    (v : ι → ℕ) (i : ι) : gridMinimum27 v ≤ v i := by
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  simp only [gridMinimum27, dif_pos hne]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private theorem le_gridMinimum27_42 {ι : Type} [Fintype ι]
    (v : ι → ℕ) (i₀ : ι) (a : ℕ) (h : ∀ i, a ≤ v i) :
    a ≤ gridMinimum27 v := by
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
  have hmem : ((Finset.univ : Finset ι).image v).min' (hne.image v) ∈
      (Finset.univ : Finset ι).image v := Finset.min'_mem _ _
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  simp only [gridMinimum27, dif_pos hne]
  rw [← hi]
  exact h i

set_option maxHeartbeats 1200000 in
-- This is the full finite-grid truncation and direct-sum assembly for the frozen exit.
/-- Frozen V17_C_Exact.4: the nearby-grid sum produces the positive child output. -/
theorem constituent_positive_positive_regional33 : S_V17_C_Exact_4 := by
  intro q w s b hq hw p d hd hb
  obtain ⟨delta, ell, hdelta, hfinite, hsupply⟩ :=
    constituent_grid_broken_supply41 q w s b hq hw p d hd hb
  let Q : ℚ → ℕ → ℕ := fun ε m =>
    Fintype.card (ConstituentFullGrid27 d m ε)
  let cap : (ε : ℚ) → (m : ℕ) → ConstituentFullGrid27 d m ε → ℕ :=
    fun ε m h => constituentGridRegionalCapacity42 q d hd delta ell ε m h
  let V : ℚ → ℕ → ℕ := fun ε m => gridMinimum27 (cap ε m)
  refine ⟨Q, V, delta, ell, hdelta, hfinite.1, ?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨Mg, hMg⟩ := mass_zero_of_population_zero_eventually q p d b hb.1
    refine ⟨Mg, fun m hm => ?_⟩
    let h₀ : ConstituentFullGrid27 d m ε :=
      constituentCentreFullGrid42 d hd hb m ε hε.le
    apply le_gridMinimum27_42 (cap ε m) h₀
    intro h
    exact constituentGridRegionalCapacity_lower42 q d hd delta ell ε m
      (hMg m hm) h
  · intro ε hε
    exact constituent_full_grid_pool28_log_sublinear d b hd hb ε hε
  · intro ε hε
    obtain ⟨Ms, hMs⟩ := hsupply ε hε
    obtain ⟨Mp, hMp⟩ := constituent_full_grid_pool28 d b hd hb ε hε
    refine ⟨max Ms Mp, fun m hm => ?_⟩
    have hms : Ms ≤ m := (Nat.le_max_left Ms Mp).trans hm
    have hmp : Mp ≤ m := (Nat.le_max_right Ms Mp).trans hm
    have hpool := hMp m hmp
    refine ⟨hpool.1, hpool.2, fun F _ => ?_⟩
    have hpoly : ∀ h : ConstituentFullGrid27 d m ε,
        ∃ N, PolyDegeneratesAt ℤ N
          (constituentPlainInputZ q p (b*m) (3*ε)).tensor
          (copiesZ (V ε m)
            (constituentGridTensorZ27 q d m h.val)).tensor := by
      intro h
      have hmin : V ε m ≤ cap ε m h :=
        gridMinimum27_le_value42 (cap ε m) h
      have hresult := hMs m hms h
      by_cases hz : ∀ x y z,
          (constituentGridTensorZ27 q d m h.val).tensor x y z = 0
      · have hzero :
            (constituentGridTensorZ27 q d m h.val).tensor = 0 := by
          funext x y z
          exact hz x y z
        have hcopies := copiesZ_tensor_eq_zero (V ε m)
          (constituentGridTensorZ27 q d m h.val) hzero
        exact ⟨0, polyDegeneratesAt_zero_target _ _ hcopies⟩
      · have hp : ConstituentSuppliedProduction42 q d hd delta ell ε m h :=
          hresult.resolve_left hz
        let P := Classical.choose hp
        have hcap : cap ε m h = P.copies := by
          dsimp only [cap]
          unfold constituentGridRegionalCapacity42
          rw [if_neg hz, dif_pos hp]
        have htruncate : Restricts
            (copiesZ (V ε m) (constituentGridTensorZ27 q d m h.val)).tensor
            (copiesZ P.copies (constituentGridTensorZ27 q d m h.val)).tensor := by
          simpa only [copiesZ] using OmegaBound.ADVXXZStage.famDS_copies_mono
            (R := ℤ) (hcap ▸ hmin)
            (constituentGridTensorZ27 q d m h.val).tensor
        exact ⟨P.degree, polyDegeneratesAt_trans_restricts P.polynomial htruncate⟩
    let e : Fin (Q ε m) ≃ ConstituentFullGrid27 d m ε :=
      (Fintype.equivFin (ConstituentFullGrid27 d m ε)).symm
    have hsum : ∀ x y z, (constituentOutputZ q d m ε).tensor x y z =
        ∑ i : Fin (Q ε m),
          (constituentGridTensorZ27 q d m (e i).val).tensor x y z := by
      intro x y z
      have hdcomp := constituentOutputZ_eq_sum_gridTensor42 (m := m) q d hd ε
      have hdxyz := congrFun (congrFun (congrFun hdcomp x) y) z
      have happ :
          ((∑ h : ConstituentFullGrid27 d m ε,
              (constituentGridTensorZ27 q d m h.val).tensor) :
            Tensor3 ℤ (constituentOutputZ q d m ε).X
              (constituentOutputZ q d m ε).Y
              (constituentOutputZ q d m ε).Z) x y z =
            ∑ h : ConstituentFullGrid27 d m ε,
              (constituentGridTensorZ27 q d m h.val).tensor x y z := by
        let f : ConstituentFullGrid27 d m ε →
            Tensor3 ℤ (constituentOutputZ q d m ε).X
              (constituentOutputZ q d m ε).Y
              (constituentOutputZ q d m ε).Z :=
          fun h => (constituentGridTensorZ27 q d m h.val).tensor
        change (∑ h, f h) x y z = ∑ h, f h x y z
        rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]
      calc
        _ = ((∑ h : ConstituentFullGrid27 d m ε,
            (constituentGridTensorZ27 q d m h.val).tensor) :
              Tensor3 ℤ (constituentOutputZ q d m ε).X
                (constituentOutputZ q d m ε).Y
                (constituentOutputZ q d m ε).Z) x y z := hdxyz
        _ = ∑ h : ConstituentFullGrid27 d m ε,
            (constituentGridTensorZ27 q d m h.val).tensor x y z := happ
        _ = _ := (Equiv.sum_comp e
          (fun h => (constituentGridTensorZ27 q d m h.val).tensor x y z)).symm
    have heach : ∀ i : Fin (Q ε m), ∃ N, PolyDegeneratesAt ℤ N
        (constituentPlainInputZ q p (b*m) (3*ε)).tensor
        (copiesZ (V ε m)
          (constituentGridTensorZ27 q d m (e i).val)).tensor :=
      fun i => hpoly (e i)
    have hall := exists_polyDegeneratesAt_famDS_of_sum
      (constituentPlainInputZ q p (b*m) (3*ε)).tensor
      (fun i : Fin (Q ε m) =>
        (constituentGridTensorZ27 q d m (e i).val).tensor)
      (constituentOutputZ q d m ε).tensor hsum (V ε m) heach
    exact integral_degenerates F _ _ ⟨hall.choose, by
      simpa only [copiesZ] using hall.choose_spec⟩

example : S_V17_C_Exact_4 := constituent_positive_positive_regional33

end
end OmegaBound.ADVXXZGeneral
end
