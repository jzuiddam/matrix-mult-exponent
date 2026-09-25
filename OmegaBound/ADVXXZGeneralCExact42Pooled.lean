import Mathlib.Algebra.Order.Floor.Semiring
import OmegaBound.ADVXXZGeneralCExact42FreshRepair
import OmegaBound.ADVXXZGeneralIterateInfraRates

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3 Filter
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private def ConstituentPooledProduction42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m epsilon) : Prop :=
  ∃ P : ConstituentGridProduction29 q d hd epsilon m h.val, ∀ r : Fin 6,
    Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
      - delta epsilon * (cLength p b m : ℝ) - ell epsilon m) ≤
    if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1 else
      ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)

private noncomputable def constituentRawGridCount42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m epsilon)
    (P : ConstituentGridProduction29 q d hd epsilon m h.val) : ℕ :=
  ∏ r : Fin 6,
    if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1
    else (P.selected r).card

private noncomputable def constituentPooledExponent42 {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (b : ℕ)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ) : ℝ :=
  (cRate d - 6 * delta epsilon) * (cLength p b m : ℝ) - 6 * ell epsilon m

private noncomputable def constituentPooledGridCapacity42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m epsilon) : ℕ :=
  if ∀ x y z, (constituentGridTensorZ27 q d m h.val).tensor x y z = 0 then
    Nat.ceil (Real.exp (constituentPooledExponent42 d b delta ell epsilon m))
  else if hp : ConstituentPooledProduction42 q d hd delta ell epsilon m h then
    constituentRawGridCount42 q d hd epsilon m h (Classical.choose hp)
  else Nat.ceil (Real.exp (constituentPooledExponent42 d b delta ell epsilon m))

private theorem constituentBaseTotal_pos42 {w s : ℕ} (p : ConstituentInput w s) :
    0 < constituentBaseTotal p := by
  unfold constituentBaseTotal
  let t : Fin s := ⟨0, p.terms_nonempty⟩
  exact lt_of_lt_of_le (p.baseN_pos t)
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))

private theorem constituentPooledExponent_eq_sum42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ) :
    constituentPooledExponent42 d b delta ell epsilon m =
      ∑ r : Fin 6, (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
        - delta epsilon * (cLength p b m : ℝ) - ell epsilon m) := by
  have hbase : (constituentBaseTotal p : ℝ) ≠ 0 := by
    exact_mod_cast (constituentBaseTotal_pos42 p).ne'
  unfold constituentPooledExponent42 cRate cLength
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hbase]
  rw [← Finset.mul_sum]
  ring

private theorem constituentRawGridCount_lower42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m epsilon)
    (P : ConstituentGridProduction29 q d hd epsilon m h.val)
    (hP : ∀ r : Fin 6,
      Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
        - delta epsilon * (cLength p b m : ℝ) - ell epsilon m) ≤
      if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
            (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1 else
        ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)) :
    Real.exp (constituentPooledExponent42 d b delta ell epsilon m) ≤
      (constituentRawGridCount42 q d hd epsilon m h P : ℝ) := by
  have hfactor : ∀ r : Fin 6,
      Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
        - delta epsilon * (cLength p b m : ℝ) - ell epsilon m) ≤
      ((if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
          (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1
        else (P.selected r).card : ℕ) : ℝ) := by
    intro r
    by_cases hn : (stagePopulationAt q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r).n = 0
    · simpa only [if_pos hn, Nat.cast_one] using hP r
    · rw [if_neg hn]
      have hr := hP r
      rw [if_neg hn] at hr
      calc
        _ ≤ ((P.selected r).card : ℝ) /
            (constituentRegionalReserve33 q P r : ℝ) := hr
        _ ≤ ((P.selected r).card : ℝ) := by
          exact div_le_self (by positivity) (by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr
              (constituentRegionalReserve33_pos q P r).ne')
  rw [constituentPooledExponent_eq_sum42, Real.exp_sum]
  change (∏ r, Real.exp
      (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ) -
        delta epsilon * (cLength p b m : ℝ) - ell epsilon m)) ≤ _
  rw [constituentRawGridCount42, Nat.cast_prod]
  exact Finset.prod_le_prod (fun r _ => (Real.exp_pos _).le) (fun r _ => hfactor r)

private theorem constituentPooledGridCapacity_lower42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (epsilon : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m epsilon)
    (hsupply : (∀ x y z,
        (constituentGridTensorZ27 q d m h.val).tensor x y z = 0) ∨
      ConstituentPooledProduction42 q d hd delta ell epsilon m h) :
    Real.exp (constituentPooledExponent42 d b delta ell epsilon m) ≤
      (constituentPooledGridCapacity42 q d hd delta ell epsilon m h : ℝ) := by
  unfold constituentPooledGridCapacity42
  split_ifs with hz hp
  · exact Nat.le_ceil _
  · exact constituentRawGridCount_lower42 q d hd delta ell epsilon m h
      (Classical.choose hp) (Classical.choose_spec hp)
  · exact (hp (hsupply.resolve_left hz)).elim

private theorem gridMinimum_le_value42 {iota : Type} [Fintype iota]
    (v : iota → ℕ) (i : iota) : gridMinimum27 v ≤ v i := by
  have hne : (Finset.univ : Finset iota).Nonempty := ⟨i, Finset.mem_univ i⟩
  simp only [gridMinimum27, dif_pos hne]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private theorem le_gridMinimum42 {iota : Type} [Fintype iota]
    (v : iota → ℕ) (i0 : iota) (a : ℝ) (h : ∀ i, a ≤ (v i : ℝ)) :
    a ≤ (gridMinimum27 v : ℝ) := by
  have hne : (Finset.univ : Finset iota).Nonempty := ⟨i0, Finset.mem_univ i0⟩
  have hmem : ((Finset.univ : Finset iota).image v).min' (hne.image v) ∈
      (Finset.univ : Finset iota).image v := Finset.min'_mem _ _
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  simp only [gridMinimum27, dif_pos hne]
  rw [← hi]
  exact h i

private theorem sublinear_six42 {L : ℕ → ℕ} {ell : ℕ → ℝ}
    (h : Sublinear L ell) : Sublinear L (fun m => 6 * ell m) := by
  intro delta hdelta
  obtain ⟨M, hM⟩ := h (delta / 6) (div_pos hdelta (by norm_num))
  refine ⟨M, fun m hm => ?_⟩
  calc
    |6 * ell m| = 6 * |ell m| := by rw [abs_mul]; norm_num
    _ ≤ 6 * (delta / 6 * (L m : ℝ)) :=
      mul_le_mul_of_nonneg_left (hM m hm) (by norm_num)
    _ = delta * (L m : ℝ) := by ring

private theorem sublinear_log_pool_mul_grid42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hq : 0 < q) (hw : 0 < w)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    Sublinear (cLength p b) (fun m => Real.log
      ((constituentRepairPool33 q p d b m *
        Fintype.card (ConstituentFullGrid27 d m epsilon) : ℕ) : ℝ)) := by
  have hp := constituent_repair_pool_sublinear33 q w s b hq hw p d hd hb
  have hg := constituent_full_grid_pool28_log_sublinear d b hd hb epsilon hepsilon
  have hadd := sublinear_add hp hg
  have heq : (fun m => Real.log
      ((constituentRepairPool33 q p d b m *
        Fintype.card (ConstituentFullGrid27 d m epsilon) : ℕ) : ℝ)) =
      (fun m => Real.log (constituentRepairPool33 q p d b m : ℝ) +
        Real.log (Fintype.card (ConstituentFullGrid27 d m epsilon) : ℝ)) := by
    funext m
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast (repairPool_pos q p d b m).ne'
    · exact_mod_cast (Fintype.card_pos_iff.mpr
        ⟨constituentCentreFullGrid42 d hd hb m epsilon hepsilon.le⟩).ne'
  rw [heq]
  exact hadd

set_option maxHeartbeats 2400000 in
-- The proof keeps the raw regional count, the changing-grid minimum, and the nested input pool
-- visible simultaneously until the final direct-sum flattening.
/-- The pooled constituent producer used by the recursion, funded before regional natural division. -/
theorem constituent_pooled_positive33 : S_constituent_pooled_positive33 := by
  intro q w s b hq hw p d hd hb
  obtain ⟨delta, ell, hdelta, hfinite, hsupply⟩ :=
    constituent_grid_broken_supply41 q w s b hq hw p d hd hb
  let Delta : ℚ → ℝ := fun epsilon => 6 * delta epsilon
  let Ell : ℚ → ℕ → ℝ := fun epsilon m => 6 * ell epsilon m
  let Q : ℚ → ℕ → ℕ := fun epsilon m =>
    Fintype.card (ConstituentFullGrid27 d m epsilon) *
      constituentRepairPool33 q p d b m
  let cap : (epsilon : ℚ) → (m : ℕ) → ConstituentFullGrid27 d m epsilon → ℕ :=
    fun epsilon m h => constituentPooledGridCapacity42 q d hd delta ell epsilon m h
  let V : ℚ → ℕ → ℕ := fun epsilon m => gridMinimum27 (cap epsilon m)
  refine ⟨Q, V, Delta, Ell, ?_, ?_, ?_, ?_, ?_⟩
  · exact vanishesWithTolerance_const_mul 6 (by norm_num) hdelta
  · refine ⟨fun epsilon m => mul_nonneg (by norm_num) (hfinite.1.1 epsilon m), ?_⟩
    intro epsilon hepsilon
    exact sublinear_six42 (hfinite.1.2 epsilon hepsilon)
  · intro epsilon hepsilon
    obtain ⟨Ms, hMs⟩ := hsupply epsilon hepsilon
    refine ⟨Ms, fun m hm => ?_⟩
    let h0 : ConstituentFullGrid27 d m epsilon :=
      constituentCentreFullGrid42 d hd hb m epsilon hepsilon.le
    apply le_gridMinimum42 (cap epsilon m) h0
    intro h
    have hs := hMs m hm h
    simpa only [cap, Delta, Ell, constituentPooledExponent42] using
      constituentPooledGridCapacity_lower42 q d hd delta ell epsilon m h hs
  · intro epsilon hepsilon
    simpa only [Q, Nat.mul_comm] using
      sublinear_log_pool_mul_grid42 q d hq hw hd hb epsilon hepsilon
  · intro epsilon hepsilon
    obtain ⟨Ms, hMs⟩ := hsupply epsilon hepsilon
    obtain ⟨Mp, hMp⟩ := constituent_full_grid_pool28 d b hd hb epsilon hepsilon
    refine ⟨max Ms Mp, fun m hm => ?_⟩
    have hms : Ms ≤ m := (Nat.le_max_left Ms Mp).trans hm
    have hmp : Mp ≤ m := (Nat.le_max_right Ms Mp).trans hm
    have hgridcard := hMp m hmp
    have hpoolpos : 0 < constituentRepairPool33 q p d b m := repairPool_pos q p d b m
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [Q]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hgridcard.1) hpoolpos.ne')
    · dsimp only [Q]
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hgridcard.2
    · have hpoly : ∀ h : ConstituentFullGrid27 d m epsilon,
          ∃ degree, PolyDegeneratesAt ℤ degree
            (copiesZ (constituentRepairPool33 q p d b m)
              (constituentPlainInputZ q p (b*m) (3*epsilon))).tensor
            (copiesZ (V epsilon m)
              (constituentGridTensorZ27 q d m h.val)).tensor := by
        intro h
        have hmin : V epsilon m ≤ cap epsilon m h :=
          gridMinimum_le_value42 (cap epsilon m) h
        have hresult := hMs m hms h
        by_cases hz : ∀ x y z,
            (constituentGridTensorZ27 q d m h.val).tensor x y z = 0
        · have hzero : (constituentGridTensorZ27 q d m h.val).tensor = 0 := by
            funext x y z
            exact hz x y z
          have hcopies := copiesZ_tensor_eq_zero (V epsilon m)
            (constituentGridTensorZ27 q d m h.val) hzero
          exact ⟨0, polyDegeneratesAt_zero_target _ _ hcopies⟩
        · have hp : ConstituentPooledProduction42 q d hd delta ell epsilon m h :=
            hresult.resolve_left hz
          let P := Classical.choose hp
          have hP := Classical.choose_spec hp
          have hcap : cap epsilon m h = constituentRawGridCount42 q d hd epsilon m h P := by
            dsimp only [cap]
            unfold constituentPooledGridCapacity42
            rw [if_neg hz, dif_pos hp]
          have hselected : ∀ r : Fin 6,
              (stagePopulationAt q (constituentGridParent27 d hd m h.val)
                (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 →
                0 < (P.selected r).card := by
            intro r hn
            have hr := hP r
            rw [if_neg hn] at hr
            have hquot : 0 < ((P.selected r).card : ℝ) /
                (constituentRegionalReserve33 q P r : ℝ) :=
              (Real.exp_pos _).trans_le hr
            rcases (div_pos_iff.mp hquot) with hpos | hneg
            · exact_mod_cast hpos.1
            · exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤
                (constituentRegionalReserve33 q P r : ℝ)) hneg.2).elim
          have hfresh := constituent_fresh_repair42 q hq d hd hb epsilon hepsilon.le
            m h P hz hselected
          have htruncate : Restricts
              (copiesZ (V epsilon m) (constituentGridTensorZ27 q d m h.val)).tensor
              (copiesZ (constituentRawGridCount42 q d hd epsilon m h P)
                (constituentGridTensorZ27 q d m h.val)).tensor := by
            simpa only [copiesZ] using OmegaBound.ADVXXZStage.famDS_copies_mono
              (R := ℤ) (hcap ▸ hmin) (constituentGridTensorZ27 q d m h.val).tensor
          exact ⟨0, polyDegeneratesAt_of_restricts (htruncate.trans hfresh)⟩
      let gridCard := Fintype.card (ConstituentFullGrid27 d m epsilon)
      let e : Fin gridCard ≃ ConstituentFullGrid27 d m epsilon :=
        (Fintype.equivFin (ConstituentFullGrid27 d m epsilon)).symm
      have hsum : ∀ x y z, (constituentOutputZ q d m epsilon).tensor x y z =
          ∑ i : Fin gridCard,
            (constituentGridTensorZ27 q d m (e i).val).tensor x y z := by
        intro x y z
        have hdcomp := constituentOutputZ_eq_sum_gridTensor42 (m := m) q d hd epsilon
        have hdxyz := congrFun (congrFun (congrFun hdcomp x) y) z
        have happ :
            ((∑ h : ConstituentFullGrid27 d m epsilon,
                (constituentGridTensorZ27 q d m h.val).tensor) :
              Tensor3 ℤ (constituentOutputZ q d m epsilon).X
                (constituentOutputZ q d m epsilon).Y
                (constituentOutputZ q d m epsilon).Z) x y z =
              ∑ h : ConstituentFullGrid27 d m epsilon,
                (constituentGridTensorZ27 q d m h.val).tensor x y z := by
          let f : ConstituentFullGrid27 d m epsilon →
              Tensor3 ℤ (constituentOutputZ q d m epsilon).X
                (constituentOutputZ q d m epsilon).Y
                (constituentOutputZ q d m epsilon).Z :=
            fun h => (constituentGridTensorZ27 q d m h.val).tensor
          change (∑ h, f h) x y z = ∑ h, f h x y z
          rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]
        calc
          _ = ((∑ h : ConstituentFullGrid27 d m epsilon,
              (constituentGridTensorZ27 q d m h.val).tensor) :
                Tensor3 ℤ (constituentOutputZ q d m epsilon).X
                  (constituentOutputZ q d m epsilon).Y
                  (constituentOutputZ q d m epsilon).Z) x y z := hdxyz
          _ = ∑ h : ConstituentFullGrid27 d m epsilon,
              (constituentGridTensorZ27 q d m h.val).tensor x y z := happ
          _ = _ := (Equiv.sum_comp e
            (fun h => (constituentGridTensorZ27 q d m h.val).tensor x y z)).symm
      have heach : ∀ i : Fin gridCard, ∃ degree, PolyDegeneratesAt ℤ degree
          (copiesZ (constituentRepairPool33 q p d b m)
            (constituentPlainInputZ q p (b*m) (3*epsilon))).tensor
          (copiesZ (V epsilon m)
            (constituentGridTensorZ27 q d m (e i).val)).tensor :=
        fun i => hpoly (e i)
      have hall := exists_polyDegeneratesAt_famDS_of_sum
        (copiesZ (constituentRepairPool33 q p d b m)
          (constituentPlainInputZ q p (b*m) (3*epsilon))).tensor
        (fun i : Fin gridCard =>
          (constituentGridTensorZ27 q d m (e i).val).tensor)
        (constituentOutputZ q d m epsilon).tensor hsum (V epsilon m) heach
      have hflat := polyDegeneratesAt_of_restricts
        (copiesZ_nested_restricts_mul gridCard (constituentRepairPool33 q p d b m)
          (constituentPlainInputZ q p (b*m) (3*epsilon)))
      obtain ⟨degree, hcombined⟩ := integral_polyDegeneratesAt_trans hflat
        (by simpa only [copiesZ] using hall.choose_spec)
      refine ⟨degree, ?_⟩
      simpa only [Q, gridCard, copiesZ] using hcombined

example : S_constituent_pooled_positive33 := constituent_pooled_positive33

end
end OmegaBound.ADVXXZGeneral
end
