import OmegaBound.ADVXXZGeneralIterateStagesInventory
import OmegaBound.ADVXXZGeneralIterateStagesGlobalData

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

/-- The stage schedule: the producer at level `l` receives `3^l ε` and emits `3^(l-1) ε`. -/
def iterateTolerance (l : ℕ) (ε : ℚ) : ℚ := (3 : ℚ) ^ l * ε

theorem iterateTolerance_pos (l : ℕ) {ε : ℚ} (hε : 0 < ε) :
    0 < iterateTolerance l ε := by
  simp [iterateTolerance, hε]

theorem iterateTolerance_nonnegative (l : ℕ) {ε : ℚ} (hε : 0 ≤ ε) :
    0 ≤ iterateTolerance l ε := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) hε

theorem three_mul_iterateTolerance (l : ℕ) (ε : ℚ) :
    3 * iterateTolerance l ε = iterateTolerance (l + 1) ε := by
  simp [iterateTolerance, pow_succ]
  ring

/-- Product of the normalized constituent pools for the valid stages below `n`. -/
noncomputable def iterateStageQThrough (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) : ℕ → ℚ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, ε, m =>
      if h : 2 ≤ n ∧ n ≤ C.top then
        iterateStageQThrough C hC hpool n ε m *
          (iterateStageData C hC hpool ⟨n, h⟩).Q (iterateTolerance (n - 1) ε) m
      else iterateStageQThrough C hC hpool n ε m

/-- Product of retained constituent copy counts for the valid stages below `n`. -/
noncomputable def iterateStageVThrough (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) : ℕ → ℚ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, ε, m =>
      if h : 2 ≤ n ∧ n ≤ C.top then
        iterateStageVThrough C hC hpool n ε m *
          (iterateStageData C hC hpool ⟨n, h⟩).V (iterateTolerance (n - 1) ε) m
      else iterateStageVThrough C hC hpool n ε m

/-- Sum of retained constituent rates for the valid stages below `n`. -/
noncomputable def iterateStageRateThrough (C : Certificate) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      if h : 2 ≤ n ∧ n ≤ C.top then
        iterateStageRateThrough C n + iterateStageRate C ⟨n, h⟩
      else iterateStageRateThrough C n

/-- Exact descending occurrence list accumulated by the constituent recursion below `n`. -/
noncomputable def iterateStageBoundaryThrough (C : Certificate) : ℕ → Inventory
  | 0 => []
  | n + 1 =>
      if h : 2 ≤ n ∧ n ≤ C.top then
        boundaryOccurrences27 (QAt C ⟨n, h⟩) ++ iterateStageBoundaryThrough C n
      else iterateStageBoundaryThrough C n

/-- Products of everywhere-positive pools remain everywhere positive. -/
theorem iterateStageQThrough_one (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) :
    ∀ n ε m, 1 ≤ iterateStageQThrough C hC hpool n ε m := by
  intro n
  induction n with
  | zero => simp [iterateStageQThrough]
  | succ n ih =>
      intro ε m
      rw [iterateStageQThrough]
      split_ifs with h
      · exact one_le_mul_of_one_le_of_one_le (ih ε m)
          ((iterateStageData C hC hpool ⟨n, h⟩).Q_one _ _)
      · exact ih ε m

/-- A product of two positive natural pools has sublinear logarithm. -/
theorem sublinear_log_mul_of_one_le {L : ℕ → ℕ} (Q R : ℕ → ℕ)
    (hQ : ∀ m, 1 ≤ Q m) (hR : ∀ m, 1 ≤ R m)
    (hsQ : Sublinear L (fun m => Real.log (Q m : ℝ)))
    (hsR : Sublinear L (fun m => Real.log (R m : ℝ))) :
    Sublinear L (fun m => Real.log ((Q m * R m : ℕ) : ℝ)) := by
  have hs := sublinear_add hsQ hsR
  have heq : (fun m => Real.log ((Q m * R m : ℕ) : ℝ)) =
      (fun m => Real.log (Q m : ℝ) + Real.log (R m : ℝ)) := by
    funext m
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hQ m))
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hR m))
  rw [heq]
  exact hs

/-- The recursively accumulated normalized stage pool is sublinear. -/
theorem iterateStageQThrough_sublinear (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) :
    ∀ n ε, 0 < ε → Sublinear (outerN C)
      (fun m => Real.log (iterateStageQThrough C hC hpool n ε m : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro ε hε
      simpa [iterateStageQThrough] using sublinear_log_one (outerN C)
  | succ n ih =>
      intro ε hε
      change Sublinear (outerN C) (fun m => Real.log
        ((if h : 2 ≤ n ∧ n ≤ C.top then
          iterateStageQThrough C hC hpool n ε m *
            (iterateStageData C hC hpool ⟨n, h⟩).Q
              (iterateTolerance (n - 1) ε) m
        else iterateStageQThrough C hC hpool n ε m : ℕ) : ℝ))
      split_ifs with h
      · apply sublinear_log_mul_of_one_le
          (fun m => iterateStageQThrough C hC hpool n ε m)
          (fun m => (iterateStageData C hC hpool ⟨n, h⟩).Q
            (iterateTolerance (n - 1) ε) m)
        · exact iterateStageQThrough_one C hC hpool n ε
        · exact (iterateStageData C hC hpool ⟨n, h⟩).Q_one _
        · exact ih ε hε
        · exact (iterateStageData C hC hpool ⟨n, h⟩).Q_sublinear _
            (iterateTolerance_pos _ hε)
      · exact ih ε hε

/-- `LowerRate` is unchanged by a fixed positive rescaling of its tolerance argument. -/
theorem lowerRate_tolerance_scale (O : ℕ → ℕ) (x : ℚ → ℕ → ℕ) (r : ℝ)
    (c : ℚ) (hc : 0 < c) (h : LowerRate O x r) :
    LowerRate O (fun ε m => x (c * ε) m) r := by
  intro δ hδ
  obtain ⟨ε₀, hε₀, htail⟩ := h δ hδ
  refine ⟨ε₀ / c, div_pos hε₀ hc, fun ε hε hεle => ?_⟩
  apply htail (c * ε) (mul_pos hc hε)
  have hc0 : 0 ≤ c := hc.le
  calc
    c * ε ≤ c * (ε₀ / c) := mul_le_mul_of_nonneg_left hεle hc0
    _ = ε₀ := by field_simp

/-- Products add lower rates. -/
theorem lowerRate_mul (O : ℕ → ℕ) (x y : ℚ → ℕ → ℕ) (r s : ℝ)
    (hx : LowerRate O x r) (hy : LowerRate O y s) :
    LowerRate O (fun ε m => x ε m * y ε m) (r + s) := by
  intro δ hδ
  have hh : 0 < δ / 2 := by positivity
  obtain ⟨εx, hεx, htx⟩ := hx (δ / 2) hh
  obtain ⟨εy, hεy, hty⟩ := hy (δ / 2) hh
  refine ⟨min εx εy, lt_min hεx hεy, fun ε hε hεmin => ?_⟩
  obtain ⟨Mx, hMx⟩ := htx ε hε (hεmin.trans (min_le_left _ _))
  obtain ⟨My, hMy⟩ := hty ε hε (hεmin.trans (min_le_right _ _))
  refine ⟨max Mx My, fun m hm => ?_⟩
  obtain ⟨hxone, hxlog⟩ := hMx m (le_trans (Nat.le_max_left _ _) hm)
  obtain ⟨hyone, hylog⟩ := hMy m (le_trans (Nat.le_max_right _ _) hm)
  refine ⟨one_le_mul_of_one_le_of_one_le hxone hyone, ?_⟩
  rw [Nat.cast_mul, Real.log_mul]
  · nlinarith
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hxone)
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hyone)

/-- The recursively accumulated retained count has the recursively accumulated rate. -/
theorem iterateStageVThrough_lowerRate (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) :
    ∀ n, LowerRate (outerN C) (iterateStageVThrough C hC hpool n)
      (iterateStageRateThrough C n) := by
  intro n
  induction n with
  | zero =>
      simpa [iterateStageVThrough, iterateStageRateThrough] using
        lowerRate_one_zero (outerN C)
  | succ n ih =>
      change LowerRate (outerN C)
        (fun ε m => if h : 2 ≤ n ∧ n ≤ C.top then
          iterateStageVThrough C hC hpool n ε m *
            (iterateStageData C hC hpool ⟨n, h⟩).V
              (iterateTolerance (n - 1) ε) m
        else iterateStageVThrough C hC hpool n ε m)
        (if h : 2 ≤ n ∧ n ≤ C.top then
          iterateStageRateThrough C n + iterateStageRate C ⟨n, h⟩
        else iterateStageRateThrough C n)
      split_ifs with h
      · have hs := (iterateStageData C hC hpool ⟨n, h⟩).V_lowerRate
        have hscaled := lowerRate_tolerance_scale (outerN C)
          (iterateStageData C hC hpool ⟨n, h⟩).V (iterateStageRate C ⟨n, h⟩)
          ((3 : ℚ) ^ (n - 1)) (by positivity) hs
        simpa only [iterateTolerance] using
          lowerRate_mul (outerN C) (iterateStageVThrough C hC hpool n)
            (fun ε m => (iterateStageData C hC hpool ⟨n, h⟩).V
              (iterateTolerance (n - 1) ε) m)
            (iterateStageRateThrough C n) (iterateStageRate C ⟨n, h⟩) ih hscaled
      · exact ih

private def stageFinEquivIterate (top : ℕ) :
    {i : Fin (top + 1) // 2 ≤ i.val} ≃ Stage top where
  toFun i := ⟨i.1.val, i.2, Nat.le_of_lt_succ i.1.isLt⟩
  invFun l := ⟨⟨l.val, Nat.lt_succ_of_le l.2.2⟩, l.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex a `finRange` stage sum by the certificate's dependent `Stage` type. -/
theorem stage_sum_finRange_for_iterate {M : Type*} [AddCommMonoid M]
    (top : ℕ) (f : Stage top → M) :
    ((List.finRange (top + 1)).map fun i =>
      if h : 2 ≤ i.val ∧ i.val ≤ top then f ⟨i.val, h⟩ else 0).sum =
      ∑ l : Stage top, f l := by
  classical
  let e := stageFinEquivIterate top
  calc
    _ = ((List.finRange (top + 1)).map fun i =>
          if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro i _hi
            have hi : i.val ≤ top := Nat.le_of_lt_succ i.isLt
            split_ifs <;> simp_all [e, stageFinEquivIterate]
    _ = ∑ i : Fin (top + 1), if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0 := by
      rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    _ = ∑ i : {i : Fin (top + 1) // 2 ≤ i.val}, f (e i) := by
      let p := fun i : Fin (top + 1) => 2 ≤ i.val
      let g := fun i : Fin (top + 1) => if h : p i then f (e ⟨i, h⟩) else 0
      letI : Fintype {i : Fin (top + 1) // p i} := Fintype.ofFinite _
      have hfilter : (∑ i : Fin (top + 1), g i) =
          (∑ i ∈ Finset.univ.filter p, g i) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hnot
        have hn : ¬ p i := by
          intro hp
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩)
        simp [g, hn]
      rw [show (∑ i : Fin (top + 1),
          if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0) =
          ∑ i : Fin (top + 1), g i by rfl, hfilter]
      rw [Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp [p]) g]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [g]
      rw [dif_pos i.property]
    _ = ∑ l : Stage top, f l := Equiv.sum_comp e f

private theorem iterateStageRateThrough_eq_range (C : Certificate) : ∀ n,
    iterateStageRateThrough C n =
      ((List.range n).map fun i =>
        if h : 2 ≤ i ∧ i ≤ C.top then iterateStageRate C ⟨i, h⟩ else 0).sum := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateStageRateThrough, List.range_succ, List.map_append, List.sum_append, ih]
      simp
      split_ifs <;> simp

/-- At the top level, the recursive retained rate is the certificate's stage sum. -/
theorem iterateStageRateThrough_top (C : Certificate) :
    iterateStageRateThrough C (C.top + 1) = ∑ l : Stage C.top, iterateStageRate C l := by
  rw [iterateStageRateThrough_eq_range]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.map_map, Function.comp_apply]
  exact stage_sum_finRange_for_iterate C.top (iterateStageRate C)

private theorem iterateStageBoundaryThrough_eq_range (C : Certificate) : ∀ n,
    iterateStageBoundaryThrough C n =
      ((List.range n).reverse).flatMap fun i =>
        if h : 2 ≤ i ∧ i ≤ C.top then boundaryOccurrences27 (QAt C ⟨i, h⟩) else [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateStageBoundaryThrough, List.range_succ, List.reverse_append,
        List.flatMap_append, ih]
      simp
      split_ifs <;> rfl

/-- The recursion's descending occurrence list is the accumulated list `accumulatedBoundary27`. -/
theorem global_append_stageBoundaryThrough_top (C : Certificate) :
    boundaryOccurrences27 (G C) ++ iterateStageBoundaryThrough C (C.top + 1) =
      accumulatedBoundary27 C := by
  rw [iterateStageBoundaryThrough_eq_range, accumulatedBoundary27]
  congr 1
  rw [← List.map_coe_finRange_eq_range, ← List.map_reverse, List.flatMap_map]

end
end OmegaBound.ADVXXZGeneral
end
