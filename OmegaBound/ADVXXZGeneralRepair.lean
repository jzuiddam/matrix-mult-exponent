import OmegaBound.ADVXXZGeneralRates

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def repairReserve (D : ℕ) (parts : Side → ℕ) : ℕ :=
  4^((∑ W, Nat.log D (parts W))+1)

def repairedCopies (good D : ℕ) (parts : Side → ℕ) : ℕ :=
  good / repairReserve D parts

def repairGroup (good reserve k : ℕ) : Finset ℕ :=
  (Finset.range good).filter (fun j => k*reserve ≤ j ∧ j < (k+1)*reserve)

theorem repairReserve_pos (D : ℕ) (parts : Side → ℕ) :
    0 < repairReserve D parts := by
  simp [repairReserve]

theorem repairedCopies_mul_reserve_le (good D : ℕ) (parts : Side → ℕ) :
    repairedCopies good D parts * repairReserve D parts ≤ good := by
  exact Nat.div_mul_le_self good (repairReserve D parts)

@[simp] theorem mem_repairGroup {good reserve k j : ℕ} :
    j ∈ repairGroup good reserve k ↔
      j < good ∧ k*reserve ≤ j ∧ j < (k+1)*reserve := by
  simp [repairGroup]

theorem repairGroup_disjoint {good reserve k l : ℕ} (hkl : k ≠ l) :
    Disjoint (repairGroup good reserve k) (repairGroup good reserve l) := by
  wlog h : k < l generalizing k l
  · exact (this hkl.symm (lt_of_le_of_ne (Nat.le_of_not_gt h) hkl.symm)).symm
  rw [Finset.disjoint_left]
  intro j hjk hjl
  have hstep : (k+1)*reserve ≤ l*reserve :=
    Nat.mul_le_mul_right reserve (Nat.succ_le_iff.mpr h)
  rw [mem_repairGroup] at hjk hjl
  omega

theorem repairGroup_card {good reserve k : ℕ} (hk : k < good / reserve) :
    (repairGroup good reserve k).card = reserve := by
  have hupper : (k+1)*reserve ≤ good := by
    calc
      (k+1)*reserve ≤ (good / reserve)*reserve :=
        Nat.mul_le_mul_right reserve (Nat.succ_le_iff.mpr hk)
      _ ≤ good := Nat.div_mul_le_self good reserve
  have hgroup : repairGroup good reserve k = Finset.Ico (k*reserve) ((k+1)*reserve) := by
    ext j
    simp only [mem_repairGroup, Finset.mem_Ico]
    omega
  rw [hgroup, Nat.card_Ico]
  simp [Nat.add_mul]

private theorem natLog_le_div (k n a : ℕ) (hk : 0 < k)
    (hbase : 3^k ≤ max 2 (2*n)) (ha : a ≤ 3^n) :
    Nat.log (max 2 (2*n)) a ≤ n / k := by
  have hexponent : n < k * (n / k + 1) := Nat.lt_mul_div_succ n hk
  have hpow : 3^n < (max 2 (2*n))^(n / k + 1) := by
    calc
      3^n < 3^(k * (n / k + 1)) :=
        Nat.pow_lt_pow_right (by omega) hexponent
      _ = (3^k)^(n / k + 1) := by rw [Nat.pow_mul]
      _ ≤ (max 2 (2*n))^(n / k + 1) :=
        Nat.pow_le_pow_left hbase (n / k + 1)
  have hlog := Nat.log_lt_of_lt_pow'
    (by simp : n / k + 1 ≠ 0) (lt_of_le_of_lt ha hpow)
  omega

private theorem sum_natLog_le (k n : ℕ) (parts : Side → ℕ) (hk : 0 < k)
    (hbase : 3^k ≤ max 2 (2*n)) (hparts : ∀ W, parts W ≤ 3^n) :
    (∑ W, Nat.log (max 2 (2*n)) (parts W)) ≤ 3 * (n / k) := by
  calc
    (∑ W, Nat.log (max 2 (2*n)) (parts W)) ≤ ∑ _W : Side, n / k :=
      Finset.sum_le_sum fun W _ => natLog_le_div k n (parts W) hk hbase (hparts W)
    _ = 3 * (n / k) := by
      rw [Finset.sum_const, Finset.card_univ,
        show Fintype.card Side = 3 by decide +kernel]
      simp

theorem repair_sublinear (L : ℕ → ℕ) (parts : Side → ℕ → ℕ)
    (hL : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hparts : ∀ W m, parts W m ≤ 3^(L m)) :
  Sublinear L (fun m => Real.log
    (repairReserve (max 2 (2*L m)) (fun W => parts W m) : ℝ)) := by
  intro δ hδ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ,
      1 / (k₀ + 1 : ℝ) < δ / (6 * Real.log 4) :=
    exists_nat_one_div_lt (by positivity)
  let k := k₀ + 1
  have hk : 0 < k := by omega
  have hk_small : 1 / (k : ℝ) < δ / (6 * Real.log 4) := by
    simpa [k] using hk₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * Real.log 4 / δ < N :=
    exists_nat_gt (2 * Real.log 4 / δ)
  have hEventually := Filter.tendsto_atTop.1 hL (max (3^k) N)
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨M, hM⟩ := hEventually
  refine ⟨M, fun m hm => ?_⟩
  have hlarge := hM m hm
  have hbase : 3^k ≤ max 2 (2*L m) := by omega
  have hsum := sum_natLog_le k (L m) (fun W => parts W m) hk hbase
    (fun W => hparts W m)
  have hexponent :
      (∑ W, Nat.log (max 2 (2*L m)) (parts W m)) + 1 ≤
        3 * (L m / k) + 1 := Nat.add_le_add_right hsum 1
  have hlog_eq :
      Real.log (repairReserve (max 2 (2*L m)) (fun W => parts W m) : ℝ) =
        ((∑ W, Nat.log (max 2 (2*L m)) (parts W m)) + 1 : ℕ) * Real.log 4 := by
    rw [repairReserve, Nat.cast_pow, Real.log_pow]
    norm_num
  have hlog_nonneg :
      0 ≤ Real.log (repairReserve (max 2 (2*L m)) (fun W => parts W m) : ℝ) := by
    rw [hlog_eq]
    positivity
  rw [abs_of_nonneg hlog_nonneg, hlog_eq]
  have hexponent_real :
      (((∑ W, Nat.log (max 2 (2*L m)) (parts W m)) + 1 : ℕ) : ℝ) ≤
        3 * ((L m / k : ℕ) : ℝ) + 1 := by
    exact_mod_cast hexponent
  calc
    (((∑ W, Nat.log (max 2 (2*L m)) (parts W m)) + 1 : ℕ) : ℝ) * Real.log 4
        ≤ (3 * ((L m / k : ℕ) : ℝ) + 1) * Real.log 4 :=
      mul_le_mul_of_nonneg_right hexponent_real hlog4.le
    _ ≤ (3 * ((L m : ℝ) / (k : ℝ)) + 1) * Real.log 4 := by
      gcongr
      exact (Nat.cast_div_le : ((L m / k : ℕ) : ℝ) ≤ (L m : ℝ) / (k : ℝ))
    _ ≤ δ * (L m : ℝ) := by
      have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk
      have hcoefficient : 3 * Real.log 4 / (k : ℝ) < δ / 2 := by
        calc
          3 * Real.log 4 / (k : ℝ) =
              (3 * Real.log 4) * (1 / (k : ℝ)) := by ring
          _ < (3 * Real.log 4) * (δ / (6 * Real.log 4)) :=
            mul_lt_mul_of_pos_left hk_small (by positivity)
          _ = δ / 2 := by
            field_simp [hlog4.ne']
            <;> ring
      have hL_nonneg : 0 ≤ (L m : ℝ) := by positivity
      have hfirst :
          (3 * ((L m : ℝ) / (k : ℝ))) * Real.log 4 ≤
            (δ / 2) * (L m : ℝ) := by
        calc
          (3 * ((L m : ℝ) / (k : ℝ))) * Real.log 4 =
              (3 * Real.log 4 / (k : ℝ)) * (L m : ℝ) := by ring
          _ ≤ (δ / 2) * (L m : ℝ) :=
            mul_le_mul_of_nonneg_right hcoefficient.le hL_nonneg
      have hNlarge : (N : ℝ) ≤ (L m : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_max_right (3^k) N) hlarge)
      have htail : Real.log 4 ≤ (δ / 2) * (L m : ℝ) := by
        have hratio : 2 * Real.log 4 / δ < (L m : ℝ) := lt_of_lt_of_le hN hNlarge
        have := (div_lt_iff₀ hδ).mp hratio
        nlinarith
      nlinarith

end OmegaBound.ADVXXZGeneral
end
