import OmegaBound.ADVXXZGeneralCExact33Reserve

set_option autoImplicit false

/-!
# `constituent_repair_pool_sublinear33`

`log (constituentRepairPool33 q p d b m)` is `o(cLength p b m)`.

The reserve of a region of population `N` is `4^(3*Nat.log N (3^(w*N)) + 1)`, so its logarithm is
`Θ(N/log N)`; six of them and `N_r ≤ 2*cLength` (`stagePopulation_n_le`) give `o(cLength)`.
`ADVXXZGeneralRepair.repair_sublinear` cannot be reused: it is stated for the base
`max 2 (2*L m)`, whereas `constituentRepairPool33` uses the population `N` itself as the base, and
its `natLog_le_div` is `private`.  The two base-splitting lemmas below are the base-`N` analogues.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
open StageCandidateRaw
noncomputable section

/-- `Nat.log D (3^n) ≤ 2*n` for EVERY base `D` (including `D ≤ 1`, where the log is `0`). -/
theorem natLog_three_pow_le (D n : ℕ) : Nat.log D (3^n) ≤ 2*n := by
  rcases Nat.lt_or_ge D 2 with hD | hD
  · rw [Nat.log_of_left_le_one (by omega)]
    exact Nat.zero_le _
  · have hpos : 0 < (4:ℕ)^n := pow_pos (by norm_num) n
    have hlt : 3^n < D^(2*n+1) := by
      calc (3:ℕ)^n ≤ 4^n := Nat.pow_le_pow_left (by norm_num) n
        _ < 4^n * 2 := by omega
        _ = 2^(2*n+1) := by rw [pow_succ, pow_mul]; norm_num
        _ ≤ D^(2*n+1) := Nat.pow_le_pow_left hD _
    have hne : (3:ℕ)^n ≠ 0 := by positivity
    have := Nat.log_lt_of_lt_pow hne hlt
    omega

/-- The base-`D` analogue of the `private natLog_le_div` of `ADVXXZGeneralRepair.lean`. -/
theorem natLog_le_div_base (k n a D : ℕ) (hk : 0 < k)
    (hbase : 3^k ≤ D) (ha : a ≤ 3^n) : Nat.log D a ≤ n / k := by
  have hexponent : n < k * (n / k + 1) := Nat.lt_mul_div_succ n hk
  have hpow : 3^n < D^(n / k + 1) := by
    calc (3:ℕ)^n < 3^(k * (n / k + 1)) := Nat.pow_lt_pow_right (by omega) hexponent
      _ = (3^k)^(n / k + 1) := by rw [Nat.pow_mul]
      _ ≤ D^(n / k + 1) := Nat.pow_le_pow_left hbase (n / k + 1)
  have hlog := Nat.log_lt_of_lt_pow' (by simp : n / k + 1 ≠ 0) (lt_of_le_of_lt ha hpow)
  omega

/-- The split that makes the pool sublinear: a constant `2*w*3^k` for small populations, and
`(w*N)/k` — an arbitrarily small multiple of `N` — for large ones. -/
theorem natLog_reserve_bound (k w N : ℕ) (hk : 0 < k) :
    Nat.log N (3^(w*N)) ≤ 2*w*3^k + (w*N)/k := by
  by_cases hbase : 3^k ≤ N
  · exact le_trans (natLog_le_div_base k (w*N) (3^(w*N)) N hk hbase (le_refl _))
      (Nat.le_add_left _ _)
  · push_neg at hbase
    have h2 : N ≤ 3^k := by omega
    calc Nat.log N (3^(w*N)) ≤ 2*(w*N) := natLog_three_pow_le N (w*N)
      _ = (2*w)*N := by ring
      _ ≤ (2*w)*3^k := Nat.mul_le_mul (le_refl (2*w)) h2
      _ = 2*w*3^k := by ring
      _ ≤ 2*w*3^k + (w*N)/k := Nat.le_add_right _ _

/-- Each pool factor is at most `4^(3*(2*w*3^k + (w*N_r)/k)+1)`. -/
theorem repairPoolFactor_le (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (k : ℕ) (hk : 0 < k) :
    constituentRepairPoolFactor33 q p d b m r
      ≤ 4 ^ (3*(2*w*3^k + (w*(stagePopulationAt q p d b m r).n)/k) + 1) := by
  unfold constituentRepairPoolFactor33
  split_ifs with hz
  · exact Nat.one_le_pow _ _ (by norm_num)
  · unfold repairReserve
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hsum : (∑ _W : Side, Nat.log ((stagePopulationAt q p d b m r).n)
        (3^(w*(stagePopulationAt q p d b m r).n)))
        = 3 * Nat.log ((stagePopulationAt q p d b m r).n)
            (3^(w*(stagePopulationAt q p d b m r).n)) := by
      rw [Finset.sum_const, Finset.card_univ,
        show Fintype.card Side = 3 from by decide +kernel, smul_eq_mul]
    rw [hsum]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (le_refl 3) (natLog_reserve_bound k w _ hk)) 1

/-- The whole pool, bounded by a power of `4` whose exponent is a constant plus `O(cLength/k)`. -/
theorem repairPool_le (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m k : ℕ) (hk : 0 < k) :
    constituentRepairPool33 q p d b m
      ≤ 4 ^ (18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6) := by
  classical
  rw [constituentRepairPool33_eq]
  calc (∏ r : Fin 6, constituentRepairPoolFactor33 q p d b m r)
      ≤ ∏ _r : Fin 6, 4 ^ (3*(2*w*3^k + (w*(2*cLength p b m))/k) + 1) := by
        refine Finset.prod_le_prod' (fun r _ => ?_)
        refine le_trans (repairPoolFactor_le q p d b m r k hk) ?_
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have hdiv : (w*(stagePopulationAt q p d b m r).n)/k ≤ (w*(2*cLength p b m))/k :=
          Nat.div_le_div_right
            (Nat.mul_le_mul (le_refl w) (stagePopulation_n_le q p d b m r))
        exact Nat.add_le_add_right
          (Nat.mul_le_mul (le_refl 3) (Nat.add_le_add_left hdiv (2*w*3^k))) 1
    _ = (4 ^ (3*(2*w*3^k + (w*(2*cLength p b m))/k) + 1))^(6:ℕ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = 4 ^ ((3*(2*w*3^k + (w*(2*cLength p b m))/k) + 1)*6) := (pow_mul 4 _ 6).symm
    _ = 4 ^ (18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6) := by
        congr 1
        ring

theorem repairPool_pos (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) : 0 < constituentRepairPool33 q p d b m := by
  rw [constituentRepairPool33_eq]
  refine Finset.prod_pos (fun r _ => ?_)
  unfold constituentRepairPoolFactor33
  split_ifs
  · norm_num
  · exact repairReserve_pos _ _

theorem le_cLength (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (hb : 0 < b) : m ≤ cLength p b m := by
  have hbase : 1 ≤ constituentBaseTotal p := by
    rw [constituentBaseTotal]
    refine le_trans (p.baseN_pos ⟨0, p.terms_nonempty⟩) ?_
    exact Finset.single_le_sum (f := p.baseN) (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
  calc m = 1 * (1 * m) := by ring
    _ ≤ constituentBaseTotal p * (b*m) :=
        Nat.mul_le_mul hbase (Nat.mul_le_mul hb (le_refl m))
    _ = cLength p b m := rfl

/-- **The repair pool is sublinear.** -/
theorem constituent_repair_pool_sublinear33
    (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) :
  Sublinear (cLength p b)
    (fun m => Real.log (constituentRepairPool33 q p d b m : ℝ)) := by
  classical
  intro δ hδ
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  -- a base `3^k` making the linear part of the exponent cost less than `δ/2`
  obtain ⟨k, hkpos, hkbig⟩ :
      ∃ k : ℕ, 0 < k ∧ 72 * (w:ℝ) * Real.log 4 / δ < (k:ℝ) := by
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (72 * (w:ℝ) * Real.log 4 / δ)
    exact ⟨k₀ + 1, Nat.succ_pos _, by push_cast; linarith⟩
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have h72 : 72 * (w:ℝ) * Real.log 4 < (k:ℝ) * δ := (div_lt_iff₀ hδ).mp hkbig
  -- a threshold `M` making the constant part of the exponent cost less than `δ/2`
  obtain ⟨M, hM⟩ :=
    exists_nat_gt (2*((18*((2*w*3^k : ℕ):ℝ) + 6) * Real.log 4)/δ)
  refine ⟨M, fun m hm => ?_⟩
  have hL0 : (0:ℝ) ≤ (cLength p b m : ℝ) := by positivity
  have hLm : (m:ℝ) ≤ (cLength p b m : ℝ) := by
    exact_mod_cast le_cLength q p d b m hb.1
  have hposPool : 0 < constituentRepairPool33 q p d b m := repairPool_pos q p d b m
  have hge1 : (1:ℝ) ≤ (constituentRepairPool33 q p d b m : ℝ) := by exact_mod_cast hposPool
  have hnn : 0 ≤ Real.log (constituentRepairPool33 q p d b m : ℝ) := Real.log_nonneg hge1
  show |Real.log (constituentRepairPool33 q p d b m : ℝ)| ≤ δ * (cLength p b m : ℝ)
  rw [abs_of_nonneg hnn]
  -- the exponent bound, transported to `ℝ`
  have hpoolR : (constituentRepairPool33 q p d b m : ℝ)
      ≤ (4:ℝ) ^ (18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6) := by
    exact_mod_cast repairPool_le q p d b m k hkpos
  have hlogpool : Real.log (constituentRepairPool33 q p d b m : ℝ)
      ≤ ((18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6 : ℕ) : ℝ) * Real.log 4 := by
    have hstep := Real.log_le_log (by linarith) hpoolR
    rwa [Real.log_pow] at hstep
  -- the linear part of the exponent
  have hXle : (((w*(2*cLength p b m))/k : ℕ) : ℝ)
      ≤ 2*(w:ℝ)*(cLength p b m : ℝ)/(k:ℝ) := by
    refine le_trans (Nat.cast_div_le :
      (((w*(2*cLength p b m))/k : ℕ) : ℝ)
        ≤ ((w*(2*cLength p b m) : ℕ):ℝ) / (k:ℝ)) ?_
    have hnum : ((w*(2*cLength p b m) : ℕ) : ℝ)
        = 2*(w:ℝ)*(cLength p b m : ℝ) := by push_cast; ring
    rw [hnum]
  have hterm : 18 * (((w*(2*cLength p b m))/k : ℕ) : ℝ) * Real.log 4
      ≤ (δ/2) * (cLength p b m : ℝ) := by
    have hbig : 18 * (((w*(2*cLength p b m))/k : ℕ) : ℝ) * Real.log 4
        ≤ 18 * (2*(w:ℝ)*(cLength p b m : ℝ)/(k:ℝ)) * Real.log 4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hXle (by norm_num : (0:ℝ) ≤ 18)) hlog4.le
    have hkey : 18 * (2*(w:ℝ)*(cLength p b m : ℝ)/(k:ℝ)) * Real.log 4
        ≤ (δ/2) * (cLength p b m : ℝ) := by
      rw [show 18 * (2*(w:ℝ)*(cLength p b m : ℝ)/(k:ℝ)) * Real.log 4
          = (36*(w:ℝ)*Real.log 4*(cLength p b m : ℝ))/(k:ℝ) by ring,
        div_le_iff₀ hkR]
      have hmul := mul_le_mul_of_nonneg_right h72.le hL0
      nlinarith [hmul, hL0]
    linarith
  -- the constant part of the exponent
  have hconst : (18*((2*w*3^k : ℕ):ℝ) + 6) * Real.log 4
      ≤ (δ/2) * (cLength p b m : ℝ) := by
    have hmR : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have h1 : 2*((18*((2*w*3^k : ℕ):ℝ) + 6) * Real.log 4)/δ < (m:ℝ) :=
      lt_of_lt_of_le hM hmR
    have h2 : 2*((18*((2*w*3^k : ℕ):ℝ) + 6) * Real.log 4) < (m:ℝ) * δ :=
      (div_lt_iff₀ hδ).mp h1
    have h3 : (m:ℝ) * δ ≤ (cLength p b m : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hLm hδ.le
    linarith
  have hEcast : ((18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6 : ℕ) : ℝ)
      = (18*((2*w*3^k : ℕ):ℝ) + 6) + 18 * (((w*(2*cLength p b m))/k : ℕ) : ℝ) := by
    push_cast; ring
  calc Real.log (constituentRepairPool33 q p d b m : ℝ)
      ≤ ((18*(2*w*3^k) + 18*((w*(2*cLength p b m))/k) + 6 : ℕ) : ℝ) * Real.log 4 := hlogpool
    _ = (18*((2*w*3^k : ℕ):ℝ) + 6) * Real.log 4
        + 18 * (((w*(2*cLength p b m))/k : ℕ) : ℝ) * Real.log 4 := by rw [hEcast]; ring
    _ ≤ (δ/2) * (cLength p b m : ℝ) + (δ/2) * (cLength p b m : ℝ) := add_le_add hconst hterm
    _ = δ * (cLength p b m : ℝ) := by ring

end
end OmegaBound.ADVXXZGeneral
end
