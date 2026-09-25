import OmegaBound.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The matrix multiplication exponent `ω`

We define the exponent of matrix multiplication over a commutative semiring `R` as

  `ω(R) = inf { τ : R(⟨n,n,n⟩) = O(nᵗ) }`

and prove the fundamental transfer principle: a single rank decomposition
`R(⟨a,a,a⟩) ≤ r` bounds the exponent, `ω ≤ log_a r`.

## Main results

* `IsMMExponent` — the predicate `R(⟨n,n,n⟩) = O(nᵗ)`
* `omegaMM` — the exponent, as an infimum
* `isMMExponent_logb` — `R(⟨a,a,a⟩) ≤ r` implies `log_a r` is an exponent
* `omegaMM_le_logb` — hence `ω ≤ log_a r`
-/

open Tensor3 Finset

set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

namespace OmegaBound

/-! ## Rank is positive -/

/-- A tensor of rank zero is zero: the defining sum is empty. -/
theorem eq_zero_of_rankLE_zero {R : Type*} [CommSemiring R] {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] {T : Tensor3 R α β γ} (h : RankLE T 0) :
    T = 0 := by
  obtain ⟨A₁, A₂, A₃, hT⟩ := h
  funext a b c
  rw [hT]
  simp [act]

/-- `⟨n,n,n⟩` is nonzero for `n ≥ 1`, hence has positive rank. -/
theorem one_le_of_rankLE_matMul {R : Type*} [CommSemiring R] [Nontrivial R]
    {n r : ℕ} (hn : 1 ≤ n) (h : RankLE (Tensor3.matMul (R := R) n n n) r) : 1 ≤ r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have hz := eq_zero_of_rankLE_zero h
    have : Tensor3.matMul (R := R) n n n (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩)
        (⟨0, hn⟩, ⟨0, hn⟩) = 1 := by
      simp [Tensor3.matMul]
    rw [hz] at this
    exact zero_ne_one this
  · exact hr

/-! ## The exponent -/

variable (R : Type*) [CommSemiring R]

/-- `τ` is an exponent for matrix multiplication over `R` if the rank of `⟨n,n,n⟩`
is `O(nᵗ)`. -/
def IsMMExponent (τ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∃ r : ℕ, RankLE (Tensor3.matMul (R := R) n n n) r ∧ (r : ℝ) ≤ C * (n : ℝ) ^ τ

/-- **The exponent of matrix multiplication** over `R`. -/
noncomputable def omegaMM : ℝ := sInf {τ | IsMMExponent R τ}

variable {R}

/-- Every exponent is nonnegative.  (The true lower bound is `2`; nonnegativity is all
that is needed to make the infimum well behaved.) -/
theorem IsMMExponent.nonneg [Nontrivial R] {τ : ℝ} (h : IsMMExponent R τ) : 0 ≤ τ := by
  obtain ⟨C, hC⟩ := h
  by_contra hτ
  push_neg at hτ
  set p : ℝ := -τ with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  -- every `n ≥ 1` gives `1 ≤ C * n ^ τ`, i.e. `n ^ p ≤ C`
  have key : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ p ≤ C := by
    intro n hn
    obtain ⟨r, hr, hrC⟩ := hC n hn
    have h1 : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast one_le_of_rankLE_matMul hn hr
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ C * (n : ℝ) ^ τ := le_trans h1 hrC
    have h3 : (0 : ℝ) < (n : ℝ) ^ τ := Real.rpow_pos_of_pos hn0 τ
    have h4 : (n : ℝ) ^ p = ((n : ℝ) ^ τ)⁻¹ := by
      rw [hp, Real.rpow_neg (le_of_lt hn0)]
    have h5 : (1 : ℝ) / (n : ℝ) ^ τ ≤ C := (div_le_iff₀ h3).mpr (by linarith)
    rw [h4, ← one_div]
    exact h5
  have hC1 : (1 : ℝ) ≤ C := by simpa using key 1 le_rfl
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  -- but `n ^ p` is unbounded
  obtain ⟨m, hm⟩ := exists_nat_gt (C ^ (1 / p))
  set n : ℕ := max m 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hmn : C ^ (1 / p) < (n : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast le_max_left m 1)
  have hbase : (0 : ℝ) ≤ C ^ (1 / p) := Real.rpow_nonneg hC0 _
  have : C < (n : ℝ) ^ p := by
    have hlt := Real.rpow_lt_rpow hbase hmn hp0
    rwa [← Real.rpow_mul hC0, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one] at hlt
  exact absurd (key n hn1) (not_le.mpr this)

theorem bddBelow_isMMExponent [Nontrivial R] : BddBelow {τ | IsMMExponent R τ} :=
  ⟨0, fun _ hτ => hτ.nonneg⟩

/-! ## The transfer principle -/

/-- **A rank decomposition bounds the exponent.**  If `⟨a,a,a⟩` has rank at most `r`
(with `a ≥ 2`), then `log_a r` is an exponent for matrix multiplication. -/
theorem isMMExponent_logb [Nontrivial R] {a r : ℕ} (ha : 2 ≤ a)
    (h : RankLE (Tensor3.matMul (R := R) a a a) r) :
    IsMMExponent R (Real.logb a r) := by
  have hr1 : 1 ≤ r := one_le_of_rankLE_matMul (by omega) h
  set τ : ℝ := Real.logb a r with hτ
  have ha1 : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_trans one_pos ha1
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hτ0 : 0 ≤ τ := Real.logb_nonneg ha1 (by exact_mod_cast hr1)
  -- `a ^ τ = r`
  have hpow : (a : ℝ) ^ τ = (r : ℝ) := Real.rpow_logb ha0 ha1.ne' hr0
  refine ⟨(r : ℝ), fun n hn => ?_⟩
  -- least `k` with `n ≤ a ^ k`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n ≤ a ^ k := ⟨n, Nat.le_of_lt_succ (Nat.lt_succ_of_le
    (Nat.le_of_lt (Nat.lt_pow_self (by omega))))⟩
  classical
  have hex : ∃ m : ℕ, n ≤ a ^ m := ⟨k, hk⟩
  obtain ⟨K, hKle, hKmin⟩ : ∃ K, n ≤ a ^ K ∧ ∀ m, m < K → ¬ (n ≤ a ^ m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨r ^ K, ?_, ?_⟩
  · exact RankLE.mono (matMul_restricts_of_le n n n _ _ _ hKle hKle hKle)
      (RankLE.matMul_pow h K)
  · -- `r ^ K ≤ r * n ^ τ`
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · rw [hK0]
      simp only [pow_zero, Nat.cast_one]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hn) hτ0
      have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      nlinarith [hr1R, h1]
    · -- minimality: `a ^ (K-1) < n`
      have hprev : ¬ (n ≤ a ^ (K - 1)) := hKmin (K - 1) (by omega)
      push_neg at hprev
      have hprevR : ((a : ℝ) ^ (K - 1)) < (n : ℝ) := by exact_mod_cast hprev
      have hbase : (0 : ℝ) ≤ (a : ℝ) ^ (K - 1) := le_of_lt (pow_pos ha0 _)
      have hmono := Real.rpow_le_rpow hbase (le_of_lt hprevR) hτ0
      -- `(a ^ (K-1)) ^ τ = r ^ (K-1)`
      have hlhs : ((a : ℝ) ^ (K - 1)) ^ τ = (r : ℝ) ^ (K - 1) := by
        rw [← Real.rpow_natCast (a : ℝ) (K - 1), ← Real.rpow_mul (le_of_lt ha0),
          mul_comm, Real.rpow_mul (le_of_lt ha0), hpow, Real.rpow_natCast]
      rw [hlhs] at hmono
      have hsplit : (r : ℝ) ^ K = (r : ℝ) * (r : ℝ) ^ (K - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      calc ((r ^ K : ℕ) : ℝ) = (r : ℝ) ^ K := by push_cast; ring
        _ = (r : ℝ) * (r : ℝ) ^ (K - 1) := hsplit
        _ ≤ (r : ℝ) * (n : ℝ) ^ τ := by
              exact mul_le_mul_of_nonneg_left hmono (le_of_lt hr0)

/-- **The exponent is bounded by any rank decomposition.** -/
theorem omegaMM_le_logb [Nontrivial R] {a r : ℕ} (ha : 2 ≤ a)
    (h : RankLE (Tensor3.matMul (R := R) a a a) r) :
    omegaMM R ≤ Real.logb a r :=
  csInf_le bddBelow_isMMExponent (isMMExponent_logb ha h)

end OmegaBound
