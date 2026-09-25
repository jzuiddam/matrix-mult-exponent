import OmegaBound.ADVXXZGeneralEntropy
import OmegaBound.ADVXXZBlkCount

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem type_class_bounds {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (k : α → ℕ) (hk : ∑ a, k a = n) :
  let H := entropyNats (fun a => (k a : ℝ)/n)
  Real.exp ((n:ℝ)*H)/(n+1:ℝ)^Fintype.card α ≤
      (Fintype.card {x : Fin n → α // ∀ a, typeCnt x a = k a} : ℝ) ∧
  (Fintype.card {x : Fin n → α // ∀ a, typeCnt x a = k a} : ℝ) ≤
      Real.exp ((n:ℝ)*H) := by
  classical
  dsimp only
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk0 : ∀ a, k a = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff.mp hk) a (Finset.mem_univ a)
    simp [entropyNats, hk0, typeCnt]
  · cases isEmpty_or_nonempty α with
    | inl hempty =>
        letI := hempty
        have hn0 : n = 0 := by simpa using hk.symm
        exact (hn.ne' hn0).elim
    | inr hnonempty =>
        letI := hnonempty
        have hcard :
            Fintype.card {x : Fin n → α // ∀ a, typeCnt x a = k a} =
              Nat.multinomial Finset.univ k := by
          rw [Fintype.card_subtype]
          exact ADVXXZ.card_filter_typeCnt k hk
        have hH : entropyNats (fun a => (k a : ℝ) / n) =
            Entropy.H Finset.univ (Entropy.emp k n) := by
          simp [entropyNats, Entropy.H_eq_neg_sum, Entropy.emp]
        constructor
        · rw [hH, hcard, div_le_iff₀ (by positivity)]
          calc
            Real.exp ((n : ℝ) * Entropy.H Finset.univ (Entropy.emp k n)) ≤
                ((n : ℝ) + 1) ^ (Fintype.card α - 1) *
                  (Nat.multinomial Finset.univ k : ℝ) :=
              Entropy.exp_mul_H_le_multinomial k n hk hn
            _ ≤ ((n : ℝ) + 1) ^ Fintype.card α *
                  (Nat.multinomial Finset.univ k : ℝ) := by
              have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
                exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ hbase (Nat.sub_le _ _)) (Nat.cast_nonneg _)
            _ = (Nat.multinomial Finset.univ k : ℝ) *
                  ((n : ℝ) + 1) ^ Fintype.card α := by ring
        · rw [hH, hcard]
          exact Entropy.multinomial_le_exp_mul_H k n hk hn

end OmegaBound.ADVXXZGeneral
end
