import OmegaBound.ADVXXZGeneralRates
import OmegaBound.ADVXXZGeneralMap
import OmegaBound.ADVXXZGeneralTensorCopiesZ

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- A copy lower bound with a tolerance-vanishing rate loss and a sublinear finite-scale loss
gives the universal rational tolerance tail required by `LowerRate`. -/
theorem copyBound_vanishing_loss_lowerRate
    (L : ℕ → ℕ) (rate : ℝ) (V : ℚ → ℕ → ℕ)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hd : VanishesWithTolerance delta) (hl : Loss L ell)
    (hV : CopyBound L rate delta ell V) : LowerRate L V rate := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨ε₀, hε₀, hsmall⟩ := hd.2 (δ / 2) hhalf
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨M₁, hM₁⟩ := hl.2 ε hε (δ / 2) hhalf
  obtain ⟨M₂, hM₂⟩ := hV ε hε
  refine ⟨max M₁ M₂, fun m hm => ?_⟩
  have hexp := hM₂ m (le_trans (Nat.le_max_right _ _) hm)
  have hpositive : 0 < (V ε m : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hnat : 0 < V ε m := by exact_mod_cast hpositive
  refine ⟨hnat, ?_⟩
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hdelta : delta ε ≤ δ / 2 :=
    (le_abs_self _).trans (hsmall ε hε hεle)
  have hell : ell ε m ≤ δ / 2 * (L m : ℝ) :=
    (le_abs_self _).trans (hM₁ m (le_trans (Nat.le_max_left _ _) hm))
  have hlength : (0 : ℝ) ≤ (L m : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Normalise a natural copy pool so it is positive at every scale. -/
def positiveCopyPool (Q : ℕ → ℕ) (m : ℕ) : ℕ := max 1 (Q m)

theorem positiveCopyPool_one_le (Q : ℕ → ℕ) (m : ℕ) :
    1 ≤ positiveCopyPool Q m := by
  exact Nat.le_max_left _ _

/-- Lean's convention `log 0 = 0` makes positive normalisation logarithmically free. -/
theorem positiveCopyPool_log (Q : ℕ → ℕ) (m : ℕ) :
    Real.log (positiveCopyPool Q m : ℝ) = Real.log (Q m : ℝ) := by
  by_cases h : Q m = 0
  · simp [positiveCopyPool, h]
  · rw [positiveCopyPool, max_eq_right (Nat.one_le_iff_ne_zero.mpr h)]

theorem positiveCopyPool_sublinear (L Q : ℕ → ℕ)
    (hQ : Sublinear L (fun m => Real.log (Q m : ℝ))) :
    Sublinear L (fun m => Real.log (positiveCopyPool Q m : ℝ)) := by
  simpa only [positiveCopyPool_log] using hQ

theorem positiveCopyPool_eq_of_one_le (Q : ℕ → ℕ) {m : ℕ}
    (hQ : 1 ≤ Q m) : positiveCopyPool Q m = Q m := by
  exact max_eq_right hQ

/-- Above a producer's positivity threshold, its polynomial witness is unchanged by `max 1`. -/
theorem positiveCopyPool_polyDegeneratesAt
    (Q : ℕ → ℕ) {T U : ITensor} {N m : ℕ} (hQ : 1 ≤ Q m)
    (h : PolyDegeneratesAt ℤ N (copiesZ (Q m) T).tensor U.tensor) :
    PolyDegeneratesAt ℤ N (copiesZ (positiveCopyPool Q m) T).tensor U.tensor := by
  rw [positiveCopyPool_eq_of_one_le Q hQ]
  exact h

private theorem sublinear_zero (L : ℕ → ℕ) : Sublinear L (fun _ => 0) := by
  intro δ hδ
  exact ⟨0, fun m _ => by simp [mul_nonneg hδ.le (Nat.cast_nonneg (L m))]⟩

theorem sublinear_add {L : ℕ → ℕ} {f g : ℕ → ℝ}
    (hf : Sublinear L f) (hg : Sublinear L g) :
    Sublinear L (fun m => f m + g m) := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨Mf, hMf⟩ := hf (δ / 2) hhalf
  obtain ⟨Mg, hMg⟩ := hg (δ / 2) hhalf
  refine ⟨max Mf Mg, fun m hm => ?_⟩
  have hf' := hMf m (le_trans (Nat.le_max_left _ _) hm)
  have hg' := hMg m (le_trans (Nat.le_max_right _ _) hm)
  calc
    |f m + g m| ≤ |f m| + |g m| := abs_add_le _ _
    _ ≤ δ / 2 * (L m : ℝ) + δ / 2 * (L m : ℝ) := add_le_add hf' hg'
    _ = δ * (L m : ℝ) := by ring

theorem sublinear_finset_sum {L : ℕ → ℕ} {J : Type*}
    (s : Finset J) (f : J → ℕ → ℝ) (hf : ∀ j ∈ s, Sublinear L (f j)) :
    Sublinear L (fun m => ∑ j ∈ s, f j m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sublinear_zero L
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact sublinear_add (hf a (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem log_nat_prod_eq_sum {J : Type*} [Fintype J]
    (Q : J → ℕ → ℕ) (hQ : ∀ j m, 1 ≤ Q j m) (m : ℕ) :
    Real.log ((∏ j, Q j m : ℕ) : ℝ) = ∑ j, Real.log (Q j m : ℝ) := by
  classical
  rw [Nat.cast_prod]
  exact Real.log_prod (fun j _ => by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hQ j m)))

/-- The logarithm of a fixed finite product of positive natural pools is sublinear when every
factor logarithm is sublinear. -/
theorem sublinear_log_nat_prod {L : ℕ → ℕ} {J : Type*} [Fintype J]
    (Q : J → ℕ → ℕ) (hQ : ∀ j m, 1 ≤ Q j m)
    (hsub : ∀ j, Sublinear L (fun m => Real.log (Q j m : ℝ))) :
    Sublinear L (fun m => Real.log ((∏ j, Q j m : ℕ) : ℝ)) := by
  have hs := sublinear_finset_sum (Finset.univ : Finset J)
    (fun j m => Real.log (Q j m : ℝ)) (fun j _ => hsub j)
  simpa only [log_nat_prod_eq_sum Q hQ] using hs

/-- Pool accounting for a global pool multiplied by finitely many positive stage pools. -/
theorem sublinear_log_global_mul_stageProduct {L : ℕ → ℕ}
    {J : Type*} [Fintype J] (Qg : ℕ → ℕ) (Qs : J → ℕ → ℕ)
    (hgpos : ∀ m, 1 ≤ Qg m) (hspos : ∀ j m, 1 ≤ Qs j m)
    (hg : Sublinear L (fun m => Real.log (Qg m : ℝ)))
    (hs : ∀ j, Sublinear L (fun m => Real.log (Qs j m : ℝ))) :
    Sublinear L (fun m => Real.log ((Qg m * ∏ j, Qs j m : ℕ) : ℝ)) := by
  have hp := sublinear_log_nat_prod Qs hspos hs
  have hadd := sublinear_add hg hp
  have heq : (fun m => Real.log ((Qg m * ∏ j, Qs j m : ℕ) : ℝ)) =
      (fun m => Real.log (Qg m : ℝ) + Real.log ((∏ j, Qs j m : ℕ) : ℝ)) := by
    funext m
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hgpos m))
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mp
        (Finset.one_le_prod' (fun j _ => hspos j m)))
  rw [heq]
  exact hadd

end OmegaBound.ADVXXZGeneral
end
