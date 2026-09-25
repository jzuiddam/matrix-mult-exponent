import OmegaBound.ADVXXZGeneralGlobalExactAssembly37
import OmegaBound.ADVXXZGeneralGlobalExactFallback37
import OmegaBound.ADVXXZGeneralGlobalExactBudget37
import OmegaBound.ADVXXZGeneralGlobalExactUniformOutput
import PLATFORM.Statements.«V17_G_Exact.1»
import PLATFORM.Statements.«V17_G_Exact.2»

set_option autoImplicit false

/-!
# The global exact stage

The consumer pays the one regional loss six times, uses one copy on zero regions, multiplies
the six occupied-region copy bounds, and then applies the unrestricted-top regional assembly
`globalRegionalTop_exactGrid37`.  It proves the frozen statements `V17_G_Exact.1`
(`global_exact_uniform`) and `V17_G_Exact.2` (`global_exact`).
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem sublinear_six37 {b : ℕ} {ell : ℕ → ℝ}
    (h : Sublinear (fun m => b*m) ell) :
    Sublinear (fun m => b*m) (fun m => 6*ell m) := by
  intro delta hd
  obtain ⟨L, hL⟩ := h (delta/6) (div_pos hd (by norm_num))
  refine ⟨L, fun m hm => ?_⟩
  calc
    |6*ell m| = 6*|ell m| := by rw [abs_mul]; norm_num
    _ ≤ 6*(delta/6*((b*m:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (hL m hm) (by norm_num)
    _ = delta*((b*m:ℕ):ℝ) := by ring

private theorem rate_sum37 {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (m : ℕ) (xi : ExactGrid g (b*m)) (e : ℝ) :
    gridRate g (b*m) xi*(b*m:ℝ)-6*e =
      ∑ r, (((globalPopulation g (b*m) xi r).n:ℝ)*Real.log 2*
        globalRegionRate (globalExactGridData27 g xi) r-e) := by
  rw [gridRate_eq_globalExactGridData27, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  simp_rw [globalPopulation_n_cast27 g hg hb xi]
  push_cast
  calc
    Real.log 2*(∑ r, g.A.probR r*globalRegionRate (globalExactGridData27 g xi) r)*
        ((b:ℝ)*m) = ∑ r, Real.log 2*
          (g.A.probR r*globalRegionRate (globalExactGridData27 g xi) r)*((b:ℝ)*m) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := Finset.sum_congr rfl (fun r _ => by ring)

/-- The consumer, parameterized by the two contracts
`GlobalExactEnvelope37.globalRegionCopies_fallback37` and
`GlobalExactEnvelope37.globalRepairBudget_uniform37`. -/
theorem uniform_from_fallback_budget37
    (hfinite : GlobalExactEnvelope37.globalRegionCopies_fallback37)
    (hbudget : GlobalExactEnvelope37.globalRepairBudget_uniform37) : S_V17_G_Exact_1 := by
  intro w b q hq hw g hg hb
  obtain ⟨ell, hell, hsub, L, hbudget⟩ := hbudget g hg hw hb
  apply global_exact_uniform_output_of_compatible q g (fun m => 6*ell m)
    (fun m => mul_nonneg (by norm_num) (hell m)) (sublinear_six37 hsub) (max L 1)
  intro m hm xi hxi
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right L 1).trans hm)
  obtain ⟨k, B, hvalid, hD, hB, hQ⟩ :=
    hbudget m ((le_max_left L 1).trans hm) hm0 xi hxi
  let j : (r : Fin 6) → GlobalTargetLabel27 g xi r :=
    fun r => Classical.choice (globalTargetLabel_nonempty27 g xi r)
  have hreg : ∀ r, ∃ V : ℕ, 0 < V ∧
      Real.exp (((globalPopulation g (b*m) xi r).n:ℝ)*Real.log 2*
        globalRegionRate (globalExactGridData27 g xi) r-ell m) ≤ (V:ℝ) ∧
      Restricts (copiesZ V (globalExactITensor27 q g xi r (j r).val)).tensor
        (topZ q w (globalPopulation g (b*m) xi r).n).tensor := by
    intro r
    by_cases hn : (globalPopulation g (b*m) xi r).n = 0
    · refine ⟨1, Nat.zero_lt_one, ?_, globalExactRegion_direct37 q g xi r (j r).val⟩
      simp only [hn, Nat.cast_zero, zero_mul, zero_sub, Nat.cast_one]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hell m))
    · letI : NeZero (2*k r+1) := ⟨by omega⟩
      let b0 : GlobalBucketLabel27 (B r) := ⟨(hB r).choose, (hB r).choose_spec⟩
      obtain ⟨V, hV, hbound, hres⟩ := hfinite q g hg hw hb 0 m hm0 xi hxi r
        (B r) (hvalid r).1 (hvalid r).2.1 (hvalid r).2.2.1
        (hvalid r).2.2.2 (hD r) (j r) b0 hn
      exact ⟨V, hV, (hQ r hn (j r)).trans hbound, hres⟩
  choose V hV hrate hres using hreg
  refine ⟨∏ r, V r, 0, ?_, globalRegionalTop_exactGrid37 q m g hg hb xi j V hres⟩
  rw [rate_sum37 g hg hb m xi, Real.exp_sum]
  push_cast
  exact Finset.prod_le_prod (fun r _ => (Real.exp_pos _).le) (fun r _ => hrate r)

/-- Frozen statement `V17_G_Exact.1`. -/
theorem global_exact_uniform : S_V17_G_Exact_1 :=
  uniform_from_fallback_budget37 globalRegionCopies_fallback37 globalRepairBudget_uniform37

example : S_V17_G_Exact_1 := global_exact_uniform

/-- Frozen statement `V17_G_Exact.2`, through `global_exact_of_uniform`. -/
theorem global_exact : S_V17_G_Exact_2 := by
  intro q w b hq hw g hg hb
  exact global_exact_of_uniform q w b hq hw g hg hb
    (global_exact_uniform q hq hw g hg hb)

example : S_V17_G_Exact_2 := global_exact

end
end OmegaBound.ADVXXZGeneral
end
