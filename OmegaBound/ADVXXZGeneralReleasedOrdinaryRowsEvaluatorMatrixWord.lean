import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixStage2

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6SplitTargetData (TargetNode wordId wordOfId wordEquiv targetDen)

/-! ## The width-two word rate

By the disintegration in `ADVXXZT6Round82` the released child law of a level-three address is the
`TargetNode.raw` row of that address's target node: nine natural numerators over the single
released denominator `ordinaryD`.  Everything the `Q3` matrix census needs about that law is
the symbolic quantity `ordinaryWordRate32`. -/

/-- The number of level-one digits equal to `1` in the width-two word coded by `i`. -/
def ordinaryOneCount32 : Fin 9 → ℕ := ![0, 1, 0, 1, 2, 1, 0, 1, 0]

/-- The inventory rate carried by one width-two atom whose law has numerators `nums` over
the released denominator. -/
noncomputable def ordinaryWordRate32 (nums : Fin 9 → ℕ) : ℝ :=
  (-∑ i : Fin 9, ((nums i : ℝ) / (ordinaryD : ℝ)) *
      Real.log ((nums i : ℝ) / (ordinaryD : ℝ))) +
    Real.log 5 * ∑ i : Fin 9, ((nums i : ℝ) / (ordinaryD : ℝ)) *
      (ordinaryOneCount32 i : ℝ)

theorem sum_fin9_32 (f : Fin 9 → ℝ) :
    ∑ i : Fin 9, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_succ]
  ring

theorem chunk2_reindex32 {M : Type*} [AddCommMonoid M] (f : Chunk 2 → M) :
    ∑ σ : Chunk 2, f σ = ∑ i : Fin 9, f (wordOfId i) :=
  (Equiv.sum_comp wordEquiv.symm f).symm

theorem wordId_wordOfId32 (i : Fin 9) : wordId (wordOfId i) = i :=
  wordEquiv.right_inv i

theorem one_count_card32 (i : Fin 9) :
    ((Finset.univ.filter (fun p : Fin 2 => ((wordOfId i) p).val = 1)).card : ℕ) =
      ordinaryOneCount32 i := by
  revert i
  decide +kernel

theorem ordinaryD_even32 : 2 * (ordinaryD / 2) = ordinaryD := by decide +kernel

/-- Half the released denominator, as an explicit literal.  Stating the two-atom profile
with `ordinaryD / 2` instead makes the kernel unfold `Nat.div` under the released target
matcher and abort with `deep recursion detected`. -/
def ordinaryHalf32 : ℕ := 58028439341502200385896448

theorem ordinaryHalf32_even : 2 * ordinaryHalf32 = ordinaryD := by decide +kernel

theorem ordinaryD_pos32 : 0 < ordinaryD := by decide +kernel

theorem ordinaryDR_ne32 : (ordinaryD : ℝ) ≠ 0 := by
  have h : ordinaryD ≠ 0 := by decide +kernel
  exact_mod_cast h

private theorem oc0 : ordinaryOneCount32 0 = 0 := rfl
private theorem oc1 : ordinaryOneCount32 1 = 1 := rfl
private theorem oc2 : ordinaryOneCount32 2 = 0 := rfl
private theorem oc3 : ordinaryOneCount32 3 = 1 := rfl
private theorem oc4 : ordinaryOneCount32 4 = 2 := rfl
private theorem oc5 : ordinaryOneCount32 5 = 1 := rfl
private theorem oc6 : ordinaryOneCount32 6 = 0 := rfl
private theorem oc7 : ordinaryOneCount32 7 = 1 := rfl
private theorem oc8 : ordinaryOneCount32 8 = 0 := rfl

private theorem half_cast32 : ((ordinaryHalf32 : ℕ) : ℝ) / (ordinaryD : ℝ) = 1 / 2 := by
  have h : (2 : ℝ) * ((ordinaryHalf32 : ℕ) : ℝ) = (ordinaryD : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) ordinaryHalf32_even
  rw [div_eq_div_iff ordinaryDR_ne32 (by norm_num : (2:ℝ) ≠ 0)]
  linarith

private theorem zero_cast32 : ((0 : ℕ) : ℝ) / (ordinaryD : ℝ) = 0 := by
  norm_num

private theorem mu_sub_cast32 (mu : ℕ) (hmu : mu ≤ ordinaryD / 2) :
    ((ordinaryD - 2 * mu : ℕ) : ℝ) / (ordinaryD : ℝ) =
      1 - 2 * ((mu : ℝ) / (ordinaryD : ℝ)) := by
  have hle : 2 * mu ≤ ordinaryD := by omega
  have hcast : ((ordinaryD - 2 * mu : ℕ) : ℝ) = (ordinaryD : ℝ) - 2 * (mu : ℝ) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast, sub_div]
  rw [div_self ordinaryDR_ne32]
  ring

private theorem log_half32 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
  rw [one_div, Real.log_inv]

/-! ## The three boundary numerator profiles -/

/-- Support `{1,3}`: two equiprobable words, each with one level-one digit `1`. -/
theorem wordRate_13_32 (nums : Fin 9 → ℕ)
    (h0 : nums 0 = 0) (h1 : nums 1 = ordinaryHalf32) (h2 : nums 2 = 0)
    (h3 : nums 3 = ordinaryHalf32) (h4 : nums 4 = 0) (h5 : nums 5 = 0)
    (h6 : nums 6 = 0) (h7 : nums 7 = 0) (h8 : nums 8 = 0) :
    ordinaryWordRate32 nums = Real.log 2 + Real.log 5 := by
  unfold ordinaryWordRate32
  rw [sum_fin9_32, sum_fin9_32, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    half_cast32, zero_cast32, log_half32,
    oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7, oc8]
  push_cast
  ring

/-- Support `{5,7}`: two equiprobable words, each with one level-one digit `1`. -/
theorem wordRate_57_32 (nums : Fin 9 → ℕ)
    (h0 : nums 0 = 0) (h1 : nums 1 = 0) (h2 : nums 2 = 0)
    (h3 : nums 3 = 0) (h4 : nums 4 = 0) (h5 : nums 5 = ordinaryHalf32)
    (h6 : nums 6 = 0) (h7 : nums 7 = ordinaryHalf32) (h8 : nums 8 = 0) :
    ordinaryWordRate32 nums = Real.log 2 + Real.log 5 := by
  unfold ordinaryWordRate32
  rw [sum_fin9_32, sum_fin9_32, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    half_cast32, zero_cast32, log_half32,
    oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7, oc8]
  push_cast
  ring

/-- Support `{2,4,6}` with masses `mu, D - 2 mu, mu`: the paper's `H(mu,mu,1-2mu)` law,
whose middle word carries two level-one digits `1`. -/
theorem wordRate_mu_32 (nums : Fin 9 → ℕ) (mu : ℕ) (hmu : mu ≤ ordinaryD / 2)
    (h0 : nums 0 = 0) (h1 : nums 1 = 0) (h2 : nums 2 = mu)
    (h3 : nums 3 = 0) (h4 : nums 4 = ordinaryD - 2 * mu) (h5 : nums 5 = 0)
    (h6 : nums 6 = mu) (h7 : nums 7 = 0) (h8 : nums 8 = 0) :
    ordinaryWordRate32 nums =
      OmegaBound.ADVXXZLevel2Closure.entropyMu ((mu : ℝ) / (ordinaryD : ℝ)) +
        2 * (1 - 2 * ((mu : ℝ) / (ordinaryD : ℝ))) * Real.log 5 := by
  unfold ordinaryWordRate32 OmegaBound.ADVXXZLevel2Closure.entropyMu
  rw [sum_fin9_32, sum_fin9_32, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    mu_sub_cast32 mu hmu, zero_cast32,
    oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7, oc8]
  simp only [Real.negMulLog]
  push_cast
  ring

end OmegaBound.ADVXXZGeneral
end
