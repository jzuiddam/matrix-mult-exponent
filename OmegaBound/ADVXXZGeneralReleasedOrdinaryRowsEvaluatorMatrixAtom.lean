import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixWord

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6SplitTargetData (TargetNode wordId wordOfId wordEquiv targetDen)
open OmegaBound.ADVXXZT6Round82 (sideIndex)

/-- The directional activity predicate of the ordinary inventory rate, at any width. -/
def OrdinaryActiveAt {w : ℕ} (W : Side) (v : Shape w) : Prop :=
  match W with
  | .X => coord .Y v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Z v
  | .Y => coord .Z v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Y v
  | .Z => coord .X v = 0 ∧ 0 < coord .Y v ∧ 0 < coord .Z v

instance instDecidableOrdinaryActiveAt {w : ℕ} (W : Side) (v : Shape w) :
    Decidable (OrdinaryActiveAt W v) := by
  unfold OrdinaryActiveAt
  cases W <;> infer_instance

/-- The side whose child law the ordinary inventory rate reads for direction `W`. -/
def ordinaryAtomSide32 : Side → Side
  | .X => .X
  | .Y => .X
  | .Z => .Y

private theorem cast5_32 : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num

/-- The two analytic pieces of one width-two atom, read off the nine numerators. -/
theorem wordRate_from_chunk32 (g : Fin 9 → ℕ) :
    entropyNats (fun σ : Chunk 2 => (((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ)) +
      Real.log ((5 : ℕ) : ℝ) * ∑ σ : Chunk 2,
        (((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ) *
          ((Finset.univ.filter (fun i : Fin 2 => (σ i).val = 1)).card : ℝ)
      = ordinaryWordRate32 g := by
  have hc : ∀ σ : Chunk 2, (((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ)
      = (g (wordId σ) : ℝ) / (ordinaryD : ℝ) := by
    intro σ
    push_cast
    ring
  unfold entropyNats ordinaryWordRate32
  rw [cast5_32,
    chunk2_reindex32 (fun σ : Chunk 2 =>
      (((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ) *
        Real.log ((((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ))),
    chunk2_reindex32 (fun σ : Chunk 2 =>
      (((g (wordId σ) : ℚ) / (ordinaryD : ℚ) : ℚ) : ℝ) *
        ((Finset.univ.filter (fun i : Fin 2 => (σ i).val = 1)).card : ℝ))]
  refine congrArg₂ (· + ·) (congrArg Neg.neg ?_) (congrArg (Real.log 5 * ·) ?_)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc, wordId_wordOfId32]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc, wordId_wordOfId32, one_count_card32]

/-- The ordinary inventory rate of a width-two atom whose law is given by nine numerators
over the released denominator. -/
theorem ordinaryAtomRate_wordRate32 (W : Side) (fr : ℚ) (v : Shape 2)
    (nums : Side → Fin 9 → ℕ) :
    ordinaryAtomRate 5 W (fr, (⟨2, v, fun V σ =>
        ((nums V (wordId σ) : ℚ) / (ordinaryD : ℚ))⟩ : AtomKey)) =
      if OrdinaryActiveAt W v then
        (fr : ℝ) * ordinaryWordRate32 (nums (ordinaryAtomSide32 W)) else 0 := by
  simp only [ordinaryAtomRate, OrdinaryActiveAt, ordinaryAtomSide32]
  cases W
  · by_cases h : coord .Y v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Z v
    · rw [if_pos h, if_pos h, wordRate_from_chunk32 (nums .X)]
    · rw [if_neg h, if_neg h]
  · by_cases h : coord .Z v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Y v
    · rw [if_pos h, if_pos h, wordRate_from_chunk32 (nums .X)]
    · rw [if_neg h, if_neg h]
  · by_cases h : coord .X v = 0 ∧ 0 < coord .Y v ∧ 0 < coord .Z v
    · rw [if_pos h, if_pos h, wordRate_from_chunk32 (nums .Y)]
    · rw [if_neg h, if_neg h]

end OmegaBound.ADVXXZGeneral
end
