import OmegaBound.ADVXXZGeneralAmend29CExact
import OmegaBound.ADVXXZGeneralInputDensityBridge

set_option autoImplicit false

/-!
# Grid-uniform input concentration: the arithmetic of the empirical grid spec

Facts about `constituentGridSpec27` used by `constituent_grid_input_concentration29`:
mixtures and products of rational distributions, `constituentGridSpec27_pair_mixture` (the grid
regional law is the alpha mixture of the grid child laws), the grid output index
`constituentOutN_grid_index`, and positivity of the grid child law. The exact per-cell chunk
counts (`gridStageCounts_cast`) are in `ADVXXZGeneralGridInput29Counts`.
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

/-! ## Mixtures and products of rational distributions -/

theorem mixtureDist27_prob {A B : Type} [Fintype A] [Fintype B]
    (weights : RatDist A) (P : A → RatDist B) (x : B) :
    (mixtureDist27 weights P).prob x = ∑ a, weights.prob a * (P a).prob x := by
  have hden : ∀ a : A, ((P a).den : ℚ) ≠ 0 := fun a => (P a).den_ne_zero
  have hwden : (weights.den : ℚ) ≠ 0 := weights.den_ne_zero
  have hnum : (mixtureDist27 weights P).num x =
      ∑ a, weights.num a * (P a).num x * ∏ a' ∈ Finset.univ.erase a, (P a').den := rfl
  have hd : (mixtureDist27 weights P).den = weights.den * ∏ a, (P a).den := rfl
  rw [RatDist.prob, hnum, hd]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro a _
  have hprod : (∏ a', ((P a').den : ℚ)) =
      ((P a).den : ℚ) * ∏ a' ∈ Finset.univ.erase a, ((P a').den : ℚ) :=
    (Finset.mul_prod_erase Finset.univ (fun a => ((P a).den : ℚ)) (Finset.mem_univ a)).symm
  have hQ : (∏ a' ∈ Finset.univ.erase a, ((P a').den : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a' _ => hden a')
  rw [hprod, RatDist.prob, RatDist.prob]
  field_simp

theorem leftHalf_joinChunk27 {w : ℕ} (x y : Chunk w) :
    leftHalf (joinChunk27 x y) = x := by
  funext a
  show joinChunk27 x y ⟨(a : ℕ), _⟩ = x a
  unfold joinChunk27
  rw [dif_pos a.isLt]

theorem rightHalf_joinChunk27 {w : ℕ} (x y : Chunk w) :
    rightHalf (joinChunk27 x y) = y := by
  funext a
  show joinChunk27 x y ⟨w + (a : ℕ), _⟩ = y a
  unfold joinChunk27
  rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right w (a : ℕ)))]
  exact congrArg y (Fin.ext (by simp))

theorem joinChunk27_halves {w : ℕ} (σ : Chunk (w + w)) :
    joinChunk27 (leftHalf σ) (rightHalf σ) = σ := by
  funext i
  unfold joinChunk27
  by_cases hi : (i : ℕ) < w
  · rw [dif_pos hi]
    exact congrArg σ (Fin.ext rfl)
  · rw [dif_neg hi]
    exact congrArg σ (Fin.ext (by simp; omega))

theorem productSplit27_prob {w : ℕ} (x y : SplitDist w) (σ : Chunk (w + w)) :
    (productSplit27 x y).prob σ = x.prob (leftHalf σ) * y.prob (rightHalf σ) := by
  have hfilter :
      (Finset.univ.filter fun a : Chunk w × Chunk w => joinChunk27 a.1 a.2 = σ) =
        {(leftHalf σ, rightHalf σ)} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      have h1 : a.1 = leftHalf σ := by rw [← hj, leftHalf_joinChunk27]
      have h2 : a.2 = rightHalf σ := by rw [← hj, rightHalf_joinChunk27]
      exact Prod.ext h1 h2
    · rintro rfl
      exact joinChunk27_halves σ
  have hnum : (productSplit27 x y).num σ =
      ∑ a ∈ Finset.univ.filter fun a : Chunk w × Chunk w => joinChunk27 a.1 a.2 = σ,
        x.num a.1 * y.num a.2 := rfl
  have hd : (productSplit27 x y).den = x.den * y.den := rfl
  rw [RatDist.prob, hnum, hd, hfilter, Finset.sum_singleton, RatDist.prob, RatDist.prob]
  push_cast
  ring

/-! ## The grid regional law is the alpha mixture of the grid child laws -/

/-- `constituentGridRegionBeta27` is the
`alpha`-mixture of `constituentGridBeta27`, i.e. the grid spec satisfies the
`pair_mixture` clause of `ConstituentAdmissibleAt`. -/
theorem constituentGridSpec27_pair_mixture {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (W : Side) (t : Fin s) (r : Fin 6)
    (σ : Chunk (w + w)) :
    (constituentGridRegionBeta27 d m h W t r).prob σ =
      ∑ u, (d.alpha t r).prob u *
        (constituentGridBeta27 d m h W t r u).prob (leftHalf σ) *
        (constituentGridBeta27 d m h W t r (complement p t u)).prob (rightHalf σ) := by
  rw [constituentGridRegionBeta27, mixtureDist27_prob]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [productSplit27_prob, mul_assoc]

/-! ## The grid child law and the exact per-cell chunk counts -/

theorem constituentOutN_grid_index {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (t : Fin s) (r : Fin 6) (u : ChildShape p t) :
    constituentOutN d.toPaper m (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) =
      d.outBase ⟨t, r, u⟩ * m := by
  unfold constituentOutN constituentIndex
  rw [(Fintype.equivFin (ConstituentTerm p)).symm_apply_apply]
  rfl

theorem constituentGridBeta27_prob_pos {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin s) (r : Fin 6) (u : ChildShape p t) (σ : Chunk w)
    (hn : 0 < constituentOutN d.toPaper m
      (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩)) :
    (constituentGridBeta27 d m h W t r u).prob σ =
      (((h.val (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) W σ).val : ℕ) : ℚ) /
        ((constituentOutN d.toPaper m
          (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) : ℕ) : ℚ) := by
  unfold constituentGridBeta27
  dsimp only
  rw [dif_pos hn]
  rfl

end
end OmegaBound.ADVXXZGeneral
end
