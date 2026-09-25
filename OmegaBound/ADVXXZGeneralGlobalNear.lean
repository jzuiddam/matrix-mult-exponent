import OmegaBound.ADVXXZGeneralGlobalNearContinuity
import OmegaBound.ADVXXZGeneralGlobalExactConsumer37
import PLATFORM.Statements.«V17_G_Near.1»

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

/-- Frozen statement `V17_G_Near.1`: the uniform exact-grid producer weakened by the
    uniform entropy-continuity debit for every plain full grid. -/
theorem global_nearby_uniform : S_V17_G_Near_1 := by
  intro w b q hq hw g hg hb
  obtain ⟨ell₀, hell₀, hsub₀, M₀, hexact⟩ :=
    global_exact_uniform q hq hw g hg hb
  obtain ⟨delta, hdelta, hrate⟩ := gridRate_ge_gRate_sub_delta g hg hb
  let V : (ε : ℚ) → (m : ℕ) → FullGrid g (b * m) ε → ℕ := fun _ m xi =>
    if hm : M₀ ≤ m then Classical.choose (hexact m hm xi.val) else 0
  let ell : ℚ → ℕ → ℝ := fun _ m => ell₀ m
  refine ⟨V, delta, ell, hdelta, ?_, ?_⟩
  · constructor
    · intro ε m
      exact hell₀ m
    · intro ε hε
      exact hsub₀
  · intro ε hε
    refine ⟨M₀, ?_⟩
    intro m hm xi
    have hwitness := Classical.choose_spec (hexact m hm xi.val)
    obtain ⟨N, hcopy, hdeg⟩ := hwitness
    have hV : V ε m xi = Classical.choose (hexact m hm xi.val) := by
      simp only [V, dif_pos hm]
    have hexponent :
        (gRate g - delta ε) * (b * m : ℝ) - ell ε m ≤
          gridRate g (b * m) xi.val * (b * m : ℝ) - ell₀ m := by
      dsimp only [ell]
      have hscale : 0 ≤ (b : ℝ) * (m : ℝ) :=
        mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg m)
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_right (hrate ε hε m xi) hscale) (ell₀ m)
    constructor
    · rw [hV]
      exact (Real.exp_le_exp.mpr hexponent).trans hcopy
    · refine ⟨N, ?_⟩
      rw [hV]
      exact hdeg

example : S_V17_G_Near_1 := global_nearby_uniform

end
end OmegaBound.ADVXXZGeneral
end
