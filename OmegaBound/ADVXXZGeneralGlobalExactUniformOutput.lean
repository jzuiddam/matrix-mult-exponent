import OmegaBound.ADVXXZGeneralGlobalExact

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

/-- A tensor which is identically zero is a degree-zero polynomial degeneration target. -/
theorem polyDegeneratesAt_zero_target
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (T : Tensor3 R X Y Z) (U : Tensor3 R X' Y' Z') (hU : U = 0) :
    PolyDegeneratesAt R 0 T U := by
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0), ?_, ?_⟩
  · intro _x _y _z k hk
    omega
  · intro x y z
    rw [hU]
    simp

/-- Copying an identically zero integral tensor remains identically zero. -/
theorem copiesZ_tensor_eq_zero (V : ℕ) (T : ITensor) (hT : T.tensor = 0) :
    (copiesZ V T).tensor = 0 := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  unfold copiesZ
  dsimp only [ITensor.tensor]
  unfold famDS
  rw [hT]
  simp

/-- The boundary-incompatible branch of the uniform exact-grid producer. -/
theorem global_exact_zero_grid {w b : ℕ} (q : ℕ) (g : GlobalSpec w)
    (m : ℕ) (xi : ExactGrid g (b*m)) (hxi : ¬ GridBoundaryCompatible xi)
    (ell : ℕ → ℝ) :
    ∃ V N : ℕ,
      Real.exp (gridRate g (b*m) xi*(b*m:ℝ)-ell m) ≤ (V:ℝ) ∧
      PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
        (copiesZ V (exactGridTensor q g (b*m) xi)).tensor := by
  let a := Real.exp (gridRate g (b*m) xi*(b*m:ℝ)-ell m)
  let V := Nat.ceil a
  refine ⟨V, 0, ?_, ?_⟩
  · exact Nat.le_ceil a
  · apply polyDegeneratesAt_zero_target
    exact copiesZ_tensor_eq_zero V (exactGridTensor q g (b*m) xi)
      (exactGridTensor_eq_zero_of_not_boundaryCompatible g xi hxi)

/--
Once the compatible-grid producer is uniform before `xi`, the already-proved zero dispatch gives
the full finite conclusion of `global_exact_uniform` without changing its quantifier order.
-/
theorem global_exact_uniform_output_of_compatible {w b : ℕ} (q : ℕ)
    (g : GlobalSpec w) (ell : ℕ → ℝ)
    (hell : ∀ m, 0 ≤ ell m) (hsub : Sublinear (fun m => b*m) ell)
    (M : ℕ)
    (hcompatible : ∀ m, M ≤ m → ∀ xi : ExactGrid g (b*m),
      GridBoundaryCompatible xi →
      ∃ V N : ℕ,
        Real.exp (gridRate g (b*m) xi*(b*m:ℝ)-ell m) ≤ (V:ℝ) ∧
        PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
          (copiesZ V (exactGridTensor q g (b*m) xi)).tensor) :
    ∃ ell : ℕ → ℝ, (∀ m, 0 ≤ ell m) ∧
      Sublinear (fun m => b*m) ell ∧
      ∃ M : ℕ, ∀ m, M ≤ m → ∀ xi : ExactGrid g (b*m),
        ∃ V N : ℕ,
          Real.exp (gridRate g (b*m) xi*(b*m:ℝ)-ell m) ≤ (V:ℝ) ∧
          PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
            (copiesZ V (exactGridTensor q g (b*m) xi)).tensor := by
  refine ⟨ell, hell, hsub, M, ?_⟩
  intro m hm xi
  by_cases hxi : GridBoundaryCompatible xi
  · exact hcompatible m hm xi hxi
  · exact global_exact_zero_grid q g m xi hxi ell

end
end OmegaBound.ADVXXZGeneral
end
