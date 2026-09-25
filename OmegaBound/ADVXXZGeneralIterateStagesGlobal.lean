import OmegaBound.ADVXXZGeneralGlobalPositiveGrid
import OmegaBound.ADVXXZGeneralIterateStagesTransport

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

private theorem gridMinimum27_le_value_iterate {iota : Type} [Fintype iota]
    (v : iota → ℕ) (i : iota) : gridMinimum27 v ≤ v i := by
  have hne : (Finset.univ : Finset iota).Nonempty := ⟨i, Finset.mem_univ i⟩
  simp only [gridMinimum27, dif_pos hne]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private theorem real_le_gridMinimum27_iterate {iota : Type} [Fintype iota]
    (v : iota → ℕ) (i₀ : iota) (a : ℝ) (h : ∀ i, a ≤ (v i : ℝ)) :
    a ≤ (gridMinimum27 v : ℝ) := by
  have hne : (Finset.univ : Finset iota).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
  have hmem : ((Finset.univ : Finset iota).image v).min' (hne.image v) ∈
      (Finset.univ : Finset iota).image v := Finset.min'_mem _ _
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  simp only [gridMinimum27, dif_pos hne]
  rw [← hi]
  exact h i

private theorem minimum_exactGridTensor_poly_iterate {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ} (v : FullGrid g n ε → ℕ)
    (ξ : FullGrid g n ε)
    (h : ∃ N, PolyDegeneratesAt ℤ N (topZ q w n).tensor
      (copiesZ (v ξ) (exactGridTensor q g n ξ.val)).tensor) :
    ∃ N, PolyDegeneratesAt ℤ N (topZ q w n).tensor
      (copiesZ (gridMinimum27 v) (exactGridTensor q g n ξ.val)).tensor := by
  obtain ⟨N, hN⟩ := h
  have hr : Restricts
      (copiesZ (gridMinimum27 v) (exactGridTensor q g n ξ.val)).tensor
      (copiesZ (v ξ) (exactGridTensor q g n ξ.val)).tensor := by
    simpa only [copiesZ] using OmegaBound.ADVXXZStage.famDS_copies_mono
      (R := ℤ) (gridMinimum27_le_value_iterate v ξ)
        (exactGridTensor q g n ξ.val).tensor
  exact integral_polyDegeneratesAt_trans hN
    (polyDegeneratesAt_of_restricts hr)

private theorem exists_polyDegeneratesAt_famDS_of_sum_iterate
    {I XI YI ZI XO YO ZO : Type} [Fintype I] [DecidableEq I]
    [Fintype XI] [Fintype YI] [Fintype ZI]
    [Fintype XO] [Fintype YO] [Fintype ZO]
    [DecidableEq XI] [DecidableEq YI] [DecidableEq ZI]
    [DecidableEq XO] [DecidableEq YO] [DecidableEq ZO]
    (Inp : Tensor3 ℤ XI YI ZI) (out : I → Tensor3 ℤ XO YO ZO)
    (Tε : Tensor3 ℤ XO YO ZO)
    (hsum : ∀ x y z, Tε x y z = ∑ i : I, out i x y z) (C : ℕ)
    (h : ∀ i, ∃ N, PolyDegeneratesAt ℤ N Inp
      (famDS (Finset.univ : Finset (Fin C)) (fun _ => out i))) :
    ∃ N, PolyDegeneratesAt ℤ N
      (famDS (Finset.univ : Finset I) (fun _ => Inp))
      (famDS (Finset.univ : Finset (Fin C)) (fun _ => Tε)) := by
  choose degree hdegree using h
  have hbig := polyDegeneratesAt_famDS_commonDegree degree
    (fun _ : I => Inp)
    (fun i => famDS (Finset.univ : Finset (Fin C)) (fun _ => out i)) hdegree
  have h₁ : famDS (Finset.univ : Finset (Fin C)) (fun _ => Tε) ≤ₜ
      famDS (Finset.univ : Finset (Fin C))
        (fun _ => famDS (Finset.univ : Finset I) out) := by
    refine OmegaBound.ADVXXZStage.famDS_const_mono
      (R := ℤ) (ι := Fin C) (X := I × XO) (Y := I × YO) (Z := I × ZO)
      (X' := XO) (Y' := YO) (Z' := ZO) _ ?_
    have hT : Tε = fun x y z => ∑ i ∈ (Finset.univ : Finset I), out i x y z := by
      funext x y z
      simpa using hsum x y z
    rw [hT]
    exact OmegaBound.ADVXXZStage.sum_restricts_famDS
      (R := ℤ) (ι := I) (X := XO) (Y := YO) (Z := ZO) _ out
  have hr := Tensor3.Restricts.trans h₁ (OmegaBound.ADVXXZStage.famDS_swap
    (R := ℤ) (ι := I) (κ := Fin C) (X := XO) (Y := YO) (Z := ZO) out)
  exact integral_polyDegeneratesAt_trans hbig (polyDegeneratesAt_of_restricts hr)

/-- Integral form of the positive-tolerance global producer, used by the recursion. -/
theorem global_positive_integral_for_iterate
    (q w b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) :
  ∃ (Q V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ Loss (fun m => b * m) ell ∧
    CopyBound (fun m => b * m) (gRate g) delta ell V ∧
    (∀ ε, 0 < ε → Sublinear (fun m => b * m)
      (fun m => Real.log (Q ε m : ℝ))) ∧
    ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
      1 ≤ Q ε m ∧ Q ε m ≤ (b * m + 1) ^ gridDimension g ∧
      ∃ N, PolyDegeneratesAt ℤ N
        (copiesZ (Q ε m) (topZ q w (b * m))).tensor
        (copiesZ (V ε m) (globalOutputZ q g (b * m) ε)).tensor := by
  obtain ⟨v, delta, ell, hdelta, hell, hnear⟩ :=
    global_nearby_uniform q hq hw g hg hb
  let Q : ℚ → ℕ → ℕ := fun ε m => fullGridPool27 g (b * m) ε
  let V : ℚ → ℕ → ℕ := fun ε m => gridMinimum27 (v ε m)
  refine ⟨Q, V, delta, ell, hdelta, hell, ?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨M, hM⟩ := hnear ε hε
    refine ⟨M, fun m hm => ?_⟩
    let ξ₀ : FullGrid g (b * m) ε := globalCentreFullGrid g hg hb m ε hε.le
    apply real_le_gridMinimum27_iterate (v ε m) ξ₀
    intro ξ
    simpa only [Nat.cast_mul] using (hM m hm ξ).1
  · intro ε hε
    exact fullGridPool27_log_sublinear g hg hb ε hε.le
  · intro ε hε
    obtain ⟨M, hM⟩ := hnear ε hε
    refine ⟨M, fun m hm => ?_⟩
    have hQpos : 0 < Q ε m := fullGridPool27_pos g hg hb m ε hε.le
    have hQle : Q ε m ≤ (b * m + 1) ^ gridDimension g :=
      fullGrid_card_le g (b * m) ε
    refine ⟨hQpos, hQle, ?_⟩
    let e : Fin (Q ε m) ≃ FullGrid g (b * m) ε :=
      (Fintype.equivFin (FullGrid g (b * m) ε)).symm
    have hsum : ∀ x y z, (globalOutputZ q g (b * m) ε).tensor x y z =
        ∑ i : Fin (Q ε m),
          (exactGridTensor q g (b * m) (e i).val).tensor x y z := by
      intro x y z
      have hd := globalOutputZ_eq_sum_exactGridTensor q (n := b * m) g ε
      have hdxyz := congrFun (congrFun (congrFun hd x) y) z
      have happ :
          ((∑ ξ : FullGrid g (b * m) ε,
              (exactGridTensor q g (b * m) ξ.val).tensor) :
            Tensor3 ℤ (globalOutputZ q g (b * m) ε).X
              (globalOutputZ q g (b * m) ε).Y
              (globalOutputZ q g (b * m) ε).Z) x y z =
            ∑ ξ : FullGrid g (b * m) ε,
              (exactGridTensor q g (b * m) ξ.val).tensor x y z := by
        let f : FullGrid g (b * m) ε →
            Tensor3 ℤ (globalOutputZ q g (b * m) ε).X
              (globalOutputZ q g (b * m) ε).Y
              (globalOutputZ q g (b * m) ε).Z :=
          fun ξ => (exactGridTensor q g (b * m) ξ.val).tensor
        change (∑ ξ, f ξ) x y z = ∑ ξ, f ξ x y z
        rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]
      calc
        _ = ((∑ ξ : FullGrid g (b * m) ε,
            (exactGridTensor q g (b * m) ξ.val).tensor) :
              Tensor3 ℤ (globalOutputZ q g (b * m) ε).X
                (globalOutputZ q g (b * m) ε).Y
                (globalOutputZ q g (b * m) ε).Z) x y z := hdxyz
        _ = ∑ ξ : FullGrid g (b * m) ε,
            (exactGridTensor q g (b * m) ξ.val).tensor x y z := happ
        _ = _ := (Equiv.sum_comp e
          (fun ξ => (exactGridTensor q g (b * m) ξ.val).tensor x y z)).symm
    have heach : ∀ i : Fin (Q ε m), ∃ N, PolyDegeneratesAt ℤ N
        (topZ q w (b * m)).tensor
        (copiesZ (V ε m)
          (exactGridTensor q g (b * m) (e i).val)).tensor := by
      intro i
      exact minimum_exactGridTensor_poly_iterate (v ε m) (e i) (hM m hm (e i)).2
    have hall := exists_polyDegeneratesAt_famDS_of_sum_iterate
      (topZ q w (b * m)).tensor
      (fun i : Fin (Q ε m) => (exactGridTensor q g (b * m) (e i).val).tensor)
      (globalOutputZ q g (b * m) ε).tensor hsum (V ε m) heach
    simpa only [copiesZ] using hall

end
end OmegaBound.ADVXXZGeneral
end
