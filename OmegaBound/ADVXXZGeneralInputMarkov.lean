import OmegaBound.ADVXXZConstituentPairing
import OmegaBound.ADVXXZGeneralInputSelfBound
import OmegaBound.ADVXXZGeneralRepairFibresApplication

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem input_avg_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

private noncomputable def inputPiDeleteEquiv {I : Type*} [DecidableEq I]
    (A : I → Type*) (c : I) :
    ((i : I) → A i) ≃ A c × ((i : {i : I // i ≠ c}) → A i.val) where
  toFun x := (x c, fun i => x i.val)
  invFun x i := if h : i = c then cast (congrArg A h).symm x.1 else x.2 ⟨i,h⟩
  left_inv x := by
    funext i
    by_cases h : i = c
    · subst i
      simp
    · simp [h]
  right_inv x := by
    apply Prod.ext
    · simp
    · funext i
      simp [i.property]

private theorem input_avg_prod {A B : Type*} [Fintype A] [Fintype B]
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B) (f : A → B → ℝ) :
    avg (fun z : A × B => f z.1 z.2) = avg (fun x : A => avg (f x)) := by
  have hAr : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBr : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Nat.cast_mul, Finset.sum_div]
  field_simp

private theorem input_avg_const {A : Type*} [Fintype A]
    (hA : 0 < Fintype.card A) (c : ℝ) : avg (fun _ : A => c) = c := by
  have hAr : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  unfold avg
  simp [hAr]

/-- A coordinate of a uniformly sampled nonempty finite dependent product is
uniform on that coordinate. -/
theorem avg_pi_apply {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] (hA : ∀ i, Nonempty (A i))
    (c : I) (f : A c → ℝ) :
    avg (fun x : (i : I) → A i => f (x c)) = avg f := by
  let R := (i : {i : I // i ≠ c}) → A i.val
  let e := inputPiDeleteEquiv A c
  have hc : 0 < Fintype.card (A c) := Fintype.card_pos_iff.mpr (hA c)
  have hR : 0 < Fintype.card R := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun i => Classical.choice (hA i.val)⟩
  calc
    avg (fun x : (i : I) → A i => f (x c)) =
        avg (fun z : A c × R => f z.1) := by
      simpa [e, inputPiDeleteEquiv] using
        (input_avg_equiv e (fun z : A c × R => f z.1))
    _ = avg (fun x : A c => avg (fun _ : R => f x)) :=
      input_avg_prod hc hR (fun x _ => f x)
    _ = avg f := by
      apply congrArg avg
      funext x
      exact input_avg_const hR (f x)

/-- Two distinct coordinates of a uniformly sampled nonempty finite dependent
product are uniformly distributed as their product. -/
theorem avg_pi_apply₂ {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] (hA : ∀ i, Nonempty (A i))
    (c d : I) (hcd : c ≠ d) (f : A c → A d → ℝ) :
    avg (fun x : (i : I) → A i => f (x c) (x d)) =
      avg (fun z : A c × A d => f z.1 z.2) := by
  let R := (i : {i : I // i ≠ c}) → A i.val
  let dc : {i : I // i ≠ c} := ⟨d, Ne.symm hcd⟩
  let e := inputPiDeleteEquiv A c
  have hc : 0 < Fintype.card (A c) := Fintype.card_pos_iff.mpr (hA c)
  have hR : 0 < Fintype.card R := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun i => Classical.choice (hA i.val)⟩
  have hinner : ∀ x : A c, avg (fun y : R => f x (y dc)) =
      avg (fun y : A d => f x y) := by
    intro x
    exact avg_pi_apply (fun i : {i : I // i ≠ c} => A i.val)
      (fun i => hA i.val) dc (f x)
  calc
    avg (fun x : (i : I) → A i => f (x c) (x d)) =
        avg (fun z : A c × R => f z.1 (z.2 dc)) := by
      simpa [e, dc, inputPiDeleteEquiv] using
        (input_avg_equiv e (fun z : A c × R => f z.1 (z.2 dc)))
    _ = avg (fun x : A c => avg (fun y : R => f x (y dc))) :=
      input_avg_prod hc hR (fun x y => f x (y dc))
    _ = avg (fun x : A c => avg (fun y : A d => f x y)) := by
      apply congrArg avg
      funext x
      exact hinner x
    _ = avg (fun z : A c × A d => f z.1 z.2) :=
      (input_avg_prod hc (Fintype.card_pos_iff.mpr (hA d)) f).symm

/-- Fourth-moment Markov in the exact finite-cardinality form used for a uniform
type-class fibre. -/
theorem uniformFourthMoment_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : 0 < Fintype.card Ω) (X : Ω → ℝ) (mu delta C : ℝ)
    (hdelta : 0 < delta)
    (hmoment : avg (fun x => (X x-mu)^4) ≤ C) :
    ((Finset.univ.filter fun x => delta ≤ |X x-mu|).card : ℝ) /
        Fintype.card Ω ≤ C/delta^4 := by
  let bad := Finset.univ.filter fun x => delta ≤ |X x-mu|
  have hpoint : ∀ x ∈ bad, delta^4 ≤ (X x-mu)^4 := by
    intro x hx
    have hdev := (Finset.mem_filter.mp hx).2
    calc
      delta^4 ≤ |X x-mu|^4 := pow_le_pow_left₀ hdelta.le hdev 4
      _ = (X x-mu)^4 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by positivity)
  have hnonneg : ∀ x : Ω, 0 ≤ (X x-mu)^4 := fun _ => by positivity
  have hsum : (bad.card : ℝ)*delta^4 ≤ ∑ x, (X x-mu)^4 := by
    calc
      (bad.card : ℝ)*delta^4 = ∑ _x ∈ bad, delta^4 := by simp [mul_comm]
      _ ≤ ∑ x ∈ bad, (X x-mu)^4 :=
        Finset.sum_le_sum fun x hx => hpoint x hx
      _ ≤ ∑ x, (X x-mu)^4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
          (fun x _ _ => hnonneg x)
  have hcard : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hsumC : (∑ x, (X x-mu)^4) ≤ C*Fintype.card Ω := by
    apply (div_le_iff₀ hcard).mp
    simpa only [avg] using hmoment
  have hbad : (bad.card : ℝ)*delta^4 ≤ C*Fintype.card Ω :=
    hsum.trans hsumC
  change (bad.card : ℝ) / Fintype.card Ω ≤ C/delta^4
  apply (div_le_iff₀ hcard).2
  rw [show C/delta^4 * (Fintype.card Ω : ℝ) =
    (C*Fintype.card Ω)/delta^4 by ring]
  exact (le_div_iff₀ (pow_pos hdelta 4)).2 (by simpa [mul_assoc] using hbad)

end OmegaBound.ADVXXZGeneral
end
