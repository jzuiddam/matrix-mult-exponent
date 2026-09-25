import OmegaBound.ADVXXZGeneralMap
import OmegaBound.Rectangular

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem identity_poly_sum {F : Type*} [Field F] {r : ℕ}
    (f g h : Fin r → Polynomial F) :
    (∑ a : Fin r, ∑ b : Fin r, ∑ c : Fin r,
      f a * g b * h c * Polynomial.C (Tensor3.identity F r a b c)) =
      ∑ ℓ : Fin r, f ℓ * g ℓ * h ℓ := by
  simp only [Tensor3.identity]
  simp only [apply_ite Polynomial.C, map_one, map_zero, mul_ite, mul_one, mul_zero]
  simp only [ite_and]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem coeff_mul_three_square {F : Type*} [Field F]
    (p q s : Polynomial F) (N : ℕ) :
    (p * q * s).coeff N =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        p.coeff b *
          (if b.1 ≤ a.1 then q.coeff (a.1 - b.1) else 0) *
          s.coeff (N - a.1) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsub : Finset.range (a.1 + 1) ⊆ Finset.range (N + 1) := by
    intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  have hpad :
      (∑ b ∈ Finset.range (a.1 + 1), p.coeff b * q.coeff (a.1 - b)) =
        ∑ b : Fin (N + 1),
          if b.1 ≤ a.1 then p.coeff b * q.coeff (a.1 - b.1) else 0 := by
    calc
      (∑ b ∈ Finset.range (a.1 + 1), p.coeff b * q.coeff (a.1 - b)) =
          ∑ b ∈ Finset.range (a.1 + 1),
            if b ≤ a.1 then p.coeff b * q.coeff (a.1 - b) else 0 := by
              apply Finset.sum_congr rfl
              intro b hb
              simp only [Finset.mem_range] at hb
              rw [if_pos (by omega)]
      _ = ∑ b ∈ Finset.range (N + 1),
            if b ≤ a.1 then p.coeff b * q.coeff (a.1 - b) else 0 := by
              apply Finset.sum_subset hsub
              intro b _ hb
              rw [if_neg]
              simp only [Finset.mem_range] at hb
              omega
      _ = ∑ b : Fin (N + 1),
            if b.1 ≤ a.1 then p.coeff b * q.coeff (a.1 - b.1) else 0 := by
              simpa using (Fin.sum_univ_eq_sum_range
                (fun b : ℕ =>
                  if b ≤ a.1 then p.coeff b * q.coeff (a.1 - b) else 0)
                (N + 1)).symm
  rw [hpad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hba : b.1 ≤ a.1
  · simp only [hba, if_true]
  · simp only [hba, if_false, mul_zero, zero_mul]

theorem rankLE_of_degeneratesAt_identity (F : Type u) [Field F]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (N r : ℕ) (T : Tensor3 F X Y Z)
    (h : CW90Eight.DegeneratesAt F N (Tensor3.identity F r) T) :
  RankLE T (r*(N+1)^2) := by
  classical
  obtain ⟨A₁, A₂, A₃, _, hcoeff⟩ := h
  let e : (Fin r × (Fin (N + 1) × Fin (N + 1))) ≃ Fin (r * (N + 1) ^ 2) :=
    Fintype.equivOfCardEq (by simp [pow_two])
  rw [rankLE_iff]
  refine ⟨
    (fun x ℓ =>
      let p := e.symm ℓ
      (A₁ x p.1).coeff p.2.2),
    (fun y ℓ =>
      let p := e.symm ℓ
      if p.2.2.1 ≤ p.2.1.1 then
        (A₂ y p.1).coeff (p.2.1.1 - p.2.2.1)
      else 0),
    (fun z ℓ =>
      let p := e.symm ℓ
      (A₃ z p.1).coeff (N - p.2.1.1)), ?_⟩
  intro x y z
  rw [← hcoeff x y z, identity_poly_sum,
    Polynomial.finset_sum_coeff]
  rw [← Equiv.sum_comp e]
  simp only [Fintype.sum_prod_type, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact coeff_mul_three_square (A₁ x i) (A₂ y i) (A₃ z i) N

end OmegaBound.ADVXXZGeneral
end
