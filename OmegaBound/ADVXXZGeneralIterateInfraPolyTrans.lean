import OmegaBound.ADVXXZGeneralMap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

section
universe u
open OmegaBound Tensor3 Polynomial Finset
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

variable {R : Type*} [CommRing R]
variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [Fintype X''] [Fintype Y''] [Fintype Z'']

private noncomputable def iterateActPoly (T : Tensor3 R X Y Z)
    (A₁ : X' → X → Polynomial R) (A₂ : Y' → Y → Polynomial R)
    (A₃ : Z' → Z → Polynomial R) (i : X') (j : Y') (k : Z') : Polynomial R :=
  ∑ a : X, ∑ b : Y, ∑ c : Z, A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)

private theorem iterateActPoly_expand (T : Tensor3 R X Y Z) (L : ℕ)
    (A₁ : X' → X → Polynomial R) (A₂ : Y' → Y → Polynomial R)
    (A₃ : Z' → Z → Polynomial R) (i : X') (j : Y') (k : Z') :
    iterateActPoly T (fun i a => Polynomial.expand R L (A₁ i a))
        (fun j b => Polynomial.expand R L (A₂ j b))
        (fun k c => Polynomial.expand R L (A₃ k c)) i j k =
      Polynomial.expand R L (iterateActPoly T A₁ A₂ A₃ i j k) := by
  simp only [iterateActPoly, map_sum, map_mul, Polynomial.expand_C]

private theorem iterate_sum6_comm {M : Type*} [AddCommMonoid M]
    (f : X → Y → Z → X' → Y' → Z' → M) :
    (∑ a : X, ∑ b : Y, ∑ c : Z, ∑ i' : X', ∑ j' : Y', ∑ k' : Z', f a b c i' j' k') =
      ∑ i' : X', ∑ j' : Y', ∑ k' : Z', ∑ a : X, ∑ b : Y, ∑ c : Z, f a b c i' j' k' := by
  have h : ∀ g : (X × Y × Z) → (X' × Y' × Z') → M,
      (∑ p : X × Y × Z, ∑ q : X' × Y' × Z', g p q) =
        ∑ q : X' × Y' × Z', ∑ p : X × Y × Z, g p q := fun _ => Finset.sum_comm
  simpa [Fintype.sum_prod_type] using
    h (fun p q => f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2)

private theorem iterate_prod3_sum {M : Type*} [CommRing M]
    (a : X' → M) (b : Y' → M) (c : Z' → M) (s : M) :
    (∑ i : X', a i) * (∑ j : Y', b j) * (∑ k : Z', c k) * s =
      ∑ i : X', ∑ j : Y', ∑ k : Z', a i * b j * c k * s := by
  have h3 : ∀ x : M, x * (∑ k : Z', c k) * s = ∑ k : Z', x * c k * s := by
    intro x
    rw [Finset.mul_sum, Finset.sum_mul]
  have h2 : ∀ x : M, x * (∑ j : Y', b j) * (∑ k : Z', c k) * s =
      ∑ j : Y', ∑ k : Z', x * b j * c k * s := by
    intro x
    have hx : x * (∑ j : Y', b j) = ∑ j : Y', x * b j := by rw [Finset.mul_sum]
    rw [hx, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h3 (x * b j)
  have ha : (∑ i : X', a i) * (∑ j : Y', b j) =
      ∑ i : X', a i * (∑ j : Y', b j) := by rw [Finset.sum_mul]
  rw [ha, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => h2 (a i)

private theorem iterateActPoly_comp (T : Tensor3 R X Y Z)
    (A₁ : X' → X → Polynomial R) (A₂ : Y' → Y → Polynomial R)
    (A₃ : Z' → Z → Polynomial R)
    (B₁ : X'' → X' → Polynomial R) (B₂ : Y'' → Y' → Polynomial R)
    (B₃ : Z'' → Z' → Polynomial R) (i : X'') (j : Y'') (k : Z'') :
    iterateActPoly T (fun i a => ∑ i' : X', B₁ i i' * A₁ i' a)
        (fun j b => ∑ j' : Y', B₂ j j' * A₂ j' b)
        (fun k c => ∑ k' : Z', B₃ k k' * A₃ k' c) i j k =
      ∑ i' : X', ∑ j' : Y', ∑ k' : Z',
        B₁ i i' * B₂ j j' * B₃ k k' * iterateActPoly T A₁ A₂ A₃ i' j' k' := by
  classical
  have hL : iterateActPoly T (fun i a => ∑ i' : X', B₁ i i' * A₁ i' a)
        (fun j b => ∑ j' : Y', B₂ j j' * A₂ j' b)
        (fun k c => ∑ k' : Z', B₃ k k' * A₃ k' c) i j k =
      ∑ a : X, ∑ b : Y, ∑ c : Z, ∑ i' : X', ∑ j' : Y', ∑ k' : Z',
        B₁ i i' * B₂ j j' * B₃ k k' *
          (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [iterate_prod3_sum (fun i' => B₁ i i' * A₁ i' a)
      (fun j' => B₂ j j' * A₂ j' b) (fun k' => B₃ k k' * A₃ k' c)
      (Polynomial.C (T a b c))]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun k' _ => by ring
  have hR : (∑ i' : X', ∑ j' : Y', ∑ k' : Z',
        B₁ i i' * B₂ j j' * B₃ k k' * iterateActPoly T A₁ A₂ A₃ i' j' k') =
      ∑ i' : X', ∑ j' : Y', ∑ k' : Z', ∑ a : X, ∑ b : Y, ∑ c : Z,
        B₁ i i' * B₂ j j' * B₃ k k' *
          (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)) := by
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun k' _ => ?_
    simp only [iterateActPoly, Finset.mul_sum]
  rw [hL, hR]
  exact iterate_sum6_comm (fun a b c i' j' k' =>
    B₁ i i' * B₂ j j' * B₃ k k' *
      (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)))

private theorem iterate_aux_sub_lt {K m M : ℕ} (h₁ : K ≤ m) (h₂ : m < K + M) :
    m - K < M := by omega

/-- The explicit degree used by integral transitivity. -/
def polyTransDegree (N₁ N₂ : ℕ) : ℕ := (N₂ + 1) * N₁ + N₂

/-- Polynomial degeneration is transitive over an arbitrary commutative ring, in particular
over `ℤ`.  Rescaling the first parameter by `t ↦ t^(N₂+1)` keeps its error above the
leading term of the second degeneration. -/
theorem polyDegeneratesAt_trans
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    [DecidableEq X''] [DecidableEq Y''] [DecidableEq Z'']
    {T : Tensor3 R X Y Z} {S : Tensor3 R X' Y' Z'} {U : Tensor3 R X'' Y'' Z''}
    {N₁ N₂ : ℕ} (h₁ : PolyDegeneratesAt R N₁ T S)
    (h₂ : PolyDegeneratesAt R N₂ S U) :
    PolyDegeneratesAt R (polyTransDegree N₁ N₂) T U := by
  classical
  obtain ⟨A₁, A₂, A₃, hvanA, hcoA⟩ := h₁
  obtain ⟨B₁, B₂, B₃, hvanB, hcoB⟩ := h₂
  have hvanA' : ∀ i j k m, m < N₁ →
      (iterateActPoly T A₁ A₂ A₃ i j k).coeff m = 0 := hvanA
  have hcoA' : ∀ i j k,
      (iterateActPoly T A₁ A₂ A₃ i j k).coeff N₁ = S i j k := hcoA
  have hvanB' : ∀ i j k m, m < N₂ →
      (iterateActPoly S B₁ B₂ B₃ i j k).coeff m = 0 := hvanB
  have hcoB' : ∀ i j k,
      (iterateActPoly S B₁ B₂ B₃ i j k).coeff N₂ = U i j k := hcoB
  have hLpos : 0 < N₂ + 1 := Nat.succ_pos N₂
  have hdegree : (N₂ + 1) * (N₁ + 1) = polyTransDegree N₁ N₂ + 1 := by
    simp only [polyTransDegree]
    ring
  have hRemdvd : ∀ i j k,
      Polynomial.X ^ ((N₂ + 1) * (N₁ + 1)) ∣
        (Polynomial.expand R (N₂ + 1) (iterateActPoly T A₁ A₂ A₃ i j k) -
          Polynomial.X ^ ((N₂ + 1) * N₁) * Polynomial.C (S i j k)) := by
    intro i j k
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, Polynomial.coeff_expand hLpos, Polynomial.coeff_X_pow_mul']
    by_cases hdiv : (N₂ + 1) ∣ d
    · obtain ⟨t, rfl⟩ := hdiv
      have ht : t ≤ N₁ := by
        have hlt : (N₂ + 1) * t < (N₂ + 1) * (N₁ + 1) := hd
        exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)
      rw [if_pos ⟨t, rfl⟩, Nat.mul_div_cancel_left t hLpos]
      rcases lt_or_eq_of_le ht with hlt | rfl
      · rw [hvanA' i j k t hlt, if_neg (by
          intro hle
          exact absurd (Nat.le_of_mul_le_mul_left hle hLpos) (Nat.not_le.mpr hlt))]
        ring
      · rw [hcoA' i j k, if_pos (le_refl _), Nat.sub_self, Polynomial.coeff_C_zero]
        ring
    · rw [if_neg hdiv]
      have hz : (if (N₂ + 1) * N₁ ≤ d then
          (Polynomial.C (S i j k)).coeff (d - (N₂ + 1) * N₁) else 0) = 0 := by
        by_cases hle : (N₂ + 1) * N₁ ≤ d
        · rw [if_pos hle, Polynomial.coeff_C, if_neg]
          intro hzero
          exact hdiv ⟨N₁, le_antisymm (Nat.le_of_sub_eq_zero hzero) hle⟩
        · rw [if_neg hle]
      rw [hz]
      ring
  have hQ : ∀ i j k,
      iterateActPoly T
          (fun i a => ∑ i' : X', B₁ i i' * Polynomial.expand R (N₂ + 1) (A₁ i' a))
          (fun j b => ∑ j' : Y', B₂ j j' * Polynomial.expand R (N₂ + 1) (A₂ j' b))
          (fun k c => ∑ k' : Z', B₃ k k' * Polynomial.expand R (N₂ + 1) (A₃ k' c))
          i j k =
        Polynomial.X ^ ((N₂ + 1) * N₁) * iterateActPoly S B₁ B₂ B₃ i j k +
          ∑ i' : X', ∑ j' : Y', ∑ k' : Z', B₁ i i' * B₂ j j' * B₃ k k' *
            (Polynomial.expand R (N₂ + 1) (iterateActPoly T A₁ A₂ A₃ i' j' k') -
              Polynomial.X ^ ((N₂ + 1) * N₁) * Polynomial.C (S i' j' k')) := by
    intro i j k
    rw [iterateActPoly_comp]
    have hpush : Polynomial.X ^ ((N₂ + 1) * N₁) *
        iterateActPoly S B₁ B₂ B₃ i j k =
      ∑ i' : X', ∑ j' : Y', ∑ k' : Z', B₁ i i' * B₂ j j' * B₃ k k' *
        (Polynomial.X ^ ((N₂ + 1) * N₁) * Polynomial.C (S i' j' k')) := by
      simp only [iterateActPoly, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
        Finset.sum_congr rfl fun k' _ => by ring
    rw [hpush, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [iterateActPoly_expand T (N₂ + 1) A₁ A₂ A₃ i' j' k']
    ring
  have hRzero : ∀ i j k d, d < (N₂ + 1) * (N₁ + 1) →
      (∑ i' : X', ∑ j' : Y', ∑ k' : Z', B₁ i i' * B₂ j j' * B₃ k k' *
        (Polynomial.expand R (N₂ + 1) (iterateActPoly T A₁ A₂ A₃ i' j' k') -
          Polynomial.X ^ ((N₂ + 1) * N₁) * Polynomial.C (S i' j' k'))).coeff d = 0 := by
    intro i j k
    refine Polynomial.X_pow_dvd_iff.mp ?_
    exact Finset.dvd_sum fun i' _ => Finset.dvd_sum fun j' _ => Finset.dvd_sum fun k' _ =>
      Dvd.dvd.mul_left (hRemdvd i' j' k') _
  refine ⟨
    (fun i a => ∑ i' : X', B₁ i i' * Polynomial.expand R (N₂ + 1) (A₁ i' a)),
    (fun j b => ∑ j' : Y', B₂ j j' * Polynomial.expand R (N₂ + 1) (A₂ j' b)),
    (fun k c => ∑ k' : Z', B₃ k k' * Polynomial.expand R (N₂ + 1) (A₃ k' c)), ?_, ?_⟩
  · intro i j k m hm
    change (iterateActPoly T
      (fun i a => ∑ i' : X', B₁ i i' * Polynomial.expand R (N₂ + 1) (A₁ i' a))
      (fun j b => ∑ j' : Y', B₂ j j' * Polynomial.expand R (N₂ + 1) (A₂ j' b))
      (fun k c => ∑ k' : Z', B₃ k k' * Polynomial.expand R (N₂ + 1) (A₃ k' c)) i j k).coeff m = 0
    rw [hQ i j k, Polynomial.coeff_add,
      hRzero i j k m (by rw [hdegree]; exact Nat.lt_succ_of_lt hm),
      Polynomial.coeff_X_pow_mul']
    by_cases hle : (N₂ + 1) * N₁ ≤ m
    · rw [if_pos hle, hvanB' i j k (m - (N₂ + 1) * N₁)
        (iterate_aux_sub_lt hle hm)]
      ring
    · rw [if_neg hle]
      ring
  · intro i j k
    change (iterateActPoly T
      (fun i a => ∑ i' : X', B₁ i i' * Polynomial.expand R (N₂ + 1) (A₁ i' a))
      (fun j b => ∑ j' : Y', B₂ j j' * Polynomial.expand R (N₂ + 1) (A₂ j' b))
      (fun k c => ∑ k' : Z', B₃ k k' * Polynomial.expand R (N₂ + 1) (A₃ k' c)) i j k).coeff
        (polyTransDegree N₁ N₂) = U i j k
    rw [hQ i j k, Polynomial.coeff_add,
      hRzero i j k _ (by rw [hdegree]; exact Nat.lt_succ_self _),
      Polynomial.coeff_X_pow_mul', if_pos (by simp [polyTransDegree]),
      show polyTransDegree N₁ N₂ - (N₂ + 1) * N₁ = N₂ by simp [polyTransDegree],
      hcoB' i j k]
    ring

/-- Existential-degree form used by recursive assembly over `ℤ`. -/
theorem integral_polyDegeneratesAt_trans
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    [DecidableEq X''] [DecidableEq Y''] [DecidableEq Z'']
    {T : Tensor3 ℤ X Y Z} {S : Tensor3 ℤ X' Y' Z'} {U : Tensor3 ℤ X'' Y'' Z''}
    {N₁ N₂ : ℕ} (h₁ : PolyDegeneratesAt ℤ N₁ T S)
    (h₂ : PolyDegeneratesAt ℤ N₂ S U) :
    ∃ N, PolyDegeneratesAt ℤ N T U :=
  ⟨polyTransDegree N₁ N₂, polyDegeneratesAt_trans h₁ h₂⟩

end OmegaBound.ADVXXZGeneral
end
