import OmegaBound.ADVXXZGeneralMap
import OmegaBound.ADVXXZGeneralTensorCopiesZ

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- Multiplying one substitution leg by a power of the parameter raises a polynomial
degeneration to any prescribed larger degree. -/
theorem polyDegeneratesAt_raise
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'} {N M : ℕ}
    (hNM : N ≤ M) (h : PolyDegeneratesAt R N T U) :
    PolyDegeneratesAt R M T U := by
  classical
  obtain ⟨A, B, C, hlow, htop⟩ := h
  let d := M - N
  have hdN : d + N = M := by simp [d, Nat.sub_add_cancel hNM]
  have key : ∀ x y z,
      (∑ i, ∑ j, ∑ k,
        (Polynomial.X ^ d * A x i) * B y j * C z k * Polynomial.C (T i j k)) =
      Polynomial.X ^ d *
        (∑ i, ∑ j, ∑ k, A x i * B y j * C z k * Polynomial.C (T i j k)) := by
    intro x y z
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  refine ⟨fun x i => Polynomial.X ^ d * A x i, B, C, ?_, ?_⟩
  · intro x y z k hk
    rw [key, Polynomial.coeff_X_pow_mul']
    by_cases hdk : d ≤ k
    · rw [if_pos hdk, hlow x y z (k - d) (by omega)]
    · rw [if_neg hdk]
  · intro x y z
    rw [key, Polynomial.coeff_X_pow_mul', if_pos (by simp [d, hNM])]
    simpa [d, Nat.sub_sub_self hNM] using htop x y z

/-- Direct sums preserve polynomial degeneration when all summands use one common degree. -/
theorem polyDegeneratesAt_famDS_common
    {R : Type*} [CommRing R]
    {J X Y Z X' Y' Z' : Type*}
    [Fintype J] [DecidableEq J]
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (N : ℕ) (T : J → Tensor3 R X Y Z) (U : J → Tensor3 R X' Y' Z')
    (h : ∀ j, PolyDegeneratesAt R N (T j) (U j)) :
    PolyDegeneratesAt R N (famDS Finset.univ T) (famDS Finset.univ U) := by
  classical
  choose A B C hlow htop using h
  refine ⟨
    (fun p q => if p.1 = q.1 then A p.1 p.2 q.2 else 0),
    (fun p q => if p.1 = q.1 then B p.1 p.2 q.2 else 0),
    (fun p q => if p.1 = q.1 then C p.1 p.2 q.2 else 0), ?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ d hd
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp only [Fintype.sum_prod_type]
        simpa [famDS] using hlow i x y z d hd
      · simp only [Fintype.sum_prod_type]
        simp [famDS, hik]
    · simp only [Fintype.sum_prod_type]
      simp [famDS, hij]
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp only [Fintype.sum_prod_type]
        simpa [famDS] using htop i x y z
      · simp only [Fintype.sum_prod_type]
        simp [famDS, hik]
    · simp only [Fintype.sum_prod_type]
      simp [famDS, hij]

/-- Finitely many polynomial degenerations at possibly different degrees use the sum of
their degrees as a common degree, and hence assemble into one direct-sum degeneration. -/
theorem polyDegeneratesAt_famDS_commonDegree
    {R : Type*} [CommRing R]
    {J X Y Z X' Y' Z' : Type*}
    [Fintype J] [DecidableEq J]
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (degree : J → ℕ) (T : J → Tensor3 R X Y Z) (U : J → Tensor3 R X' Y' Z')
    (h : ∀ j, PolyDegeneratesAt R (degree j) (T j) (U j)) :
    PolyDegeneratesAt R (∑ j, degree j) (famDS Finset.univ T) (famDS Finset.univ U) := by
  apply polyDegeneratesAt_famDS_common
  intro j
  exact polyDegeneratesAt_raise (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    (h j)

end OmegaBound.ADVXXZGeneral
end
