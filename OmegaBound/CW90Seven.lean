import OmegaBound.CW90Tensor

/-!
# Coppersmith–Winograd 1990, §7: the basic tensor and its border rank

Section 7 replaces the §6 tensor by

  `CW_q = ∑_{i=1}^q (x₀ y_i z_i + x_i y₀ z_i + x_i y_i z₀)
          + x₀ y₀ z_{q+1} + x₀ y_{q+1} z₀ + x_{q+1} y₀ z₀`,

equation (10) of the paper, still with `q + 2` multiplications:

  `λ^{-2} ∑_i (x₀ + λ x_i)(y₀ + λ y_i)(z₀ + λ z_i)`
  `- λ^{-3} (x₀ + λ² ∑ x_i)(y₀ + λ² ∑ y_i)(z₀ + λ² ∑ z_i)`
  `+ (λ^{-3} - q λ^{-2})(x₀ + λ³ x_{q+1})(y₀ + λ³ y_{q+1})(z₀ + λ³ z_{q+1})`.

Only the third product changes: its three factors acquire the new variables.  This file
writes that certificate out as finite `ℚ[X]` data (everything multiplied by `λ³`) and
verifies it for **general `q`**, exactly as `CW90.br_T` does for §6.

The variables now carry **three** block levels rather than two — `x₀` is level `0`,
`x₁ … x_q` level `1`, `x_{q+1}` level `2` — and the support of the tensor consists of the
six triples of levels summing to `2`:

  `(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)`.

That is the "6-pattern grading" the rest of §7 is built on.

## Main results

* `CW90.br_T7` — `R̄(CW_q) ≤ q + 2`, as explicit `ℚ[X]` data, general `q`.
* `CW90.degenerates_powT7` — `Degenerates ℚ (identity ℚ ((q+2)^n)) (powT (T7 q) n)`.
* `CW90.lvl7_add_of_ne_zero` — the six support patterns have levels summing to `2`.
-/

open Polynomial Finset Tensor3

namespace OmegaBound

namespace CW90

/-! ## The variables and the tensor -/

/-- Variable index for the §7 construction: `inl none` is `x₀` (block level `0`),
`inl (some i)` is `x_i` (level `1`), `inr ()` is `x_{q+1}` (level `2`). -/
abbrev Idx7 (q : ℕ) := Option (Fin q) ⊕ Unit

/-- The block level of a variable. -/
def lvl7 {q : ℕ} : Idx7 q → Fin 3
  | .inl none => 0
  | .inl (some _) => 1
  | .inr _ => 2

/-- `CW90.T7 q` is the tensor of Coppersmith–Winograd 1990, equation (10). -/
def T7 (q : ℕ) : Tensor3 ℚ (Idx7 q) (Idx7 q) (Idx7 q) := fun a b c =>
  match a, b, c with
  | .inl none, .inl (some i), .inl (some j) => if i = j then 1 else 0
  | .inl (some i), .inl none, .inl (some j) => if i = j then 1 else 0
  | .inl (some i), .inl (some j), .inl none => if i = j then 1 else 0
  | .inl none, .inl none, .inr _ => 1
  | .inl none, .inr _, .inl none => 1
  | .inr _, .inl none, .inl none => 1
  | _, _, _ => 0

/-- **The support of `T7` is graded**: a nonzero entry has its three block levels summing
to `2`.  These are the six patterns `(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)`
of the §7 grading. -/
theorem lvl7_add_of_ne_zero {q : ℕ} (a b c : Idx7 q) (h : T7 q a b c ≠ 0) :
    (lvl7 a).val + (lvl7 b).val + (lvl7 c).val = 2 := by
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;> rcases c with (_ | c) | c <;>
    simp_all [T7, lvl7]

/-! ## The `q+2` multiplications -/

private def d7 {ι : Type*} [DecidableEq ι] (a b : ι) : ℚ := if a = b then 1 else 0

private lemma d7_comm {ι : Type*} [DecidableEq ι] (a b : ι) : d7 a b = d7 b a := by
  unfold d7
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

private lemma d7_self {ι : Type*} [DecidableEq ι] (a : ι) : d7 a a = 1 := by simp [d7]

private lemma sum_d7 {q : ℕ} (a : Fin q) : ∑ i : Fin q, d7 a i = 1 := by simp [d7]

private lemma sum_d7₂ {q : ℕ} (a b : Fin q) : ∑ i : Fin q, d7 a i * d7 b i = d7 a b := by
  rw [Finset.sum_eq_single a]
  · rw [d7_comm b a, d7_self, one_mul]
  · intro i _ hi
    simp [d7, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma sum_d7₃ {q : ℕ} (a b c : Fin q) :
    ∑ i : Fin q, d7 a i * d7 b i * d7 c i = d7 a b * d7 a c := by
  rw [Finset.sum_eq_single a]
  · rw [d7_comm b a, d7_comm c a, d7_self, one_mul]
  · intro i _ hi
    simp [d7, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma sum_C_mul7 {q m : ℕ} (f : Fin q → ℚ) :
    ∑ i : Fin q, Polynomial.C (f i) * X ^ m
      = Polynomial.C (∑ i : Fin q, f i) * X ^ m := by
  rw [map_sum, Finset.sum_mul]

private lemma sum_split7 (q : ℕ) (f : Mul q → ℚ[X]) :
    ∑ ℓ : Mul q, f ℓ = (∑ i : Fin q, f (.inl i)) + (f (.inr false) + f (.inr true)) := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_bool]
  ring

/-- The scalar `1 - q λ` that multiplies the third product. -/
private noncomputable def uu (q : ℕ) : ℚ[X] := 1 - Polynomial.C (q : ℚ) * X

/-- First factor of the §7 border-rank decomposition (multiplied through by `λ³`). -/
private noncomputable def A17 (q : ℕ) : Idx7 q → Mul q → ℚ[X]
  | .inl none, .inl _ => X
  | .inl (some j), .inl i => Polynomial.C (d7 j i) * X ^ 2
  | .inr _, .inl _ => 0
  | .inl none, .inr false => -1
  | .inl (some _), .inr false => -X ^ 2
  | .inr _, .inr false => 0
  | .inl none, .inr true => uu q
  | .inl (some _), .inr true => 0
  | .inr _, .inr true => uu q * X ^ 3

/-- Second (and third) factor of the §7 border-rank decomposition. -/
private noncomputable def A27 (q : ℕ) : Idx7 q → Mul q → ℚ[X]
  | .inl none, _ => 1
  | .inl (some j), .inl i => Polynomial.C (d7 j i) * X
  | .inl (some _), .inr false => X ^ 2
  | .inl (some _), .inr true => 0
  | .inr _, .inl _ => 0
  | .inr _, .inr false => 0
  | .inr _, .inr true => X ^ 3

/-- The error term of the §7 border-rank decomposition. -/
private noncomputable def BQ7 (q : ℕ) : Idx7 q → Idx7 q → Idx7 q → ℚ[X] := fun a b c =>
  match a, b, c with
  | .inl none, .inl (some i), .inl (some j) => Polynomial.C (d7 i j) - X
  | .inl (some i), .inl none, .inl (some j) => Polynomial.C (d7 i j) - X
  | .inl (some i), .inl (some j), .inl none => Polynomial.C (d7 i j) - X
  | .inl (some i), .inl (some j), .inl (some k) =>
      Polynomial.C (d7 i j) * Polynomial.C (d7 i k) * X - X ^ 3
  | .inl none, .inl none, .inr _ => uu q
  | .inl none, .inr _, .inl none => uu q
  | .inr _, .inl none, .inl none => uu q
  | .inl none, .inr _, .inr _ => uu q * X ^ 3
  | .inr _, .inl none, .inr _ => uu q * X ^ 3
  | .inr _, .inr _, .inl none => uu q * X ^ 3
  | .inr _, .inr _, .inr _ => uu q * X ^ 6
  | _, _, _ => 0

/-- **`R̄(CW_q) ≤ q + 2` for the §7 tensor**, as explicit `ℚ[X]` data. -/
theorem br_T7 (q : ℕ) : BR (T7 q) (Mul q) := by
  refine ⟨3, A17 q, A27 q, A27 q, BQ7 q, ?_, ?_⟩
  · intro a b c
    rw [sum_split7]
    rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;> rcases c with (_ | c) | c <;>
      simp only [A17, A27, BQ7, uu, mul_one, one_mul, mul_zero, zero_mul, neg_mul, mul_neg]
    -- (0,0,0)
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Polynomial.C_eq_natCast]
      ring
    -- (0,0,s)
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7 c i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 c i) * X ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h, sum_C_mul7, sum_d7, map_one]
      ring
    -- (0,0,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (0,s,0)
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7 b i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 b i) * X ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h, sum_C_mul7, sum_d7, map_one]
      ring
    -- (0,s,s)
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7 b i) * X) * (Polynomial.C (d7 c i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 b i * d7 c i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7, sum_d7₂]
      ring
    -- (0,s,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (0,t,0)
    · simp only [Finset.sum_const_zero]
      ring
    -- (0,t,s)
    · simp only [Finset.sum_const_zero]
      ring
    -- (0,t,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (s,0,0)
    · rw [sum_C_mul7, sum_d7, map_one]
      ring
    -- (s,0,s)
    · have h : ∑ i : Fin q, Polynomial.C (d7 a i) * X ^ 2 * (Polynomial.C (d7 c i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 a i * d7 c i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7, sum_d7₂]
      ring
    -- (s,0,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (s,s,0)
    · have h : ∑ i : Fin q, Polynomial.C (d7 a i) * X ^ 2 * (Polynomial.C (d7 b i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 a i * d7 b i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7, sum_d7₂]
      ring
    -- (s,s,s)
    · have h : ∑ i : Fin q, Polynomial.C (d7 a i) * X ^ 2 *
            (Polynomial.C (d7 b i) * X) * (Polynomial.C (d7 c i) * X)
          = ∑ i : Fin q, Polynomial.C (d7 a i * d7 b i * d7 c i) * X ^ 4 :=
        Finset.sum_congr rfl fun i _ => by
          rw [Polynomial.C_mul, Polynomial.C_mul]; ring
      rw [h, sum_C_mul7, sum_d7₃, Polynomial.C_mul]
      ring
    -- (s,s,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (s,t,0)
    · simp only [Finset.sum_const_zero]
      ring
    -- (s,t,s)
    · simp only [Finset.sum_const_zero]
      ring
    -- (s,t,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,0,0)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,0,s)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,0,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,s,0)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,s,s)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,s,t)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,t,0)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,t,s)
    · simp only [Finset.sum_const_zero]
      ring
    -- (t,t,t)
    · simp only [Finset.sum_const_zero]
      ring
  · intro a b c
    rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;> rcases c with (_ | c) | c <;>
      simp only [BQ7, T7, uu, d7] <;>
      first
        | rfl
        | (split_ifs <;> simp)
        | simp

/-! ## The `n`-th power -/

/-- **`R̄(CW_q^{⊗n}) ≤ (q+2)^n`**, as a degeneration of the identity tensor. -/
theorem degenerates_powT7 (q n : ℕ) :
    Degenerates ℚ (Tensor3.identity ℚ ((q + 2) ^ n)) (powT (T7 q) n) :=
  BR.toDegenerates
    (((br_T7 q).pow n).reindex
      (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin n → Mul q) = (q + 2) ^ n)))

end CW90

end OmegaBound
