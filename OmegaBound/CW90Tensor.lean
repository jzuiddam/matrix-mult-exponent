import OmegaBound.BorderRank

/-!
# Coppersmith–Winograd 1990, §6: the basic tensor and its border rank

The basic construction of Coppersmith–Winograd 1990, equation (5), is the tensor

  `T_q = ∑_{i=1}^q (x₀ y_i z_i + x_i y₀ z_i + x_i y_i z₀)`

on `q+1` variables in each of the three slots.  The paper exhibits it as a limit of
`q+2` products,

  `λ^{-2} ∑_i (x₀ + λ x_i)(y₀ + λ y_i)(z₀ + λ z_i)`
  `- λ^{-3} (x₀ + λ² ∑ x_i)(y₀ + λ² ∑ y_i)(z₀ + λ² ∑ z_i)`
  `+ (λ^{-3} - q λ^{-2}) x₀ y₀ z₀`
  `= T_q + O(λ)`,

so `R̄(T_q) ≤ q + 2`.  This file writes that certificate out as finite literal data over
`ℚ[X]` (clearing denominators: everything is multiplied by `λ³`) and verifies it, for
**general `q`**, by polynomial algebra — no `decide`, no `native_decide`.

## Main definitions

* `CW90.Idx q` — the variable index type, `Option (Fin q)`; `none` is `x₀`.
* `CW90.T q` — the tensor above.
* `CW90.BR T L` — border-rank data with the multiplication index set `L` left general.
  This is `Degenerates ℚ (identity ℚ |L|) T` with the bookkeeping deferred.
* `CW90.powT T n` — the `n`-fold tensor power indexed by `Fin n → α` (rather than the
  right-nested `TIdx` of `BorderRank.lean`).

## Main results

* `CW90.br_T` — `BR (T q) (Fin q ⊕ Bool)`, i.e. `R̄(T_q) ≤ q + 2`.
* `CW90.BR.pow` — `BR T L → BR (powT T n) (Fin n → L)`, border rank is submultiplicative.
* `CW90.degenerates_powT` — `Degenerates ℚ (identity ℚ ((q+2)^n)) (powT (T q) n)`.
-/

open Polynomial Finset Tensor3

namespace OmegaBound

namespace CW90

variable {α β γ : Type*}

/-! ## Border-rank data with a general index set for the multiplications -/

/-- `BR T L`: the tensor `T` is the constant term of `X^{-N} ∑_{ℓ ∈ L} A₁(ℓ)A₂(ℓ)A₃(ℓ)`.

This is exactly `Degenerates ℚ (Tensor3.identity ℚ |L|) T` (see `BR.toDegenerates`), but
with the index set of the multiplications left general, which makes the tensor power
`BR.pow` a one-line computation instead of an induction. -/
def BR (T : Tensor3 ℚ α β γ) (L : Type*) [Fintype L] : Prop :=
  ∃ (N : ℕ) (A₁ : α → L → ℚ[X]) (A₂ : β → L → ℚ[X]) (A₃ : γ → L → ℚ[X])
    (Q : α → β → γ → ℚ[X]),
    (∀ i j k, ∑ ℓ : L, A₁ i ℓ * A₂ j ℓ * A₃ k ℓ = X ^ N * Q i j k) ∧
    (∀ i j k, (Q i j k).coeff 0 = T i j k)

/-- Relabelling the multiplications. -/
theorem BR.reindex {T : Tensor3 ℚ α β γ} {L L' : Type*} [Fintype L] [Fintype L']
    (h : BR T L) (e : L ≃ L') : BR T L' := by
  obtain ⟨N, A₁, A₂, A₃, Q, h1, h2⟩ := h
  refine ⟨N, fun i ℓ => A₁ i (e.symm ℓ), fun j ℓ => A₂ j (e.symm ℓ),
    fun k ℓ => A₃ k (e.symm ℓ), Q, ?_, h2⟩
  intro i j k
  rw [← h1 i j k]
  exact Equiv.sum_comp e.symm (fun ℓ => A₁ i ℓ * A₂ j ℓ * A₃ k ℓ)

/-- The identity tensor collapses a triple sum to a diagonal sum. -/
private lemma identity_sum_eq {r : ℕ} (f g h : Fin r → ℚ[X]) :
    ∑ a : Fin r, ∑ b : Fin r, ∑ c : Fin r,
      f a * g b * h c * Polynomial.C (Tensor3.identity ℚ r a b c) =
    ∑ ℓ : Fin r, f ℓ * g ℓ * h ℓ := by
  simp only [Tensor3.identity]
  simp only [apply_ite Polynomial.C, map_one, map_zero, mul_ite, mul_one, mul_zero]
  simp only [ite_and]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Border-rank data on `Fin r` is a degeneration of the `r`-dimensional identity tensor. -/
theorem BR.toDegenerates [Fintype α] [Fintype β] [Fintype γ] {T : Tensor3 ℚ α β γ} {r : ℕ}
    (h : BR T (Fin r)) : Degenerates ℚ (Tensor3.identity ℚ r) T := by
  obtain ⟨N, A₁, A₂, A₃, Q, h1, h2⟩ := h
  refine ⟨N, A₁, A₂, A₃, ?_, ?_⟩
  · intro i j k m hm
    rw [identity_sum_eq, h1 i j k, coeff_X_pow_mul']
    simp [Nat.not_le.mpr hm]
  · intro i j k
    rw [identity_sum_eq, h1 i j k, coeff_X_pow_mul']
    simp [h2 i j k]

/-! ## Tensor powers indexed by functions -/

/-- The `n`-fold tensor power, with index sets `Fin n → α` etc. -/
def powT (T : Tensor3 ℚ α β γ) (n : ℕ) :
    Tensor3 ℚ (Fin n → α) (Fin n → β) (Fin n → γ) :=
  fun a b c => ∏ j : Fin n, T (a j) (b j) (c j)

theorem powT_apply (T : Tensor3 ℚ α β γ) (n : ℕ) (a : Fin n → α) (b : Fin n → β)
    (c : Fin n → γ) : powT T n a b c = ∏ j : Fin n, T (a j) (b j) (c j) := rfl

/-- **Border rank is submultiplicative under tensor powers.** -/
theorem BR.pow {T : Tensor3 ℚ α β γ} {L : Type*} [Fintype L]
    (h : BR T L) (n : ℕ) : BR (powT T n) (Fin n → L) := by
  classical
  obtain ⟨N, A₁, A₂, A₃, Q, h1, h2⟩ := h
  refine ⟨N * n,
    fun a ℓ => ∏ j : Fin n, A₁ (a j) (ℓ j),
    fun b ℓ => ∏ j : Fin n, A₂ (b j) (ℓ j),
    fun c ℓ => ∏ j : Fin n, A₃ (c j) (ℓ j),
    fun a b c => ∏ j : Fin n, Q (a j) (b j) (c j), ?_, ?_⟩
  · intro a b c
    have hstep : ∀ ℓ : Fin n → L,
        (∏ j : Fin n, A₁ (a j) (ℓ j)) * (∏ j : Fin n, A₂ (b j) (ℓ j)) *
          (∏ j : Fin n, A₃ (c j) (ℓ j))
        = ∏ j : Fin n, A₁ (a j) (ℓ j) * A₂ (b j) (ℓ j) * A₃ (c j) (ℓ j) := by
      intro ℓ
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp only [hstep]
    have hswap : ∑ ℓ : Fin n → L,
        ∏ j : Fin n, A₁ (a j) (ℓ j) * A₂ (b j) (ℓ j) * A₃ (c j) (ℓ j)
        = ∏ j : Fin n, ∑ m : L, A₁ (a j) m * A₂ (b j) m * A₃ (c j) m := by
      rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset L))
        (fun j m => A₁ (a j) m * A₂ (b j) m * A₃ (c j) m)]
      rw [Fintype.piFinset_univ]
    rw [hswap]
    simp only [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]
  · intro a b c
    have hc : ∀ p : ℚ[X], p.coeff 0 = Polynomial.constantCoeff p := fun p => rfl
    rw [hc, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [← hc]; exact h2 _ _ _

/-! ## The basic tensor -/

/-- The variable index type of the CW90 basic construction: `none` is `x₀` (block `[0]`),
`some i` is `x_i` (block `[1]`). -/
abbrev Idx (q : ℕ) := Option (Fin q)

/-- `CW90.T q = ∑_{i=1}^q (x₀ y_i z_i + x_i y₀ z_i + x_i y_i z₀)`, the basic tensor of
Coppersmith–Winograd 1990, equation (5). -/
def T (q : ℕ) : Tensor3 ℚ (Idx q) (Idx q) (Idx q) := fun a b c =>
  match a, b, c with
  | none, some i, some j => if i = j then 1 else 0
  | some i, none, some j => if i = j then 1 else 0
  | some i, some j, none => if i = j then 1 else 0
  | _, _, _ => 0

@[simp] theorem T_nn (q : ℕ) (c : Idx q) : T q none none c = 0 := by
  cases c <;> rfl

@[simp] theorem T_nsn (q : ℕ) (i : Fin q) : T q none (some i) none = 0 := rfl

@[simp] theorem T_nss (q : ℕ) (i j : Fin q) :
    T q none (some i) (some j) = if i = j then 1 else 0 := rfl

@[simp] theorem T_snn (q : ℕ) (i : Fin q) : T q (some i) none none = 0 := rfl

@[simp] theorem T_sns (q : ℕ) (i j : Fin q) :
    T q (some i) none (some j) = if i = j then 1 else 0 := rfl

@[simp] theorem T_ssn (q : ℕ) (i j : Fin q) :
    T q (some i) (some j) none = if i = j then 1 else 0 := rfl

@[simp] theorem T_sss (q : ℕ) (i j k : Fin q) : T q (some i) (some j) (some k) = 0 := rfl

/-! ## The `q+2` multiplications -/

/-- The index set of the `q+2` multiplications: `inl i` is the `i`-th product,
`inr false` is the "sum" product, `inr true` is the correction product. -/
abbrev Mul (q : ℕ) := Fin q ⊕ Bool

/-- A `ℚ`-valued Kronecker delta. -/
private def dl {ι : Type*} [DecidableEq ι] (a b : ι) : ℚ := if a = b then 1 else 0

private lemma sum_dl {q : ℕ} (a : Fin q) : ∑ i : Fin q, dl a i = 1 := by
  simp [dl]

private lemma sum_dl2 {q : ℕ} (a b : Fin q) :
    ∑ i : Fin q, dl a i * dl b i = dl a b := by
  simp only [dl, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ a (fun i => if b = i then (1 : ℚ) else 0)]
  simp only [Finset.mem_univ, if_true]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

private lemma dl_comm {ι : Type*} [DecidableEq ι] (a b : ι) : dl a b = dl b a := by
  unfold dl
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

private lemma dl_self {ι : Type*} [DecidableEq ι] (a : ι) : dl a a = 1 := by
  simp [dl]

private lemma sum_dl3 {q : ℕ} (a b c : Fin q) :
    ∑ i : Fin q, dl a i * dl b i * dl c i = dl a b * dl a c := by
  rw [Finset.sum_eq_single a]
  · rw [dl_comm b a, dl_comm c a, dl_self, one_mul]
  · intro i _ hi
    simp [dl, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- First factor of the CW90 border-rank decomposition (multiplied through by `λ³`). -/
private noncomputable def BA₁ (q : ℕ) : Idx q → Mul q → ℚ[X]
  | none, .inl _ => X
  | some j, .inl i => Polynomial.C (dl j i) * X ^ 2
  | none, .inr false => -1
  | some _, .inr false => -X ^ 2
  | none, .inr true => 1 - Polynomial.C (q : ℚ) * X
  | some _, .inr true => 0

/-- Second (and third) factor of the CW90 border-rank decomposition. -/
private noncomputable def BA₂ (q : ℕ) : Idx q → Mul q → ℚ[X]
  | none, _ => 1
  | some j, .inl i => Polynomial.C (dl j i) * X
  | some _, .inr false => X ^ 2
  | some _, .inr true => 0

/-- The error term of the CW90 border-rank decomposition. -/
private noncomputable def BQ (q : ℕ) : Idx q → Idx q → Idx q → ℚ[X] := fun a b c =>
  match a, b, c with
  | none, some i, some j => Polynomial.C (dl i j) - X
  | some i, none, some j => Polynomial.C (dl i j) - X
  | some i, some j, none => Polynomial.C (dl i j) - X
  | some i, some j, some k => Polynomial.C (dl i j) * Polynomial.C (dl i k) * X - X ^ 3
  | _, _, _ => 0

private lemma sum_split (q : ℕ) (f : Mul q → ℚ[X]) :
    ∑ ℓ : Mul q, f ℓ = (∑ i : Fin q, f (.inl i)) + (f (.inr false) + f (.inr true)) := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_bool]
  ring

/-- Pull a `C`-scalar out of a sum. -/
private lemma sum_C_mul {q m : ℕ} (f : Fin q → ℚ) :
    ∑ i : Fin q, Polynomial.C (f i) * X ^ m
      = Polynomial.C (∑ i : Fin q, f i) * X ^ m := by
  rw [map_sum, Finset.sum_mul]

/-- **`R̄(T_q) ≤ q + 2`, as explicit `ℚ[X]` data.** -/
theorem br_T (q : ℕ) : BR (T q) (Mul q) := by
  refine ⟨3, BA₁ q, BA₂ q, BA₂ q, BQ q, ?_, ?_⟩
  · intro a b c
    rw [sum_split]
    match a, b, c with
    | none, none, none =>
        simp only [BA₁, BA₂, BQ, mul_one]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Polynomial.C_eq_natCast]
        ring
    | none, none, some k =>
        simp only [BA₁, BA₂, BQ, mul_one]
        have h : ∑ i : Fin q, X * (Polynomial.C (dl k i) * X)
            = ∑ i : Fin q, Polynomial.C (dl k i) * X ^ 2 :=
          Finset.sum_congr rfl fun i _ => by ring
        rw [h, sum_C_mul, sum_dl, map_one]
        ring
    | none, some j, none =>
        simp only [BA₁, BA₂, BQ, mul_one]
        have h : ∑ i : Fin q, X * (Polynomial.C (dl j i) * X)
            = ∑ i : Fin q, Polynomial.C (dl j i) * X ^ 2 :=
          Finset.sum_congr rfl fun i _ => by ring
        rw [h, sum_C_mul, sum_dl, map_one]
        ring
    | some i₀, none, none =>
        simp only [BA₁, BA₂, BQ, mul_one]
        rw [sum_C_mul, sum_dl, map_one]
        ring
    | none, some j, some k =>
        simp only [BA₁, BA₂, BQ]
        have h : ∑ i : Fin q, X * (Polynomial.C (dl j i) * X) * (Polynomial.C (dl k i) * X)
            = ∑ i : Fin q, Polynomial.C (dl j i * dl k i) * X ^ 3 :=
          Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
        rw [h, sum_C_mul, sum_dl2]
        ring
    | some i₀, none, some k =>
        simp only [BA₁, BA₂, BQ, mul_one]
        have h : ∑ i : Fin q,
              Polynomial.C (dl i₀ i) * X ^ 2 * (Polynomial.C (dl k i) * X)
            = ∑ i : Fin q, Polynomial.C (dl i₀ i * dl k i) * X ^ 3 :=
          Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
        rw [h, sum_C_mul, sum_dl2]
        ring
    | some i₀, some j, none =>
        simp only [BA₁, BA₂, BQ, mul_one]
        have h : ∑ i : Fin q,
              Polynomial.C (dl i₀ i) * X ^ 2 * (Polynomial.C (dl j i) * X)
            = ∑ i : Fin q, Polynomial.C (dl i₀ i * dl j i) * X ^ 3 :=
          Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
        rw [h, sum_C_mul, sum_dl2]
        ring
    | some i₀, some j, some k =>
        simp only [BA₁, BA₂, BQ]
        have h : ∑ i : Fin q, Polynomial.C (dl i₀ i) * X ^ 2 *
              (Polynomial.C (dl j i) * X) * (Polynomial.C (dl k i) * X)
            = ∑ i : Fin q, Polynomial.C (dl i₀ i * dl j i * dl k i) * X ^ 4 :=
          Finset.sum_congr rfl fun i _ => by
            rw [Polynomial.C_mul, Polynomial.C_mul]; ring
        rw [h, sum_C_mul, sum_dl3, Polynomial.C_mul]
        ring
  · intro a b c
    match a, b, c with
    | none, none, none => simp [BQ]
    | none, none, some k => simp [BQ]
    | none, some j, none => simp [BQ]
    | some i₀, none, none => simp [BQ]
    | none, some j, some k =>
        simp only [BQ, T_nss, dl]
        by_cases h : j = k <;> simp [h]
    | some i₀, none, some k =>
        simp only [BQ, T_sns, dl]
        by_cases h : i₀ = k <;> simp [h]
    | some i₀, some j, none =>
        simp only [BQ, T_ssn, dl]
        by_cases h : i₀ = j <;> simp [h]
    | some i₀, some j, some k => simp [BQ]

/-! ## The `n`-th power -/

/-- The multiplication index set of the `n`-th power has `(q+2)^n` elements. -/
private lemma card_pow_mul (q n : ℕ) : Fintype.card (Fin n → Mul q) = (q + 2) ^ n := by
  simp

/-- **`R̄(T_q^{⊗n}) ≤ (q+2)^n`**, as a degeneration of the identity tensor. -/
theorem degenerates_powT (q n : ℕ) :
    Degenerates ℚ (Tensor3.identity ℚ ((q + 2) ^ n)) (powT (T q) n) :=
  BR.toDegenerates
    (((br_T q).pow n).reindex (Fintype.equivFinOfCardEq (card_pow_mul q n)))

end CW90

end OmegaBound
