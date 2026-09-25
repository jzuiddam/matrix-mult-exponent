import OmegaBound.Rank
import OmegaBound.Rectangular
import OmegaBound.Tensor.Degenerates
import Mathlib.LinearAlgebra.Lagrange

/-!
# Border rank with a degree bound, and Bini's theorem

`BRankLE T r D` says that `T` is the leading coefficient of a rank-`r` decomposition over
`ℚ[ε]` whose error terms have degree at most `D`:

  `∑_{ℓ<r} A₁(i,ℓ)·A₂(j,ℓ)·A₃(k,ℓ) = ε^N · Q(i,j,k)`,  `Q(i,j,k)(0) = T(i,j,k)`,
  `deg Q(i,j,k) ≤ D`.

Three things are proved about it.

* `BRankLE.tensorProd` — border rank is submultiplicative and the degrees add.
* `BRankLE.toRankLE` — **Bini's theorem**: `R(T) ≤ (D+1)·r`.  The proof is Lagrange
  interpolation of `Q` at `D+1` nonzero rational points.
* `brankLE_of_degenerates` — a `Degenerates` statement from the repository (which carries
  no degree bound) yields `BRankLE` for *some* degree `D`.

Finally `tpow` is the `n`-fold tensor power and `BRankLE.tpow` iterates
`BRankLE.tensorProd`: an `n`-th power costs `rⁿ` with error degree `n·D`, so that Bini's
polynomial overhead `n·D+1` is negligible against `rⁿ`.
-/

open Tensor3 Finset Polynomial

namespace OmegaBound

universe u

variable {α β γ α' β' γ' : Type*}

/-! ## Definition -/

/-- The polynomial `∑_ℓ A₁(i,ℓ)·A₂(j,ℓ)·A₃(k,ℓ)`. -/
noncomputable def bpoly {r : ℕ} (A₁ : α → Fin r → ℚ[X]) (A₂ : β → Fin r → ℚ[X])
    (A₃ : γ → Fin r → ℚ[X]) (i : α) (j : β) (k : γ) : ℚ[X] :=
  ∑ ℓ : Fin r, A₁ i ℓ * A₂ j ℓ * A₃ k ℓ

/-- `BRankLE T r D`: border rank at most `r` with error degree at most `D`. -/
def BRankLE (T : Tensor3 ℚ α β γ) (r D : ℕ) : Prop :=
  ∃ (N : ℕ) (A₁ : α → Fin r → ℚ[X]) (A₂ : β → Fin r → ℚ[X]) (A₃ : γ → Fin r → ℚ[X])
    (Q : α → β → γ → ℚ[X]),
    (∀ i j k, bpoly A₁ A₂ A₃ i j k = X ^ N * Q i j k) ∧
    (∀ i j k, (Q i j k).coeff 0 = T i j k) ∧
    (∀ i j k, (Q i j k).natDegree ≤ D)

/-- Weakening the degree bound. -/
theorem BRankLE.mono_degree {T : Tensor3 ℚ α β γ} {r D D' : ℕ} (h : BRankLE T r D)
    (hD : D ≤ D') : BRankLE T r D' := by
  obtain ⟨N, A₁, A₂, A₃, Q, h1, h2, h3⟩ := h
  exact ⟨N, A₁, A₂, A₃, Q, h1, h2, fun i j k => (h3 i j k).trans hD⟩

/-! ## Submultiplicativity -/

/-- **Border rank is submultiplicative**, and the error degrees add. -/
theorem BRankLE.tensorProd {T : Tensor3 ℚ α β γ} {S : Tensor3 ℚ α' β' γ'} {r D r' D' : ℕ}
    (h : BRankLE T r D) (h' : BRankLE S r' D') :
    BRankLE (tensorProd T S) (r * r') (D + D') := by
  obtain ⟨N, A₁, A₂, A₃, Q, hQ, hQ0, hQd⟩ := h
  obtain ⟨N', B₁, B₂, B₃, Q', hQ', hQ0', hQd'⟩ := h'
  refine ⟨N + N',
    fun x ℓ => A₁ x.1 (finProdFinEquiv.symm ℓ).1 * B₁ x.2 (finProdFinEquiv.symm ℓ).2,
    fun y ℓ => A₂ y.1 (finProdFinEquiv.symm ℓ).1 * B₂ y.2 (finProdFinEquiv.symm ℓ).2,
    fun z ℓ => A₃ z.1 (finProdFinEquiv.symm ℓ).1 * B₃ z.2 (finProdFinEquiv.symm ℓ).2,
    fun x y z => Q x.1 y.1 z.1 * Q' x.2 y.2 z.2, ?_, ?_, ?_⟩
  · intro i j k
    have hsplit : bpoly (r := r * r')
        (fun x ℓ => A₁ x.1 (finProdFinEquiv.symm ℓ).1 * B₁ x.2 (finProdFinEquiv.symm ℓ).2)
        (fun y ℓ => A₂ y.1 (finProdFinEquiv.symm ℓ).1 * B₂ y.2 (finProdFinEquiv.symm ℓ).2)
        (fun z ℓ => A₃ z.1 (finProdFinEquiv.symm ℓ).1 * B₃ z.2 (finProdFinEquiv.symm ℓ).2)
        i j k
        = bpoly A₁ A₂ A₃ i.1 j.1 k.1 * bpoly B₁ B₂ B₃ i.2 j.2 k.2 := by
      simp only [bpoly]
      rw [← Equiv.sum_comp (finProdFinEquiv (m := r) (n := r'))]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [hsplit, hQ, hQ', pow_add]
    ring
  · intro i j k
    rw [mul_coeff_zero, hQ0, hQ0']
    obtain ⟨i₁, i₂⟩ := i; obtain ⟨j₁, j₂⟩ := j; obtain ⟨k₁, k₂⟩ := k
    rfl
  · intro i j k
    exact (natDegree_mul_le).trans (Nat.add_le_add (hQd _ _ _) (hQd' _ _ _))

/-! ## Bini's theorem -/

/-- **Bini's theorem.**  A border rank decomposition of error degree `D` yields a genuine
rank decomposition of size `(D+1)·r`: interpolate the error polynomial at `D+1` nonzero
rational points and read off its constant term. -/
theorem BRankLE.toRankLE {T : Tensor3 ℚ α β γ} {r D : ℕ} (h : BRankLE T r D) :
    RankLE T ((D + 1) * r) := by
  obtain ⟨N, A₁, A₂, A₃, Q, hQ, hQ0, hQd⟩ := h
  -- `D+1` distinct nonzero nodes
  set v : Fin (D + 1) → ℚ := fun t => (t : ℚ) + 1 with hv
  have hvinj : Function.Injective v := by
    intro s t hst
    simp only [hv, add_left_inj, Nat.cast_inj] at hst
    exact Fin.ext (by exact_mod_cast hst)
  have hvpos : ∀ t, (0 : ℚ) < v t := by
    intro t
    have : (0 : ℚ) ≤ (t : ℚ) := by positivity
    simp only [hv]; linarith
  have hvne : ∀ t, v t ≠ 0 := fun t => ne_of_gt (hvpos t)
  -- the interpolation weights
  set lam : Fin (D + 1) → ℚ :=
    fun t => (Lagrange.basis Finset.univ v t).eval 0 * ((v t) ^ N)⁻¹ with hlam
  rw [rankLE_iff]
  refine ⟨fun i ℓ => lam (finProdFinEquiv.symm ℓ).1 *
            (A₁ i (finProdFinEquiv.symm ℓ).2).eval (v (finProdFinEquiv.symm ℓ).1),
          fun j ℓ => (A₂ j (finProdFinEquiv.symm ℓ).2).eval (v (finProdFinEquiv.symm ℓ).1),
          fun k ℓ => (A₃ k (finProdFinEquiv.symm ℓ).2).eval (v (finProdFinEquiv.symm ℓ).1),
          ?_⟩
  intro i j k
  -- reindex `Fin ((D+1)*r)` as `Fin (D+1) × Fin r`
  rw [← Equiv.sum_comp (finProdFinEquiv (m := D + 1) (n := r))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  -- the inner sum is the evaluation of `bpoly`
  have hinner : ∀ t : Fin (D + 1),
      (∑ ℓ : Fin r, lam t * (A₁ i ℓ).eval (v t) *
        (A₂ j ℓ).eval (v t) * (A₃ k ℓ).eval (v t))
      = lam t * (bpoly A₁ A₂ A₃ i j k).eval (v t) := by
    intro t
    simp only [bpoly, eval_finset_sum, Finset.mul_sum, eval_mul]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [Finset.sum_congr rfl fun t _ => hinner t]
  -- `bpoly = X^N * Q`, so the weights recover the Lagrange coefficients of `Q`
  have hstep : ∀ t : Fin (D + 1),
      lam t * (bpoly A₁ A₂ A₃ i j k).eval (v t)
      = (Q i j k).eval (v t) * (Lagrange.basis Finset.univ v t).eval 0 := by
    intro t
    rw [hQ, eval_mul, eval_pow, eval_X, hlam]
    have hne : (v t : ℚ) ^ N ≠ 0 := pow_ne_zero _ (hvne t)
    rw [show (Polynomial.eval 0 (Lagrange.basis Finset.univ v t) * ((v t) ^ N)⁻¹) *
          ((v t) ^ N * Polynomial.eval (v t) (Q i j k))
        = (((v t) ^ N)⁻¹ * (v t) ^ N) *
          (Polynomial.eval (v t) (Q i j k) *
            Polynomial.eval 0 (Lagrange.basis Finset.univ v t)) from by ring,
      inv_mul_cancel₀ hne, one_mul]
  rw [Finset.sum_congr rfl fun t _ => hstep t]
  -- Lagrange interpolation of `Q i j k`
  have hdeg : (Q i j k).degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    have : (Q i j k).natDegree < (Finset.univ : Finset (Fin (D + 1))).card := by
      simpa using Nat.lt_succ_of_le (hQd i j k)
    exact_mod_cast Nat.cast_lt.mpr this
  have hinterp := Lagrange.eq_interpolate (v := v) (s := (Finset.univ : Finset (Fin (D + 1))))
    (f := Q i j k) (Set.injOn_of_injective hvinj) hdeg
  have hev : (Q i j k).eval 0 =
      ∑ t : Fin (D + 1), (Q i j k).eval (v t) * (Lagrange.basis Finset.univ v t).eval 0 := by
    conv_lhs => rw [hinterp]
    simp only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C]
  rw [← hev, ← hQ0 i j k, ← coeff_zero_eq_eval_zero]

/-! ## From `Degenerates` to `BRankLE` -/

/-- Acting on the identity tensor collapses the triple sum to a diagonal sum. -/
private lemma identity_poly_sum {r : ℕ} (f : Fin r → ℚ[X]) (g : Fin r → ℚ[X])
    (h : Fin r → ℚ[X]) :
    (∑ a : Fin r, ∑ b : Fin r, ∑ c : Fin r,
      f a * g b * h c * Polynomial.C (Tensor3.identity ℚ r a b c))
    = ∑ ℓ : Fin r, f ℓ * g ℓ * h ℓ := by
  simp only [Tensor3.identity]
  simp only [apply_ite Polynomial.C, map_one, map_zero, mul_ite, mul_one, mul_zero]
  simp only [ite_and]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A degeneration from the identity tensor is a border rank bound, for some degree. -/
theorem brankLE_of_degenerates [Fintype α] [Fintype β] [Fintype γ]
    {T : Tensor3 ℚ α β γ} {r : ℕ} (h : Degenerates ℚ (Tensor3.identity ℚ r) T) :
    ∃ D : ℕ, BRankLE T r D := by
  classical
  obtain ⟨N, A₁, A₂, A₃, hvanish, hcoeff⟩ := h
  have hbp : ∀ i j k, (∑ a : Fin r, ∑ b : Fin r, ∑ c : Fin r,
      A₁ i a * A₂ j b * A₃ k c * Polynomial.C (Tensor3.identity ℚ r a b c))
      = bpoly A₁ A₂ A₃ i j k := fun i j k => identity_poly_sum _ _ _
  -- divide out `X ^ N`
  have hdvd : ∀ i j k, X ^ N ∣ bpoly A₁ A₂ A₃ i j k := by
    intro i j k
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [← hbp]
    exact hvanish i j k d hd
  choose Q hQ using hdvd
  have hQ0 : ∀ i j k, (Q i j k).coeff 0 = T i j k := by
    intro i j k
    have := hcoeff i j k
    rw [hbp] at this
    rw [hQ i j k] at this
    rw [← this]
    have := Polynomial.coeff_X_pow_mul (Q i j k) N 0
    simpa using this.symm
  refine ⟨Finset.sup Finset.univ (fun p : α × β × γ => (Q p.1 p.2.1 p.2.2).natDegree),
    N, A₁, A₂, A₃, Q, hQ, hQ0, ?_⟩
  intro i j k
  exact Finset.le_sup (f := fun p : α × β × γ => (Q p.1 p.2.1 p.2.2).natDegree)
    (Finset.mem_univ (i, j, k))

/-! ## Tensor powers -/

/-- The index type of an `n`-fold tensor power. -/
def TIdx (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => TIdx α n × α

instance TIdx.instFintype (α : Type u) [Fintype α] (n : ℕ) : Fintype (TIdx α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (TIdx α n × α))

instance TIdx.instDecidableEq (α : Type u) [DecidableEq α] (n : ℕ) :
    DecidableEq (TIdx α n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (TIdx α n × α))

/-- The `n`-fold tensor power. -/
def tpow {R : Type*} [CommSemiring R] (T : Tensor3 R α β γ) :
    (n : ℕ) → Tensor3 R (TIdx α n) (TIdx β n) (TIdx γ n)
  | 0 => fun _ _ _ => 1
  | n + 1 => tensorProd (tpow T n) T

@[simp] theorem tpow_succ {R : Type*} [CommSemiring R] (T : Tensor3 R α β γ) (n : ℕ) :
    tpow T (n + 1) = tensorProd (tpow T n) T := rfl

/-- The trivial tensor has border rank one and error degree zero. -/
theorem brankLE_tpow_zero (T : Tensor3 ℚ α β γ) : BRankLE (tpow T 0) 1 0 := by
  refine ⟨0, fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, fun _ _ _ => 1, ?_, ?_, ?_⟩
  · intro i j k; simp [bpoly]
  · intro i j k; simp [tpow]
  · intro i j k; simp

/-- **Border rank of a tensor power.** -/
theorem BRankLE.tpow {T : Tensor3 ℚ α β γ} {r D : ℕ} (h : BRankLE T r D) (n : ℕ) :
    BRankLE (OmegaBound.tpow T n) (r ^ n) (n * D) := by
  induction n with
  | zero => simpa using brankLE_tpow_zero T
  | succ n ih =>
      have h2 := ih.tensorProd h
      rw [tpow_succ]
      have hd : n * D + D = (n + 1) * D := by ring
      have hr : r ^ n * r = r ^ (n + 1) := (pow_succ r n).symm
      rw [← hd, ← hr]
      exact h2

end OmegaBound
