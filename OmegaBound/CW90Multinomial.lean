import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# The six-part largest-term estimate

Coppersmith–Winograd 1990, §7, needs the multinomial version of the three-part (central trinomial)
largest-term estimate: with the six part sizes
`n = (L, L, L, N-L, N-L, N-L)`, whose sum is `3N`,

  `(3N)^{3N} ≤ (3N+1)^5 · binom(3N; n) · ∏ᵢ nᵢ^{nᵢ}`.

The proof is the standard "largest term" argument.  Expanding `(n₁ + ⋯ + n₆)^{3N}` by the
multinomial theorem, the term at `k = n` is `binom(3N;n)·∏ nᵢ^{nᵢ}`, it is the largest of the
at most `(3N+1)^5` terms, and the sum is `(3N)^{3N}`.

Rather than working with six-dimensional antidiagonals we peel one part at a time.  The whole
argument is carried by the *two*-part case

  `pow_add_self_le_choose_mul : (u+v)^{u+v} ≤ (u+v+1)·C(u+v,u)·u^u·v^v`,

proved by a ratio test (`Nat.choose_succ_right_eq`): for the
sequence `t k = C(u+v,k)·u^k·v^{u+v-k}` summing to `(u+v)^{u+v}`, the peak sits exactly at
`k = u`.  Applying it five times, to `n₁ + (n₂ + ⋯ + n₆)`, then to `n₂ + (n₃ + ⋯ + n₆)`, and so
on, produces five factors `≤ (3N+1)`, the five binomial coefficients whose product is the
multinomial coefficient, and the six powers `nᵢ^{nᵢ}`.

Note `0 ^ 0 = 1` in `ℕ`, which is exactly what makes the degenerate part sizes (`L = 0`, or
`L = N`) come out right; see `pow27_le_multinomial_six`, the `L = 0` specialisation, which
recovers the rate `27` of the central trinomial bound.
-/

open Finset
open scoped Nat

namespace OmegaBound

namespace CW90

/-! ## The two-part case -/

/-- The `k`-th term of the binomial expansion `(u+v)^m = ∑ₖ C(m,k)·u^k·v^{m-k}`. -/
private def bterm (u v m k : ℕ) : ℕ := Nat.choose m k * (u ^ k * v ^ (m - k))

private lemma bterm_sum (u v m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), bterm u v m k = (u + v) ^ m := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [bterm, Nat.cast_id]
  ring

/-- Going up: below the peak `k = u` the terms increase. -/
private lemma bterm_step_up (u v k : ℕ) (hk : k < u) :
    bterm u v (u + v) k ≤ bterm u v (u + v) (k + 1) := by
  have harith : (k + 1) * v ≤ (u + v - k) * u := by
    calc (k + 1) * v ≤ u * v := Nat.mul_le_mul (by omega) (le_refl v)
      _ = v * u := Nat.mul_comm _ _
      _ ≤ (u + v - k) * u := Nat.mul_le_mul (by omega) (le_refl u)
  have hkey : (u + v).choose k * v ≤ (u + v).choose (k + 1) * u := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
    have hcs : (u + v).choose (k + 1) * (k + 1) = (u + v).choose k * (u + v - k) :=
      Nat.choose_succ_right_eq _ _
    calc (k + 1) * ((u + v).choose k * v)
        = ((k + 1) * v) * (u + v).choose k := by ring
      _ ≤ ((u + v - k) * u) * (u + v).choose k := Nat.mul_le_mul harith (le_refl _)
      _ = ((u + v).choose k * (u + v - k)) * u := by ring
      _ = ((u + v).choose (k + 1) * (k + 1)) * u := by rw [hcs]
      _ = (k + 1) * ((u + v).choose (k + 1) * u) := by ring
  have hpow : u + v - k = (u + v - (k + 1)) + 1 := by omega
  unfold bterm
  rw [hpow, pow_succ, pow_succ]
  calc (u + v).choose k * (u ^ k * (v ^ (u + v - (k + 1)) * v))
      = ((u + v).choose k * v) * (u ^ k * v ^ (u + v - (k + 1))) := by ring
    _ ≤ ((u + v).choose (k + 1) * u) * (u ^ k * v ^ (u + v - (k + 1))) :=
        Nat.mul_le_mul hkey (le_refl _)
    _ = (u + v).choose (k + 1) * (u ^ k * u * v ^ (u + v - (k + 1))) := by ring

/-- Going down: above the peak `k = u` the terms decrease. -/
private lemma bterm_step_down (u v k : ℕ) (hk : u ≤ k) (hk2 : k < u + v) :
    bterm u v (u + v) (k + 1) ≤ bterm u v (u + v) k := by
  have harith : (u + v - k) * u ≤ (k + 1) * v := by
    calc (u + v - k) * u ≤ v * u := Nat.mul_le_mul (by omega) (le_refl u)
      _ = u * v := Nat.mul_comm _ _
      _ ≤ (k + 1) * v := Nat.mul_le_mul (by omega) (le_refl v)
  have hkey : (u + v).choose (k + 1) * u ≤ (u + v).choose k * v := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
    have hcs : (u + v).choose (k + 1) * (k + 1) = (u + v).choose k * (u + v - k) :=
      Nat.choose_succ_right_eq _ _
    calc (k + 1) * ((u + v).choose (k + 1) * u)
        = ((u + v).choose (k + 1) * (k + 1)) * u := by ring
      _ = ((u + v).choose k * (u + v - k)) * u := by rw [hcs]
      _ = ((u + v - k) * u) * (u + v).choose k := by ring
      _ ≤ ((k + 1) * v) * (u + v).choose k := Nat.mul_le_mul harith (le_refl _)
      _ = (k + 1) * ((u + v).choose k * v) := by ring
  have hpow : u + v - k = (u + v - (k + 1)) + 1 := by omega
  unfold bterm
  rw [hpow, pow_succ, pow_succ]
  calc (u + v).choose (k + 1) * (u ^ k * u * v ^ (u + v - (k + 1)))
      = ((u + v).choose (k + 1) * u) * (u ^ k * v ^ (u + v - (k + 1))) := by ring
    _ ≤ ((u + v).choose k * v) * (u ^ k * v ^ (u + v - (k + 1))) :=
        Nat.mul_le_mul hkey (le_refl _)
    _ = (u + v).choose k * (u ^ k * (v ^ (u + v - (k + 1)) * v)) := by ring

private lemma bterm_le_peak (u v : ℕ) :
    ∀ k, k ≤ u + v → bterm u v (u + v) k ≤ bterm u v (u + v) u := by
  have hup : ∀ j, j ≤ u → bterm u v (u + v) (u - j) ≤ bterm u v (u + v) u := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hstep : bterm u v (u + v) (u - (j + 1)) ≤ bterm u v (u + v) (u - (j + 1) + 1) :=
          bterm_step_up u v (u - (j + 1)) (by omega)
        have heq : u - (j + 1) + 1 = u - j := by omega
        rw [heq] at hstep
        exact hstep.trans (ih (by omega))
  have hdn : ∀ j, u + j ≤ u + v → bterm u v (u + v) (u + j) ≤ bterm u v (u + v) u := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hstep : bterm u v (u + v) (u + j + 1) ≤ bterm u v (u + v) (u + j) :=
          bterm_step_down u v (u + j) (by omega) (by omega)
        have heq : u + (j + 1) = u + j + 1 := by omega
        rw [heq]
        exact hstep.trans (ih (by omega))
  intro k hk
  rcases Nat.lt_or_ge u k with h | h
  · have := hdn (k - u) (by omega)
    rwa [show u + (k - u) = k by omega] at this
  · have := hup (u - k) (by omega)
    rwa [show u - (u - k) = k by omega] at this

/-- **The two-part largest-term bound.**  Expanding `(u+v)^{u+v}` by the binomial theorem, the
largest of the `u+v+1` terms sits at `k = u`, where it equals `C(u+v,u)·u^u·v^v`. -/
theorem pow_add_self_le_choose_mul (u v : ℕ) :
    (u + v) ^ (u + v) ≤ (u + v + 1) * (Nat.choose (u + v) u * (u ^ u * v ^ v)) := by
  have hpeak : bterm u v (u + v) u = Nat.choose (u + v) u * (u ^ u * v ^ v) := by
    unfold bterm
    rw [show u + v - u = v by omega]
  rw [← bterm_sum u v (u + v), ← hpeak]
  calc ∑ k ∈ Finset.range (u + v + 1), bterm u v (u + v) k
      ≤ ∑ _k ∈ Finset.range (u + v + 1), bterm u v (u + v) u :=
        Finset.sum_le_sum fun k hk =>
          bterm_le_peak u v k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (u + v + 1) * bterm u v (u + v) u := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- One peeling step, in the shape the six-fold iteration needs: the factor `u+v+1` is weakened
to the global `S+1`, and the tail `v^v` to any upper bound `X` for it. -/
private lemma peel_step (S u v X : ℕ) (hS : u + v ≤ S) (hX : v ^ v ≤ X) :
    (u + v) ^ (u + v) ≤ (S + 1) * (Nat.choose (u + v) u * (u ^ u * X)) := by
  calc (u + v) ^ (u + v) ≤ (u + v + 1) * (Nat.choose (u + v) u * (u ^ u * v ^ v)) :=
        pow_add_self_le_choose_mul u v
    _ ≤ (S + 1) * (Nat.choose (u + v) u * (u ^ u * X)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX))

/-! ## The six-part case -/

/-- The six-part multinomial coefficient as a chain of five binomial coefficients. -/
theorem multinomial_six_eq (a b c d e f : ℕ) :
    Nat.multinomial Finset.univ ![a, b, c, d, e, f] =
      (a + (b + (c + (d + (e + f))))).choose a * ((b + (c + (d + (e + f)))).choose b *
        ((c + (d + (e + f))).choose c * ((d + (e + f)).choose d * (e + f).choose e))) := by
  have hfac : ∀ i j : ℕ, (i + j).choose i * (i ! * j !) = (i + j)! := by
    intro i j
    have h := Nat.add_choose_mul_factorial_mul_factorial j i
    rw [Nat.add_comm j i] at h
    rw [← h]; ring
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin 6)) ![a, b, c, d, e, f]
  have hprod : ∏ i, (![a, b, c, d, e, f] i)! = a ! * b ! * c ! * d ! * e ! * f ! := by
    rw [Fin.prod_univ_six]; rfl
  have hsum : ∑ i, ![a, b, c, d, e, f] i = a + (b + (c + (d + (e + f)))) := by
    rw [Fin.sum_univ_six]
    change a + b + c + d + e + f = _
    ring
  rw [hprod, hsum] at hspec
  have hpos : 0 < a ! * b ! * c ! * d ! * e ! * f ! := by positivity
  refine Nat.eq_of_mul_eq_mul_left hpos (hspec.trans ?_)
  calc (a + (b + (c + (d + (e + f)))))!
      = (a + (b + (c + (d + (e + f))))).choose a *
          (a ! * ((b + (c + (d + (e + f)))).choose b *
            (b ! * ((c + (d + (e + f))).choose c *
              (c ! * ((d + (e + f)).choose d *
                (d ! * ((e + f).choose e * (e ! * f !))))))))) := by
        rw [hfac e f, hfac d (e + f), hfac c (d + (e + f)), hfac b (c + (d + (e + f))),
          hfac a (b + (c + (d + (e + f))))]
    _ = a ! * b ! * c ! * d ! * e ! * f ! *
          ((a + (b + (c + (d + (e + f))))).choose a * ((b + (c + (d + (e + f)))).choose b *
            ((c + (d + (e + f))).choose c * ((d + (e + f)).choose d * (e + f).choose e)))) := by
        ring

/-- The five-fold iteration of `peel_step`, with all five polynomial factors weakened to the
same `S + 1`. -/
private lemma chain_six (S a b c d e f : ℕ) (hS : a + (b + (c + (d + (e + f)))) ≤ S) :
    (a + (b + (c + (d + (e + f))))) ^ (a + (b + (c + (d + (e + f))))) ≤
      (S + 1) ^ 5 *
        ((a + (b + (c + (d + (e + f))))).choose a * ((b + (c + (d + (e + f)))).choose b *
          ((c + (d + (e + f))).choose c * ((d + (e + f)).choose d * (e + f).choose e)))) *
        (a ^ a * b ^ b * c ^ c * d ^ d * e ^ e * f ^ f) := by
  have g5 := peel_step S e f (f ^ f) (by omega) (le_refl _)
  have g4 := peel_step S d (e + f) _ (by omega) g5
  have g3 := peel_step S c (d + (e + f)) _ (by omega) g4
  have g2 := peel_step S b (c + (d + (e + f))) _ (by omega) g3
  have g1 := peel_step S a (b + (c + (d + (e + f)))) _ (by omega) g2
  exact g1.trans (le_of_eq (by ring))

/-- **The six-part largest-term bound**, general form.  With `S = a+b+c+d+e+f`,

  `S^S ≤ (S+1)^5 · binom(S; a,b,c,d,e,f) · a^a·b^b·c^c·d^d·e^e·f^f`. -/
theorem pow_sum_le_multinomial_six (a b c d e f : ℕ) :
    (a + b + c + d + e + f) ^ (a + b + c + d + e + f) ≤
      (a + b + c + d + e + f + 1) ^ 5 * Nat.multinomial Finset.univ ![a, b, c, d, e, f] *
        (a ^ a * b ^ b * c ^ c * d ^ d * e ^ e * f ^ f) := by
  rw [multinomial_six_eq, show a + b + c + d + e + f = a + (b + (c + (d + (e + f)))) by ring]
  exact chain_six _ a b c d e f (le_refl _)

/-- **The six-part largest-term bound** in the form CW90 §7 uses it: the six part sizes are
`(L, L, L, N-L, N-L, N-L)`, summing to `3N`. -/
theorem multinomial_six_lower (N L : ℕ) (hL : L ≤ N) :
    (3 * N) ^ (3 * N) ≤
      (3 * N + 1) ^ 5 * Nat.multinomial Finset.univ ![L, L, L, N - L, N - L, N - L] *
        (N - L) ^ (3 * (N - L)) * L ^ (3 * L) := by
  have h := pow_sum_le_multinomial_six L L L (N - L) (N - L) (N - L)
  rw [show L + L + L + (N - L) + (N - L) + (N - L) = 3 * N by omega] at h
  have hp1 : (N - L) ^ (3 * (N - L)) =
      (N - L) ^ (N - L) * (N - L) ^ (N - L) * (N - L) ^ (N - L) := by
    rw [show 3 * (N - L) = (N - L) + (N - L) + (N - L) by ring, pow_add, pow_add]
  have hp2 : L ^ (3 * L) = L ^ L * L ^ L * L ^ L := by
    rw [show 3 * L = L + L + L by ring, pow_add, pow_add]
  refine h.trans (le_of_eq ?_)
  rw [hp1, hp2]
  ring

/-- The `L = 0` sanity check: the six-part bound degenerates to the central trinomial bound,
i.e. to the rate `27`. -/
theorem pow27_le_multinomial_six (N : ℕ) :
    27 ^ N ≤ (3 * N + 1) ^ 5 * (Nat.choose (3 * N) N * Nat.choose (2 * N) N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  have hmul : Nat.multinomial Finset.univ ![0, 0, 0, N, N, N] =
      Nat.choose (3 * N) N * Nat.choose (2 * N) N := by
    rw [multinomial_six_eq]
    rw [show N + (N + N) = 3 * N by ring, show N + N = 2 * N by ring]
    simp
  have h := multinomial_six_lower N 0 (Nat.zero_le N)
  rw [Nat.sub_zero, hmul] at h
  simp only [Nat.mul_zero, pow_zero, mul_one] at h
  -- `h : (3*N)^(3*N) ≤ (3*N+1)^5 * (C(3N,N)*C(2N,N)) * N^(3*N)`
  have hsplit : (3 * N) ^ (3 * N) = 27 ^ N * N ^ (3 * N) := by
    rw [Nat.mul_pow, show (27 : ℕ) ^ N = 3 ^ (3 * N) by rw [pow_mul]; norm_num]
  rw [hsplit] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hN _)

/-! ## Real-valued restatement -/

theorem multinomial_six_lower_real (N L : ℕ) (hL : L ≤ N) :
    ((3 * N : ℕ) : ℝ) ^ (3 * N) ≤
      ((3 * N + 1 : ℕ) : ℝ) ^ 5 *
        ((Nat.multinomial Finset.univ ![L, L, L, N - L, N - L, N - L] : ℕ) : ℝ) *
        ((N - L : ℕ) : ℝ) ^ (3 * (N - L)) * ((L : ℕ) : ℝ) ^ (3 * L) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (multinomial_six_lower N L hL)
  push_cast at h ⊢
  linarith

end CW90

end OmegaBound
