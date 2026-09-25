import OmegaBound.BorderRank

/-!
# Transitivity of degeneration

`Tensor3.Degenerates F T S` says that the `N`-th `ε`-coefficient of a polynomial substitution
applied to `T` is `S`, and that all lower coefficients vanish.  The master bridge is a
composite of degenerations — the global stage degenerates the seed power to the global interface,
the constituent stage degenerates each interface term to its level-2 children, and the level-2
closure degenerates those to matrix multiplication tensors — so transitivity is proved here.

## Why it is not a one-liner

Naively substituting one polynomial substitution into the other fails.  If

    act(A(ε)) T = ε^N S + O(ε^{N+1})    and    act(B(ε)) S = ε^M U + O(ε^{M+1}),

then `act(B(ε)) (act(A(ε)) T) = ε^N (ε^M U + O(ε^{M+1})) + O(ε^{N+1})`, and the second error
term has order `N+1`, which is **below** the target order `N + M` as soon as `M ≥ 2`.  The fix is
to rescale the inner substitution: replace `A(ε)` by `A(ε^L)` with `L = M + 1`, which is
`Polynomial.expand F L` applied entrywise.  Then the inner error sits at order `L(N+1) = LN+M+1`,
one above the target order `LN + M`.  `degenerates_trans` implements exactly that; the
resulting order is `transOrder N M = (M + 1) * N + M`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Polynomial Tensor3 Finset

namespace OmegaBound
namespace ADVXXZDegenTrans

variable {F : Type*} [Field F]

section

variable {α β γ α' β' γ' α'' β'' γ'' : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [Fintype α'] [Fintype β'] [Fintype γ']
variable [Fintype α''] [Fintype β''] [Fintype γ'']

/-- The polynomial attached to a substitution and a target index triple.  `Degenerates` is a
statement about the coefficients of exactly this polynomial. -/
noncomputable def actPoly (T : Tensor3 F α β γ)
    (A₁ : α' → α → Polynomial F) (A₂ : β' → β → Polynomial F)
    (A₃ : γ' → γ → Polynomial F) (i : α') (j : β') (k : γ') : Polynomial F :=
  ∑ a : α, ∑ b : β, ∑ c : γ, A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)

/-- Rescaling `ε ↦ ε^L` entrywise rescales the whole substitution polynomial. -/
theorem actPoly_expand (T : Tensor3 F α β γ) (L : ℕ)
    (A₁ : α' → α → Polynomial F) (A₂ : β' → β → Polynomial F)
    (A₃ : γ' → γ → Polynomial F) (i : α') (j : β') (k : γ') :
    actPoly T (fun i a => Polynomial.expand F L (A₁ i a))
        (fun j b => Polynomial.expand F L (A₂ j b))
        (fun k c => Polynomial.expand F L (A₃ k c)) i j k
      = Polynomial.expand F L (actPoly T A₁ A₂ A₃ i j k) := by
  simp only [actPoly, map_sum, map_mul, Polynomial.expand_C]

/-- Commuting a six-fold finite sum. -/
private theorem sum6_comm {M : Type*} [AddCommMonoid M]
    (f : α → β → γ → α' → β' → γ' → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ i' : α', ∑ j' : β', ∑ k' : γ', f a b c i' j' k')
      = ∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ a : α, ∑ b : β, ∑ c : γ, f a b c i' j' k' := by
  have h1 : ∀ g : (α × β × γ) → (α' × β' × γ') → M,
      (∑ p : α × β × γ, ∑ u : α' × β' × γ', g p u)
        = ∑ u : α' × β' × γ', ∑ p : α × β × γ, g p u := fun _ => Finset.sum_comm
  simpa [Fintype.sum_prod_type] using
    h1 (fun p u => f p.1 p.2.1 p.2.2 u.1 u.2.1 u.2.2)

/-- A product of three finite sums, times a scalar. -/
private theorem prod3_sum {M : Type*} [CommRing M]
    (u : α' → M) (v : β' → M) (w : γ' → M) (s : M) :
    (∑ i' : α', u i') * (∑ j' : β', v j') * (∑ k' : γ', w k') * s
      = ∑ i' : α', ∑ j' : β', ∑ k' : γ', u i' * v j' * w k' * s := by
  have step3 : ∀ x : M, x * (∑ k' : γ', w k') * s = ∑ k' : γ', x * w k' * s := by
    intro x
    rw [Finset.mul_sum, Finset.sum_mul]
  have step2 : ∀ x : M, x * (∑ j' : β', v j') * (∑ k' : γ', w k') * s
      = ∑ j' : β', ∑ k' : γ', x * v j' * w k' * s := by
    intro x
    have hx : x * (∑ j' : β', v j') = ∑ j' : β', x * v j' := by rw [Finset.mul_sum]
    rw [hx, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j' _ => step3 (x * v j')
  have hu : (∑ i' : α', u i') * (∑ j' : β', v j') = ∑ i' : α', u i' * (∑ j' : β', v j') := by
    rw [Finset.sum_mul]
  rw [hu, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i' _ => step2 (u i')

/-- **Composing the two substitutions.**  The composite substitution matrices are the matrix
products `C₁ i a = ∑_{i'} B₁ i i' * A₁ i' a`, and the resulting polynomial is the `B`-weighted
sum of the inner polynomials.  This is the only place trilinearity of the action is used. -/
theorem actPoly_comp (T : Tensor3 F α β γ)
    (A₁ : α' → α → Polynomial F) (A₂ : β' → β → Polynomial F)
    (A₃ : γ' → γ → Polynomial F)
    (B₁ : α'' → α' → Polynomial F) (B₂ : β'' → β' → Polynomial F)
    (B₃ : γ'' → γ' → Polynomial F) (i : α'') (j : β'') (k : γ'') :
    actPoly T (fun i a => ∑ i' : α', B₁ i i' * A₁ i' a)
        (fun j b => ∑ j' : β', B₂ j j' * A₂ j' b)
        (fun k c => ∑ k' : γ', B₃ k k' * A₃ k' c) i j k
      = ∑ i' : α', ∑ j' : β', ∑ k' : γ',
          B₁ i i' * B₂ j j' * B₃ k k' * actPoly T A₁ A₂ A₃ i' j' k' := by
  classical
  have hL : actPoly T (fun i a => ∑ i' : α', B₁ i i' * A₁ i' a)
        (fun j b => ∑ j' : β', B₂ j j' * A₂ j' b)
        (fun k c => ∑ k' : γ', B₃ k k' * A₃ k' c) i j k
      = ∑ a : α, ∑ b : β, ∑ c : γ, ∑ i' : α', ∑ j' : β', ∑ k' : γ',
          B₁ i i' * B₂ j j' * B₃ k k' *
            (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [prod3_sum (fun i' => B₁ i i' * A₁ i' a) (fun j' => B₂ j j' * A₂ j' b)
      (fun k' => B₃ k k' * A₃ k' c) (Polynomial.C (T a b c))]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun k' _ => by ring
  have hR : (∑ i' : α', ∑ j' : β', ∑ k' : γ',
        B₁ i i' * B₂ j j' * B₃ k k' * actPoly T A₁ A₂ A₃ i' j' k')
      = ∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ a : α, ∑ b : β, ∑ c : γ,
          B₁ i i' * B₂ j j' * B₃ k k' *
            (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)) := by
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun k' _ => ?_
    simp only [actPoly, Finset.mul_sum]
  rw [hL, hR]
  exact sum6_comm (fun a b c i' j' k' =>
    B₁ i i' * B₂ j j' * B₃ k k' *
      (A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)))

/-! ## The composite order -/

private theorem aux_sub_lt {K m M : ℕ} (h1 : K ≤ m) (h2 : m < K + M) : m - K < M := by omega

/-- The order at which the composite degeneration lands: rescaling the inner substitution by
`ε ↦ ε^(M+1)` moves its order `N` to `(M+1) * N`, and the outer substitution adds `M`. -/
def transOrder (N M : ℕ) : ℕ := (M + 1) * N + M

/-- **Degeneration is transitive.**  This is the structural composition law the master bridge
needs: the tree's stages are degenerations, not restrictions. -/
theorem degenerates_trans {T : Tensor3 F α β γ} {S : Tensor3 F α' β' γ'}
    {U : Tensor3 F α'' β'' γ''}
    (h₁ : Degenerates F T S) (h₂ : Degenerates F S U) :
    Degenerates F T U := by
  classical
  obtain ⟨N, A₁, A₂, A₃, hvanA, hcoA⟩ := h₁
  obtain ⟨M, B₁, B₂, B₃, hvanB, hcoB⟩ := h₂
  have hvanA' : ∀ (i' : α') (j' : β') (k' : γ') (m : ℕ), m < N →
      (actPoly T A₁ A₂ A₃ i' j' k').coeff m = 0 := hvanA
  have hcoA' : ∀ (i' : α') (j' : β') (k' : γ'),
      (actPoly T A₁ A₂ A₃ i' j' k').coeff N = S i' j' k' := hcoA
  have hvanB' : ∀ (i : α'') (j : β'') (k : γ'') (m : ℕ), m < M →
      (actPoly S B₁ B₂ B₃ i j k).coeff m = 0 := hvanB
  have hcoB' : ∀ (i : α'') (j : β'') (k : γ''),
      (actPoly S B₁ B₂ B₃ i j k).coeff M = U i j k := hcoB
  have hLpos : 0 < M + 1 := Nat.succ_pos M
  have hMN : (M + 1) * (N + 1) = (M + 1) * N + M + 1 := by ring
  -- the remainder of the rescaled inner polynomial after its prescribed leading term
  have hRemdvd : ∀ (i' : α') (j' : β') (k' : γ'),
      Polynomial.X ^ ((M + 1) * (N + 1)) ∣
        (Polynomial.expand F (M + 1) (actPoly T A₁ A₂ A₃ i' j' k')
          - Polynomial.X ^ ((M + 1) * N) * Polynomial.C (S i' j' k')) := by
    intro i' j' k'
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, Polynomial.coeff_expand hLpos, Polynomial.coeff_X_pow_mul']
    by_cases hdd : (M + 1) ∣ d
    · obtain ⟨t, rfl⟩ := hdd
      have ht : t ≤ N := by
        have h1 : (M + 1) * t < (M + 1) * (N + 1) := hd
        exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h1)
      rw [if_pos ⟨t, rfl⟩, Nat.mul_div_cancel_left t hLpos]
      rcases lt_or_eq_of_le ht with hlt | rfl
      · rw [hvanA' i' j' k' t hlt, if_neg (by
          intro hle
          exact absurd (Nat.le_of_mul_le_mul_left hle hLpos) (Nat.not_le.mpr hlt))]
        ring
      · rw [hcoA' i' j' k', if_pos (le_refl _), Nat.sub_self, Polynomial.coeff_C_zero]
        ring
    · rw [if_neg hdd]
      have hzero : (if (M + 1) * N ≤ d then
          (Polynomial.C (S i' j' k')).coeff (d - (M + 1) * N) else 0) = 0 := by
        by_cases hle : (M + 1) * N ≤ d
        · rw [if_pos hle, Polynomial.coeff_C, if_neg]
          intro h0
          exact hdd ⟨N, le_antisymm (Nat.le_of_sub_eq_zero h0) hle⟩
        · rw [if_neg hle]
      rw [hzero]
      ring
  -- the composite polynomial splits into the prescribed leading part and a high-order remainder
  have hQ : ∀ (i : α'') (j : β'') (k : γ''),
      actPoly T (fun i a => ∑ i' : α', B₁ i i' * Polynomial.expand F (M + 1) (A₁ i' a))
          (fun j b => ∑ j' : β', B₂ j j' * Polynomial.expand F (M + 1) (A₂ j' b))
          (fun k c => ∑ k' : γ', B₃ k k' * Polynomial.expand F (M + 1) (A₃ k' c)) i j k
        = Polynomial.X ^ ((M + 1) * N) * actPoly S B₁ B₂ B₃ i j k
          + ∑ i' : α', ∑ j' : β', ∑ k' : γ',
              B₁ i i' * B₂ j j' * B₃ k k' *
                (Polynomial.expand F (M + 1) (actPoly T A₁ A₂ A₃ i' j' k')
                  - Polynomial.X ^ ((M + 1) * N) * Polynomial.C (S i' j' k')) := by
    intro i j k
    rw [actPoly_comp]
    have hpush : Polynomial.X ^ ((M + 1) * N) * actPoly S B₁ B₂ B₃ i j k
        = ∑ i' : α', ∑ j' : β', ∑ k' : γ',
            B₁ i i' * B₂ j j' * B₃ k k' *
              (Polynomial.X ^ ((M + 1) * N) * Polynomial.C (S i' j' k')) := by
      simp only [actPoly, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
        Finset.sum_congr rfl fun k' _ => by ring
    rw [hpush, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [actPoly_expand T (M + 1) A₁ A₂ A₃ i' j' k']
    ring
  have hRtot0 : ∀ (i : α'') (j : β'') (k : γ'') (d : ℕ), d < (M + 1) * (N + 1) →
      (∑ i' : α', ∑ j' : β', ∑ k' : γ',
        B₁ i i' * B₂ j j' * B₃ k k' *
          (Polynomial.expand F (M + 1) (actPoly T A₁ A₂ A₃ i' j' k')
            - Polynomial.X ^ ((M + 1) * N) * Polynomial.C (S i' j' k'))).coeff d = 0 := by
    intro i j k
    refine Polynomial.X_pow_dvd_iff.mp ?_
    exact Finset.dvd_sum fun i' _ => Finset.dvd_sum fun j' _ => Finset.dvd_sum fun k' _ =>
      Dvd.dvd.mul_left (hRemdvd i' j' k') _
  refine ⟨(M + 1) * N + M,
    fun i a => ∑ i' : α', B₁ i i' * Polynomial.expand F (M + 1) (A₁ i' a),
    fun j b => ∑ j' : β', B₂ j j' * Polynomial.expand F (M + 1) (A₂ j' b),
    fun k c => ∑ k' : γ', B₃ k k' * Polynomial.expand F (M + 1) (A₃ k' c), ?_, ?_⟩
  · intro i j k m hm
    show (actPoly T (fun i a => ∑ i' : α', B₁ i i' * Polynomial.expand F (M + 1) (A₁ i' a))
      (fun j b => ∑ j' : β', B₂ j j' * Polynomial.expand F (M + 1) (A₂ j' b))
      (fun k c => ∑ k' : γ', B₃ k k' * Polynomial.expand F (M + 1) (A₃ k' c)) i j k).coeff m = 0
    rw [hQ i j k, Polynomial.coeff_add,
      hRtot0 i j k m (by rw [hMN]; exact Nat.lt_succ_of_lt hm),
      Polynomial.coeff_X_pow_mul']
    by_cases hle : (M + 1) * N ≤ m
    · rw [if_pos hle, hvanB' i j k (m - (M + 1) * N) (aux_sub_lt hle hm)]
      ring
    · rw [if_neg hle]
      ring
  · intro i j k
    show (actPoly T (fun i a => ∑ i' : α', B₁ i i' * Polynomial.expand F (M + 1) (A₁ i' a))
      (fun j b => ∑ j' : β', B₂ j j' * Polynomial.expand F (M + 1) (A₂ j' b))
      (fun k c => ∑ k' : γ', B₃ k k' * Polynomial.expand F (M + 1) (A₃ k' c)) i j k).coeff
        ((M + 1) * N + M) = U i j k
    rw [hQ i j k, Polynomial.coeff_add,
      hRtot0 i j k _ (by rw [hMN]; exact Nat.lt_succ_self _),
      Polynomial.coeff_X_pow_mul', if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      hcoB' i j k]
    ring

end

end ADVXXZDegenTrans
end OmegaBound
