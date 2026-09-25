import OmegaBound.ASI
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Combinatorial lemmas for the asymptotic sum inequality with many summands

Associativity and commutativity of `tensorProd` up to restriction (`tensorProd_comm_le`,
`tensorProd_assoc_le`, `tensorProd_assoc_le'`, `tensorProd_swap23_le`, `blockDiag_tensorProd_le'`);
`matMul_le_tpow`, `⟨a,b,c⟩^{⊗k}` inside `tpow`; the right-nested index type `mmIdxSum` of an
`s`-fold direct sum; the multiplicity `mmult` (a multinomial written as an iterated binomial); and
`exists_dominant_type_gen`: one type carries a `1/(N+1)^s` fraction of the weight.
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]

/-! ## Associativity and commutativity of the tensor product -/

section Plumbing

variable {α β γ α' β' γ' α'' β'' γ'' : Type*}
variable [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
variable [Fintype α''] [Fintype β''] [Fintype γ'']
variable [DecidableEq α''] [DecidableEq β''] [DecidableEq γ'']

theorem tensorProd_comm_le (X : Tensor3 R α β γ) (Y : Tensor3 R α' β' γ') :
    tensorProd X Y ≤ₜ tensorProd Y X := by
  refine Restricts.of_eq (precomp_restricts (fun x : α × α' => x.swap)
    (fun y : β × β' => y.swap) (fun z : γ × γ' => z.swap) (tensorProd Y X)) ?_
  funext x y z
  exact tensorProd_comm_apply X Y x y z

/-- `X ⊗ (Y ⊗ Z) ≤ₜ (X ⊗ Y) ⊗ Z`. -/
theorem tensorProd_assoc_le (X : Tensor3 R α β γ) (Y : Tensor3 R α' β' γ')
    (Z : Tensor3 R α'' β'' γ'') :
    tensorProd X (tensorProd Y Z) ≤ₜ tensorProd (tensorProd X Y) Z := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : α × (α' × α'') => ((x.1, x.2.1), x.2.2))
    (fun y : β × (β' × β'') => ((y.1, y.2.1), y.2.2))
    (fun z : γ × (γ' × γ'') => ((z.1, z.2.1), z.2.2))
    (tensorProd (tensorProd X Y) Z)) ?_
  funext x y z
  obtain ⟨a, a', a''⟩ := x; obtain ⟨b, b', b''⟩ := y; obtain ⟨c, c', c''⟩ := z
  simp only [tensorProd]
  ring

/-- `(X ⊗ Y) ⊗ Z ≤ₜ X ⊗ (Y ⊗ Z)`. -/
theorem tensorProd_assoc_le' (X : Tensor3 R α β γ) (Y : Tensor3 R α' β' γ')
    (Z : Tensor3 R α'' β'' γ'') :
    tensorProd (tensorProd X Y) Z ≤ₜ tensorProd X (tensorProd Y Z) := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : (α × α') × α'' => (x.1.1, (x.1.2, x.2)))
    (fun y : (β × β') × β'' => (y.1.1, (y.1.2, y.2)))
    (fun z : (γ × γ') × γ'' => (z.1.1, (z.1.2, z.2)))
    (tensorProd X (tensorProd Y Z))) ?_
  funext x y z
  obtain ⟨⟨a, a'⟩, a''⟩ := x; obtain ⟨⟨b, b'⟩, b''⟩ := y; obtain ⟨⟨c, c'⟩, c''⟩ := z
  simp only [tensorProd]
  ac_rfl

/-- Swapping the last two factors of a triple tensor product. -/
theorem tensorProd_swap23_le (X : Tensor3 R α β γ) (Y : Tensor3 R α' β' γ')
    (Z : Tensor3 R α'' β'' γ'') :
    tensorProd (tensorProd X Z) Y ≤ₜ tensorProd (tensorProd X Y) Z :=
  Tensor3.Restricts.trans (tensorProd_assoc_le' X Z Y)
    (Tensor3.Restricts.trans
      (OmegaBound.Restricts.tensorProd_left (tensorProd_comm_le Z Y) X)
      (tensorProd_assoc_le X Y Z))

/-- Block-diagonal sums commute with tensoring on the left. -/
theorem blockDiag_tensorProd_le' (m : ℕ) (S : Tensor3 R α β γ) (U : Tensor3 R α' β' γ') :
    blockDiag (Fin m) (tensorProd U S) ≤ₜ tensorProd U (blockDiag (Fin m) S) := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : Fin m × (α' × α) => (x.2.1, (x.1, x.2.2)))
    (fun y : Fin m × (β' × β) => (y.2.1, (y.1, y.2.2)))
    (fun z : Fin m × (γ' × γ) => (z.2.1, (z.1, z.2.2)))
    (tensorProd U (blockDiag (Fin m) S))) ?_
  funext x y z
  obtain ⟨t, a', a⟩ := x; obtain ⟨t', b', b⟩ := y; obtain ⟨t'', c', c⟩ := z
  simp only [blockDiag_apply, tensorProd]
  by_cases h : t = t' ∧ t = t''
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

end Plumbing

/-! ## `⟨a,b,c⟩^{⊗k}` inside `tpow` -/

theorem matMul_le_tpow (a b c : ℕ) :
    ∀ k : ℕ, Tensor3.matMul (R := R) (a ^ k) (b ^ k) (c ^ k)
      ≤ₜ tpow (Tensor3.matMul (R := R) a b c) k := by
  intro k
  induction k with
  | zero =>
      refine Restricts.of_eq (precomp_restricts
        (fun _ => (PUnit.unit : TIdx (Fin a × Fin b) 0))
        (fun _ => (PUnit.unit : TIdx (Fin b × Fin c) 0))
        (fun _ => (PUnit.unit : TIdx (Fin c × Fin a) 0))
        (tpow (Tensor3.matMul (R := R) a b c) 0)) ?_
      funext x y z
      exact matMul_one_apply x y z
  | succ k ih =>
      refine Tensor3.Restricts.trans ?_
        (OmegaBound.Restricts.tensorProd_right ih (Tensor3.matMul (R := R) a b c))
      exact matMul_congr_le (matMul_restricts_tensorProd (a ^ k) (b ^ k) (c ^ k) a b c)
        (by ring) (by ring) (by ring)

/-! ## The `s`-fold direct sum -/

/-- Index type of the `s`-fold direct sum, right-nested so that no `Σ`-types appear. -/
def mmIdxSum (a b : ℕ → ℕ) : ℕ → Type
  | 0 => Empty
  | s + 1 => (Fin (a s) × Fin (b s)) ⊕ mmIdxSum a b s

instance mmIdxSum.instFintype (a b : ℕ → ℕ) (s : ℕ) : Fintype (mmIdxSum a b s) := by
  induction s with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ s ih => exact inferInstanceAs (Fintype ((Fin (a s) × Fin (b s)) ⊕ mmIdxSum a b s))

instance mmIdxSum.instDecidableEq (a b : ℕ → ℕ) (s : ℕ) : DecidableEq (mmIdxSum a b s) := by
  induction s with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ s ih => exact inferInstanceAs (DecidableEq ((Fin (a s) × Fin (b s)) ⊕ mmIdxSum a b s))


/-- The multiplicity of a type, as an iterated binomial coefficient.  This is the
multinomial coefficient `N! / ∏ mᵢ!`, written so that the recursion it satisfies is
definitional. -/
def mmult (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | s + 1 => (∑ i ∈ Finset.range (s + 1), m i).choose (m s) * mmult m s

theorem mmult_congr {m m' : ℕ → ℕ} :
    ∀ (s : ℕ), (∀ i, i < s → m i = m' i) → mmult m s = mmult m' s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
      intro h
      have hsum : (∑ i ∈ Finset.range (s + 1), m i) = ∑ i ∈ Finset.range (s + 1), m' i :=
        Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)
      show (∑ i ∈ Finset.range (s + 1), m i).choose (m s) * mmult m s = _
      rw [hsum, h s (by omega), ih (fun i hi => h i (by omega))]
      rfl


theorem one_le_mmult (m : ℕ → ℕ) : ∀ s : ℕ, 1 ≤ mmult m s := by
  intro s
  induction s with
  | zero => exact le_refl 1
  | succ s ih =>
      have h1 : 1 ≤ (∑ i ∈ Finset.range (s + 1), m i).choose (m s) :=
        Nat.choose_pos (by rw [Finset.sum_range_succ]; omega)
      show 1 ≤ (∑ i ∈ Finset.range (s + 1), m i).choose (m s) * mmult m s
      calc 1 = 1 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul h1 ih

/-! ## The counting step -/

/-- **One type carries a `1/(N+1)^s` fraction of the total weight.** -/
theorem exists_dominant_type_gen (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ∀ (s N : ℕ), ∃ m : ℕ → ℕ, (∑ i ∈ Finset.range (s + 1), m i) = N ∧
      (∑ i ∈ Finset.range (s + 1), q i) ^ N / (((N : ℝ) + 1) ^ (s + 1))
        ≤ (mmult m (s + 1) : ℝ) * ∏ i ∈ Finset.range (s + 1), q i ^ m i := by
  intro s
  induction s with
  | zero =>
      intro N
      refine ⟨fun _ => N, by norm_num, ?_⟩
      have hm : mmult (fun _ => N) 1 = 1 := by
        show (∑ i ∈ Finset.range 1, (fun _ => N) i).choose N * mmult (fun _ => N) 0 = 1
        rw [show mmult (fun _ => N) 0 = 1 from rfl]
        simp
      have hqp : (0 : ℝ) ≤ q 0 ^ N := pow_nonneg (hq 0) N
      have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      show (∑ i ∈ Finset.range 1, q i) ^ N / (((N : ℝ) + 1) ^ 1)
          ≤ (mmult (fun _ => N) 1 : ℝ) * ∏ i ∈ Finset.range 1, q i ^ (N : ℕ)
      rw [hm]
      simp only [Finset.sum_range_one, Finset.prod_range_one, pow_one, Nat.cast_one, one_mul]
      exact div_le_self hqp hN1
  | succ s ih =>
      intro N
      set Q : ℝ := ∑ i ∈ Finset.range (s + 1), q i with hQ
      have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => hq i
      obtain ⟨k, hkN, hk⟩ := exists_dominant_type (q (s + 1)) Q (hq _) hQ0 N
      obtain ⟨m', hm'sum, hm'⟩ := ih (N - k)
      refine ⟨Function.update m' (s + 1) k, ?_, ?_⟩
      · rw [Finset.sum_range_succ]
        have hlow : ∀ i ∈ Finset.range (s + 1), Function.update m' (s + 1) k i = m' i := by
          intro i hi
          have hlt : i < s + 1 := Finset.mem_range.mp hi
          exact Function.update_of_ne (by omega) _ _
        rw [Finset.sum_congr rfl hlow, hm'sum, Function.update_self]
        omega
      · -- rewrite the multiplicity and the product
        have hlow : ∀ i ∈ Finset.range (s + 1), Function.update m' (s + 1) k i = m' i := by
          intro i hi
          have hlt : i < s + 1 := Finset.mem_range.mp hi
          exact Function.update_of_ne (by omega) _ _
        have hsum1 : (∑ i ∈ Finset.range (s + 1), Function.update m' (s + 1) k i) = N - k := by
          rw [Finset.sum_congr rfl hlow, hm'sum]
        have hsumtot : (∑ i ∈ Finset.range (s + 2), Function.update m' (s + 1) k i) = N := by
          rw [Finset.sum_range_succ, hsum1, Function.update_self]; omega
        have hmm : mmult (Function.update m' (s + 1) k) (s + 2)
            = N.choose k * mmult m' (s + 1) := by
          show (∑ i ∈ Finset.range (s + 2), Function.update m' (s + 1) k i).choose
              (Function.update m' (s + 1) k (s + 1))
              * mmult (Function.update m' (s + 1) k) (s + 1) = _
          rw [hsumtot, Function.update_self,
            mmult_congr (s + 1) (fun i hi => hlow i (Finset.mem_range.mpr hi))]
        have hprod : (∏ i ∈ Finset.range (s + 2), q i ^ Function.update m' (s + 1) k i)
            = (∏ i ∈ Finset.range (s + 1), q i ^ m' i) * q (s + 1) ^ k := by
          rw [Finset.prod_range_succ, Function.update_self]
          congr 1
          exact Finset.prod_congr rfl fun i hi => by rw [hlow i hi]
        rw [hmm, hprod]
        push_cast
        -- numeric chaining
        have hPnn : (0 : ℝ) ≤ ∏ i ∈ Finset.range (s + 1), q i ^ m' i :=
          Finset.prod_nonneg fun i _ => pow_nonneg (hq i) _
        have hqk : (0 : ℝ) ≤ q (s + 1) ^ k := pow_nonneg (hq _) k
        have hch : (0 : ℝ) ≤ (N.choose k : ℝ) := by positivity
        have hstep1 : Q ^ (N - k) / (((N : ℝ) + 1) ^ (s + 1))
            ≤ (mmult m' (s + 1) : ℝ) * ∏ i ∈ Finset.range (s + 1), q i ^ m' i := by
          refine le_trans ?_ hm'
          have hle : ((((N - k : ℕ) : ℝ)) + 1) ^ (s + 1) ≤ (((N : ℝ)) + 1) ^ (s + 1) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            have : ((N - k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N k
            linarith
          have hQpow : (0 : ℝ) ≤ Q ^ (N - k) := pow_nonneg hQ0 _
          have hpos1 : (0 : ℝ) < ((((N - k : ℕ) : ℝ)) + 1) ^ (s + 1) := by positivity
          have hpos2 : (0 : ℝ) < (((N : ℝ)) + 1) ^ (s + 1) := by positivity
          rw [div_le_div_iff₀ hpos2 hpos1]
          exact mul_le_mul_of_nonneg_left hle hQpow
        have hdivmono : ∀ x y : ℝ, x ≤ y →
            x / (((N : ℝ) + 1) ^ (s + 1)) ≤ y / (((N : ℝ) + 1) ^ (s + 1)) := by
          intro x y hxy
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hxy (by positivity)
        have hkey : (q (s + 1) + Q) ^ N / ((N : ℝ) + 1) / (((N : ℝ) + 1) ^ (s + 1))
            ≤ (N.choose k : ℝ) * (q (s + 1) ^ k * Q ^ (N - k)) / (((N : ℝ) + 1) ^ (s + 1)) :=
          hdivmono _ _ hk
        have hfinal : (N.choose k : ℝ) * (q (s + 1) ^ k * Q ^ (N - k)) / (((N : ℝ) + 1) ^ (s + 1))
            ≤ (N.choose k : ℝ) * mmult m' (s + 1)
              * ((∏ i ∈ Finset.range (s + 1), q i ^ m' i) * q (s + 1) ^ k) := by
          have h1 : (N.choose k : ℝ) * (q (s + 1) ^ k * Q ^ (N - k)) / (((N : ℝ) + 1) ^ (s + 1))
              = (N.choose k : ℝ) * q (s + 1) ^ k * (Q ^ (N - k) / (((N : ℝ) + 1) ^ (s + 1))) := by
            field_simp
          rw [h1]
          have h2 : (0 : ℝ) ≤ (N.choose k : ℝ) * q (s + 1) ^ k := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hstep1 h2, hPnn, hqk, hch]
        have hsplit : (∑ i ∈ Finset.range (s + 2), q i) = q (s + 1) + Q := by
          rw [Finset.sum_range_succ, hQ]; ring
        rw [hsplit]
        have hexp : (q (s + 1) + Q) ^ N / (((N : ℝ) + 1) ^ (s + 2))
            = (q (s + 1) + Q) ^ N / ((N : ℝ) + 1) / (((N : ℝ) + 1) ^ (s + 1)) := by
          have hpp : (((N : ℝ) + 1)) ^ (s + 2) = ((N : ℝ) + 1) * (((N : ℝ) + 1)) ^ (s + 1) := by
            ring
          rw [div_div, hpp]
        rw [hexp]
        exact le_trans hkey hfinal

end OmegaBound
