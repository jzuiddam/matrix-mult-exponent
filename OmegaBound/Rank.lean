import OmegaBound.TensorProduct
import OmegaBound.ZeroPadding
import OmegaBound.Tensor.Identity

/-!
# Tensor rank, submultiplicativity, and powers of the matrix multiplication tensor

This module builds the algebraic input to a bound on the matrix multiplication
exponent `ω`:

* `RankLE T r` — the tensor `T` has rank at most `r`, i.e. `T ≤ₜ identity R r`;
* `RankLE.tensorProd` — rank is submultiplicative under `⊗`;
* `matMul_tensorProd_apply` — `⟨a,b,c⟩ ⊗ ⟨a',b',c'⟩ ≅ ⟨aa',bb',cc'⟩`;
* `RankLE.matMul_pow` — `R(⟨a,a,a⟩) ≤ r` implies `R(⟨aᵏ,aᵏ,aᵏ⟩) ≤ rᵏ`.

The analytic half (the definition of `ω` and the limit) is in `OmegaBound.Omega`.
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-! ## Precomposition of index sets -/

/-- Precomposing a tensor with maps on its index sets is a restriction.  This is the
workhorse for every "these two tensors agree up to relabelling" step below. -/
theorem precomp_restricts [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f₁ : α' → α) (f₂ : β' → β) (f₃ : γ' → γ) (T : Tensor3 R α β γ) :
    (fun a b c => T (f₁ a) (f₂ b) (f₃ c)) ≤ₜ T := by
  refine ⟨fun a' x => if f₁ a' = x then 1 else 0,
          fun b' y => if f₂ b' = y then 1 else 0,
          fun c' z => if f₃ c' = z then 1 else 0, ?_⟩
  funext a b c
  exact (act_delta f₁ f₂ f₃ T a b c).symm

/-- Restriction is invariant under rewriting the restricted tensor. -/
theorem Restricts.of_eq [Fintype α] [Fintype β] [Fintype γ]
    {S S' : Tensor3 R α' β' γ'} {T : Tensor3 R α β γ}
    (h : S ≤ₜ T) (he : S' = S) : S' ≤ₜ T := by rw [he]; exact h

/-! ## Rank -/

/-- `RankLE T r` says the tensor `T` has rank at most `r`: it is a restriction of the
`r`-dimensional identity tensor, equivalently a sum of `r` rank-one tensors. -/
def RankLE (T : Tensor3 R α β γ) (r : ℕ) : Prop := T ≤ₜ identity R r

theorem RankLE.mono [Fintype α] [Fintype β] [Fintype γ]
    {S : Tensor3 R α' β' γ'} {T : Tensor3 R α β γ} {r : ℕ}
    (hST : S ≤ₜ T) (hT : RankLE T r) : RankLE S r :=
  Tensor3.Restricts.trans hST hT

/-! ### Entries of the unit tensor -/

/-- Every entry of `⟨1,1,1⟩` is `1`. -/
theorem matMul_one_apply (x y z : Fin 1 × Fin 1) :
    Tensor3.matMul (R := R) 1 1 1 x y z = 1 := by
  obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y; obtain ⟨z₁, z₂⟩ := z
  show (if _ ∧ _ ∧ _ then (1 : R) else 0) = 1
  rw [if_pos ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩]

/-! ## Tensor products -/

/-- `tensorProd` is symmetric up to swapping the index pairs. -/
theorem tensorProd_comm_apply (T : Tensor3 R α β γ) (S : Tensor3 R α' β' γ')
    (a : α × α') (b : β × β') (c : γ × γ') :
    tensorProd T S a b c = tensorProd S T a.swap b.swap c.swap := by
  obtain ⟨a₁, a₂⟩ := a; obtain ⟨b₁, b₂⟩ := b; obtain ⟨c₁, c₂⟩ := c
  simp only [tensorProd, Prod.swap_prod_mk]
  ring

/-- Monotonicity of `⊗` in the *left* argument, from the right-hand version by symmetry. -/
theorem Restricts.tensorProd_left
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype α'] [Fintype β'] [Fintype γ']
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    {α₁ β₁ γ₁ : Type*} [Fintype α₁] [Fintype β₁] [Fintype γ₁]
    [DecidableEq α₁] [DecidableEq β₁] [DecidableEq γ₁]
    {S : Tensor3 R α₁ β₁ γ₁} {T : Tensor3 R α β γ}
    (h : S ≤ₜ T) (U : Tensor3 R α' β' γ') :
    tensorProd U S ≤ₜ tensorProd U T := by
  have hswap := OmegaBound.Restricts.tensorProd_right h U
  refine Tensor3.Restricts.trans (Restricts.of_eq (precomp_restricts
      (fun p : α' × α₁ => p.swap) (fun p : β' × β₁ => p.swap)
      (fun p : γ' × γ₁ => p.swap) (tensorProd S U)) ?_) ?_
  · funext a b c; exact tensorProd_comm_apply U S a b c
  · refine Tensor3.Restricts.trans hswap (Restricts.of_eq (precomp_restricts
      (fun p : α × α' => p.swap) (fun p : β × β' => p.swap)
      (fun p : γ × γ' => p.swap) (tensorProd U T)) ?_)
    funext a b c
    exact tensorProd_comm_apply T U a b c

/-! ### `I_r ⊗ I_s ≅ I_{rs}` -/

/-- The tensor product of two identity tensors is the identity tensor of the product
size, relabelled along `finProdFinEquiv`. -/
theorem identity_tensorProd (r s : ℕ) :
    tensorProd (identity R r) (identity R s) =
      fun a b c => identity R (r * s)
        (finProdFinEquiv a) (finProdFinEquiv b) (finProdFinEquiv c) := by
  funext a b c
  obtain ⟨a₁, a₂⟩ := a; obtain ⟨b₁, b₂⟩ := b; obtain ⟨c₁, c₂⟩ := c
  simp only [tensorProd, identity, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem identity_tensorProd_rankLE (r s : ℕ) :
    RankLE (tensorProd (identity R r) (identity R s)) (r * s) :=
  Restricts.of_eq
    (precomp_restricts (fun a => finProdFinEquiv a) (fun b => finProdFinEquiv b)
      (fun c => finProdFinEquiv c) (identity R (r * s)))
    (identity_tensorProd r s)

/-- **Rank is submultiplicative under tensor product.** -/
theorem RankLE.tensorProd
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    {S : Tensor3 R α β γ} {T : Tensor3 R α' β' γ'} {r s : ℕ}
    (hS : RankLE S r) (hT : RankLE T s) :
    RankLE (OmegaBound.tensorProd S T) (r * s) :=
  Tensor3.Restricts.trans
    (Tensor3.Restricts.trans (OmegaBound.Restricts.tensorProd_right hS T)
      (OmegaBound.Restricts.tensorProd_left hT (identity R r)))
    (identity_tensorProd_rankLE r s)

/-! ### `⟨a,b,c⟩ ⊗ ⟨a',b',c'⟩ ≅ ⟨aa',bb',cc'⟩` -/

/-- The relabelling `(Fin a × Fin b) × (Fin a' × Fin b') → Fin (a*a') × Fin (b*b')`
identifying a tensor product of matrix multiplication tensors with a single one. -/
def mmIdx (a b a' b' : ℕ) :
    (Fin a × Fin b) × (Fin a' × Fin b') → Fin (a * a') × Fin (b * b') :=
  fun p => (finProdFinEquiv (p.1.1, p.2.1), finProdFinEquiv (p.1.2, p.2.2))

/-- Its inverse. -/
def mmIdxInv (a b a' b' : ℕ) :
    Fin (a * a') × Fin (b * b') → (Fin a × Fin b) × (Fin a' × Fin b') :=
  fun q =>
    (((finProdFinEquiv.symm q.1).1, (finProdFinEquiv.symm q.2).1),
     ((finProdFinEquiv.symm q.1).2, (finProdFinEquiv.symm q.2).2))

@[simp] theorem mmIdx_mmIdxInv (a b a' b' : ℕ) (q : Fin (a * a') × Fin (b * b')) :
    mmIdx a b a' b' (mmIdxInv a b a' b' q) = q := by
  obtain ⟨u, v⟩ := q
  have h1 : ((finProdFinEquiv.symm u).1, (finProdFinEquiv.symm u).2)
      = finProdFinEquiv.symm u := rfl
  have h2 : ((finProdFinEquiv.symm v).1, (finProdFinEquiv.symm v).2)
      = finProdFinEquiv.symm v := rfl
  simp only [mmIdx, mmIdxInv, h1, h2, Equiv.apply_symm_apply]

/-- **Multiplicativity of the matrix multiplication tensor**, pointwise. -/
theorem matMul_tensorProd_apply (a b c a' b' c' : ℕ)
    (x : (Fin a × Fin b) × (Fin a' × Fin b'))
    (y : (Fin b × Fin c) × (Fin b' × Fin c'))
    (z : (Fin c × Fin a) × (Fin c' × Fin a')) :
    tensorProd (Tensor3.matMul (R := R) a b c) (Tensor3.matMul (R := R) a' b' c') x y z =
      Tensor3.matMul (R := R) (a * a') (b * b') (c * c')
        (mmIdx a b a' b' x) (mmIdx b c b' c' y) (mmIdx c a c' a' z) := by
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := x
  obtain ⟨⟨j₂, k⟩, ⟨j₂', k'⟩⟩ := y
  obtain ⟨⟨k₂, i₂⟩, ⟨k₂', i₂'⟩⟩ := z
  simp only [tensorProd, Tensor3.matMul, mmIdx,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- `⟨aa',bb',cc'⟩` is a restriction of `⟨a,b,c⟩ ⊗ ⟨a',b',c'⟩`.  This is the direction
needed to push a rank bound up a tensor power. -/
theorem matMul_restricts_tensorProd (a b c a' b' c' : ℕ) :
    Tensor3.matMul (R := R) (a * a') (b * b') (c * c') ≤ₜ
      tensorProd (Tensor3.matMul (R := R) a b c) (Tensor3.matMul (R := R) a' b' c') := by
  refine Restricts.of_eq (precomp_restricts (mmIdxInv a b a' b') (mmIdxInv b c b' c')
    (mmIdxInv c a c' a')
    (tensorProd (Tensor3.matMul (R := R) a b c) (Tensor3.matMul (R := R) a' b' c'))) ?_
  funext x y z
  rw [matMul_tensorProd_apply, mmIdx_mmIdxInv, mmIdx_mmIdxInv, mmIdx_mmIdxInv]

/-! ## Powers -/

/-- `⟨1,1,1⟩` has rank one. -/
theorem rankLE_matMul_one : RankLE (Tensor3.matMul (R := R) 1 1 1) 1 := by
  refine Restricts.of_eq (precomp_restricts
    (fun _ : Fin 1 × Fin 1 => (0 : Fin 1)) (fun _ : Fin 1 × Fin 1 => (0 : Fin 1))
    (fun _ : Fin 1 × Fin 1 => (0 : Fin 1)) (identity R 1)) ?_
  funext x y z
  obtain ⟨i, j⟩ := x; obtain ⟨j', k⟩ := y; obtain ⟨k', i'⟩ := z
  simp [identity, Tensor3.matMul, Subsingleton.elim i i', Subsingleton.elim j j',
    Subsingleton.elim k k']

/-- **The power rule.** If `⟨a,a,a⟩` has rank at most `r`, then `⟨aᵏ,aᵏ,aᵏ⟩` has rank
at most `rᵏ`. -/
theorem RankLE.matMul_pow {a r : ℕ} (h : RankLE (Tensor3.matMul (R := R) a a a) r) :
    ∀ k : ℕ, RankLE (Tensor3.matMul (R := R) (a ^ k) (a ^ k) (a ^ k)) (r ^ k) := by
  intro k
  induction k with
  | zero => simpa using rankLE_matMul_one (R := R)
  | succ k ih =>
      have hstep :
          RankLE (OmegaBound.tensorProd (Tensor3.matMul (R := R) (a ^ k) (a ^ k) (a ^ k))
            (Tensor3.matMul (R := R) a a a)) (r ^ k * r) := ih.tensorProd h
      have hres :
          Tensor3.matMul (R := R) (a ^ k * a) (a ^ k * a) (a ^ k * a) ≤ₜ
            OmegaBound.tensorProd (Tensor3.matMul (R := R) (a ^ k) (a ^ k) (a ^ k))
              (Tensor3.matMul (R := R) a a a) :=
        matMul_restricts_tensorProd _ _ _ _ _ _
      have := OmegaBound.RankLE.mono hres hstep
      simpa [pow_succ] using this


/-! ## Base change along a ring homomorphism -/

section Map

variable {S : Type*} [CommSemiring S]

theorem map_act [Fintype α] [Fintype β] [Fintype γ] (f : R →+* S)
    (A₁ : α' → α → R) (A₂ : β' → β → R) (A₃ : γ' → γ → R) (T : Tensor3 R α β γ)
    (a : α') (b : β') (c : γ') :
    f (act A₁ A₂ A₃ T a b c) =
      act (fun x y => f (A₁ x y)) (fun x y => f (A₂ x y)) (fun x y => f (A₃ x y))
        (fun x y z => f (T x y z)) a b c := by
  simp only [act, map_sum, map_mul]

/-- **A rank bound for `⟨a,b,c⟩` transfers along any ring homomorphism.**  Together with
`Int.castRingHom` this promotes a decomposition with integer coefficients to one over an
arbitrary commutative ring. -/
theorem RankLE.map (f : R →+* S) {a b c r : ℕ}
    (h : RankLE (Tensor3.matMul (R := R) a b c) r) :
    RankLE (Tensor3.matMul (R := S) a b c) r := by
  obtain ⟨A₁, A₂, A₃, hT⟩ := h
  refine ⟨fun x y => f (A₁ x y), fun x y => f (A₂ x y), fun x y => f (A₃ x y), ?_⟩
  funext i j k
  have h1 : f (Tensor3.matMul (R := R) a b c i j k)
      = Tensor3.matMul (R := S) a b c i j k := by
    obtain ⟨i₁, i₂⟩ := i; obtain ⟨j₁, j₂⟩ := j; obtain ⟨k₁, k₂⟩ := k
    simp only [Tensor3.matMul, apply_ite f, map_one, map_zero]
  have h2 : (fun x y z => f (identity R r x y z)) = identity S r := by
    funext x y z
    simp only [identity, apply_ite f, map_one, map_zero]
  rw [← h1, hT, map_act, h2]

end Map

end OmegaBound
