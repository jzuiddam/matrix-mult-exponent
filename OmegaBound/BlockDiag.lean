import OmegaBound.Rank
import OmegaBound.Monotonicity
import OmegaBound.Rectangular

/-!
# Block-diagonal sums of a tensor

`blockDiag ι S` is the direct sum of `|ι|` copies of `S`, realised concretely on product
index sets rather than iterated `Sum` types: the bookkeeping device for "many disjoint copies"
of one tensor.

## Main results

* `blockDiag_eq_tensorProd` — `blockDiag (Fin m) S = I_m ⊗ S`
* `blockDiag_le_of_injective` — more blocks is a stronger tensor
* `blockDiag_add_le` — `blockDiag (Fin (m+n)) S ≤ₜ blockDiag (Fin m) S ⊕ₜ blockDiag (Fin n) S`
* `blockDiag_mul_le` — `blockDiag (Fin (m*n)) S ≤ₜ blockDiag (Fin m) (blockDiag (Fin n) S)`
* `blockDiag_tensorProd_le` — `blockDiag ι (S ⊗ U) ≤ₜ blockDiag ι S ⊗ U`
* `RankLE.blockDiag` — `R(blockDiag (Fin m) S) ≤ m · R(S)`
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {ι κ α β γ α' β' γ' α'' β'' γ'' : Type*}

/-- The `ι`-fold block-diagonal sum of `S`: `|ι|` disjoint copies of `S`. -/
def blockDiag (ι : Type*) [DecidableEq ι] (S : Tensor3 R α β γ) :
    Tensor3 R (ι × α) (ι × β) (ι × γ) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then S x.2 y.2 z.2 else 0

@[simp] theorem blockDiag_apply [DecidableEq ι] (S : Tensor3 R α β γ)
    (t t' t'' : ι) (x : α) (y : β) (z : γ) :
    blockDiag ι S (t, x) (t', y) (t'', z) = if t = t' ∧ t = t'' then S x y z else 0 := rfl

/-! ## Basic identifications -/

/-- `blockDiag (Fin m) S` is literally `I_m ⊗ S`. -/
theorem blockDiag_eq_tensorProd (m : ℕ) (S : Tensor3 R α β γ) :
    blockDiag (Fin m) S = tensorProd (identity R m) S := by
  funext x y z
  obtain ⟨t, a⟩ := x; obtain ⟨t', b⟩ := y; obtain ⟨t'', c⟩ := z
  simp only [blockDiag_apply, tensorProd, identity]
  by_cases h : t = t' ∧ t = t''
  · obtain ⟨h1, h2⟩ := h
    rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h1 ▸ h2⟩, one_mul]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.1, hh.1.trans hh.2⟩), zero_mul]

/-- A single block is a restriction of any nonempty block-diagonal sum. -/
theorem restricts_blockDiag [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) (t : ι) : S ≤ₜ blockDiag ι S := by
  refine Restricts.of_eq (precomp_restricts (fun a : α => (t, a)) (fun b : β => (t, b))
    (fun c : γ => (t, c)) (blockDiag ι S)) ?_
  funext a b c
  simp [blockDiag]

/-! ## Monotonicity -/

/-- Block-diagonal sums are monotone in the block. -/
theorem blockDiag_mono (m : ℕ)
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    {S : Tensor3 R α' β' γ'} {T : Tensor3 R α β γ} (h : S ≤ₜ T) :
    blockDiag (Fin m) S ≤ₜ blockDiag (Fin m) T := by
  rw [blockDiag_eq_tensorProd, blockDiag_eq_tensorProd]
  exact OmegaBound.Restricts.tensorProd_left h (identity R m)

/-- Fewer blocks restrict from more blocks. -/
theorem blockDiag_le_of_injective [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) {f : ι → κ} (hf : Function.Injective f) :
    blockDiag ι S ≤ₜ blockDiag κ S := by
  refine Restricts.of_eq (precomp_restricts (fun x : ι × α => (f x.1, x.2))
    (fun y : ι × β => (f y.1, y.2)) (fun z : ι × γ => (f z.1, z.2)) (blockDiag κ S)) ?_
  funext x y z
  obtain ⟨t, a⟩ := x; obtain ⟨t', b⟩ := y; obtain ⟨t'', c⟩ := z
  simp only [blockDiag_apply]
  by_cases h : t = t' ∧ t = t''
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg (fun hh => h ⟨hf hh.1, hf hh.2⟩)]

/-- Relabelling the block index set. -/
theorem blockDiag_congr [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) (e : ι ≃ κ) : blockDiag ι S ≤ₜ blockDiag κ S :=
  blockDiag_le_of_injective S e.injective

/-! ## Splitting and nesting -/

/-- Splitting the blocks into two groups. -/
theorem blockDiag_sum_le [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) :
    blockDiag (ι ⊕ κ) S ≤ₜ (blockDiag ι S ⊕ₜ blockDiag κ S) := by
  classical
  refine Restricts.of_eq (precomp_restricts
    (fun x : (ι ⊕ κ) × α => match x with
      | (.inl t, a) => Sum.inl (t, a) | (.inr t, a) => Sum.inr (t, a))
    (fun y : (ι ⊕ κ) × β => match y with
      | (.inl t, b) => Sum.inl (t, b) | (.inr t, b) => Sum.inr (t, b))
    (fun z : (ι ⊕ κ) × γ => match z with
      | (.inl t, c) => Sum.inl (t, c) | (.inr t, c) => Sum.inr (t, c))
    (blockDiag ι S ⊕ₜ blockDiag κ S)) ?_
  funext x y z
  obtain ⟨t, a⟩ := x; obtain ⟨t', b⟩ := y; obtain ⟨t'', c⟩ := z
  cases t <;> cases t' <;> cases t'' <;>
    simp [blockDiag, directSum, Sum.inl.injEq, Sum.inr.injEq]

/-- `m + n` blocks split as `m` blocks plus `n` blocks. -/
theorem blockDiag_add_le [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) (m n : ℕ) :
    blockDiag (Fin (m + n)) S ≤ₜ (blockDiag (Fin m) S ⊕ₜ blockDiag (Fin n) S) :=
  Tensor3.Restricts.trans (blockDiag_congr S (finSumFinEquiv (m := m) (n := n)).symm)
    (blockDiag_sum_le S)

/-- Nested block-diagonal sums. -/
theorem blockDiag_prod_le [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) :
    blockDiag (ι × κ) S ≤ₜ blockDiag ι (blockDiag κ S) := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : (ι × κ) × α => (x.1.1, (x.1.2, x.2)))
    (fun y : (ι × κ) × β => (y.1.1, (y.1.2, y.2)))
    (fun z : (ι × κ) × γ => (z.1.1, (z.1.2, z.2)))
    (blockDiag ι (blockDiag κ S))) ?_
  funext x y z
  obtain ⟨⟨t, u⟩, a⟩ := x; obtain ⟨⟨t', u'⟩, b⟩ := y; obtain ⟨⟨t'', u''⟩, c⟩ := z
  simp only [blockDiag_apply, Prod.mk.injEq]
  by_cases h1 : t = t' ∧ t = t''
  · rw [if_pos h1]
    by_cases h2 : u = u' ∧ u = u''
    · rw [if_pos h2, if_pos ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩]
    · rw [if_neg h2, if_neg (fun hh => h2 ⟨hh.1.2, hh.2.2⟩)]
  · rw [if_neg h1, if_neg (fun hh => h1 ⟨hh.1.1, hh.2.1⟩)]

/-- `m * n` blocks regroup as `m` groups of `n`. -/
theorem blockDiag_mul_le [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Tensor3 R α β γ) (m n : ℕ) :
    blockDiag (Fin (m * n)) S ≤ₜ blockDiag (Fin m) (blockDiag (Fin n) S) :=
  Tensor3.Restricts.trans
    (blockDiag_congr S (finProdFinEquiv (m := m) (n := n)).symm) (blockDiag_prod_le S)

/-! ## Interaction with tensor products and direct sums -/

/-- Block-diagonal sums commute with tensoring on the right. -/
theorem blockDiag_tensorProd_le [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    (S : Tensor3 R α β γ) (U : Tensor3 R α' β' γ') :
    blockDiag ι (tensorProd S U) ≤ₜ tensorProd (blockDiag ι S) U := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : ι × (α × α') => ((x.1, x.2.1), x.2.2))
    (fun y : ι × (β × β') => ((y.1, y.2.1), y.2.2))
    (fun z : ι × (γ × γ') => ((z.1, z.2.1), z.2.2))
    (tensorProd (blockDiag ι S) U)) ?_
  funext x y z
  obtain ⟨t, a, a'⟩ := x; obtain ⟨t', b, b'⟩ := y; obtain ⟨t'', c, c'⟩ := z
  simp only [blockDiag_apply, tensorProd]
  by_cases h : t = t' ∧ t = t''
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]


/-! ## Rank of a block-diagonal sum -/

/-- Restriction is reflexive. -/
theorem Restricts.reflBD [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Tensor3 R α β γ) : T ≤ₜ T :=
  precomp_restricts id id id T

theorem rankLE_identity (m : ℕ) : RankLE (identity R m) m := Restricts.reflBD _

/-- **Rank is subadditive over blocks**: `R(m ⋅ S) ≤ m · R(S)`. -/
theorem RankLE.blockDiag [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {S : Tensor3 R α β γ} {s : ℕ} (h : RankLE S s) (m : ℕ) :
    RankLE (blockDiag (Fin m) S) (m * s) := by
  rw [blockDiag_eq_tensorProd]
  exact (rankLE_identity m).tensorProd h

/-- The empty block-diagonal sum restricts from anything. -/
theorem blockDiag_empty_le [IsEmpty ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype α'] [Fintype β'] [Fintype γ']
    (S : Tensor3 R α β γ) (T : Tensor3 R α' β' γ') : blockDiag ι S ≤ₜ T := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  funext x y z
  exact (IsEmpty.false x.1).elim

/-! ## Direct sum helpers -/

/-- Direct sum is commutative up to relabelling. -/
theorem directSumCommLe
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    (S : Tensor3 R α β γ) (U : Tensor3 R α' β' γ') : (S ⊕ₜ U) ≤ₜ (U ⊕ₜ S) := by
  refine Restricts.of_eq (precomp_restricts (fun x : α ⊕ α' => x.swap)
    (fun y : β ⊕ β' => y.swap) (fun z : γ ⊕ γ' => z.swap) (U ⊕ₜ S)) ?_
  funext x y z
  rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;> rfl

/-- Direct sum is monotone in the second argument. -/
theorem Restricts.directSumLeft
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    [Fintype α''] [Fintype β''] [Fintype γ''] [DecidableEq α''] [DecidableEq β''] [DecidableEq γ'']
    {S : Tensor3 R α' β' γ'} {T : Tensor3 R α β γ} {U : Tensor3 R α'' β'' γ''}
    (h : S ≤ₜ T) : (U ⊕ₜ S) ≤ₜ (U ⊕ₜ T) :=
  Tensor3.Restricts.trans (directSumCommLe U S)
    (Tensor3.Restricts.trans (OmegaBound.Restricts.directSum_right h) (directSumCommLe T U))

/-- Direct sum is monotone in both arguments. -/
theorem Restricts.directSum
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    {α₁ β₁ γ₁ α₂ β₂ γ₂ : Type*}
    [Fintype α₂] [Fintype β₂] [Fintype γ₂] [DecidableEq α₂] [DecidableEq β₂] [DecidableEq γ₂]
    {S : Tensor3 R α₁ β₁ γ₁} {T : Tensor3 R α β γ}
    {S' : Tensor3 R α₂ β₂ γ₂} {T' : Tensor3 R α' β' γ'}
    (h : S ≤ₜ T) (h' : S' ≤ₜ T') : (S ⊕ₜ S') ≤ₜ (T ⊕ₜ T') :=
  Tensor3.Restricts.trans (OmegaBound.Restricts.directSum_right h)
    (OmegaBound.Restricts.directSumLeft h')

/-- Tensor products distribute over direct sums in the right factor. -/
theorem tensorProd_directSum_le
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α'] [Fintype β'] [Fintype γ'] [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    [Fintype α''] [Fintype β''] [Fintype γ'']
    [DecidableEq α''] [DecidableEq β''] [DecidableEq γ'']
    (U : Tensor3 R α'' β'' γ'') (S : Tensor3 R α β γ) (S' : Tensor3 R α' β' γ') :
    (tensorProd U S ⊕ₜ tensorProd U S') ≤ₜ tensorProd U (S ⊕ₜ S') := by
  refine Restricts.of_eq (precomp_restricts
    (fun x : (α'' × α) ⊕ (α'' × α') => match x with
      | .inl (u, a) => (u, Sum.inl a) | .inr (u, a) => (u, Sum.inr a))
    (fun y : (β'' × β) ⊕ (β'' × β') => match y with
      | .inl (u, b) => (u, Sum.inl b) | .inr (u, b) => (u, Sum.inr b))
    (fun z : (γ'' × γ) ⊕ (γ'' × γ') => match z with
      | .inl (u, c) => (u, Sum.inl c) | .inr (u, c) => (u, Sum.inr c))
    (tensorProd U (S ⊕ₜ S'))) ?_
  funext x y z
  rcases x with ⟨u, a⟩ | ⟨u, a⟩ <;> rcases y with ⟨v, b⟩ | ⟨v, b⟩ <;>
    rcases z with ⟨w, c⟩ | ⟨w, c⟩ <;> simp [tensorProd, directSum]

end OmegaBound
