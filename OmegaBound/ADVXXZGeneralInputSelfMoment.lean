import OmegaBound.ADVXXZGeneralInputConcentration
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The number of oriented pairs carrying `(a,b)` in one word. -/
def selfPairCount {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a b : α)
    (x : Fin n → α) : ℕ :=
  (S.filter fun i => x i = a ∧ x (e i) = b).card

private theorem self_typeCnt_comp_perm {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (x : Fin n → α) (e : Equiv.Perm (Fin n))
    (a : α) : typeCnt (fun i => x (e i)) a = typeCnt x a := by
  unfold typeCnt
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa using hi
  · intro i₁ _ i₂ _ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa using hj

private def selfWordPerm {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {k : α → ℕ} (e : Equiv.Perm (Fin n)) :
    Words n k ≃ Words n k where
  toFun x := ⟨fun i => x.val (e.symm i), fun a => by
    rw [self_typeCnt_comp_perm x.val e.symm a]
    exact x.property a⟩
  invFun x := ⟨fun i => x.val (e i), fun a => by
    rw [self_typeCnt_comp_perm x.val e a]
    exact x.property a⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

private noncomputable def selfEmbeddingPerm {γ : Type*} [Fintype γ]
    {n : ℕ} (f g : γ ↪ Fin n) : Equiv.Perm (Fin n) := by
  classical
  let h : Set.range f ≃ Set.range g :=
    f.toEquivRange.symm.trans g.toEquivRange
  exact h.extendSubtype

private theorem selfEmbeddingPerm_apply {γ : Type*} [Fintype γ]
    {n : ℕ} (f g : γ ↪ Fin n) (i : γ) :
    selfEmbeddingPerm f g (f i) = g i := by
  classical
  unfold selfEmbeddingPerm
  rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self i)]
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_symm_apply_self,
    Function.Embedding.toEquivRange_apply, Subtype.coe_mk]

private def pairPattern {α : Type*} {r : ℕ} (a b : α) :
    Fin r ⊕ Fin r → α
  | .inl _ => a
  | .inr _ => b

private abbrev SelfPatternHit {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (k : α → ℕ) {r : ℕ} (a b : α)
    (f : (Fin r ⊕ Fin r) ↪ Fin n) :=
  {x : Words n k // ∀ i, x.val (f i) = pairPattern a b i}

private noncomputable def selfPatternHitEquiv {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} {k : α → ℕ} {r : ℕ} (a b : α)
    (f g : (Fin r ⊕ Fin r) ↪ Fin n) :
    SelfPatternHit k a b f ≃ SelfPatternHit k a b g := by
  classical
  let e := selfEmbeddingPerm f g
  refine (selfWordPerm e).subtypeEquiv ?_
  intro x
  constructor
  · intro hx i
    change x.val (e.symm (g i)) = pairPattern a b i
    rw [← selfEmbeddingPerm_apply f g i, e.symm_apply_apply]
    exact hx i
  · intro hx i
    have hi := hx i
    change x.val (e.symm (g i)) = pairPattern a b i at hi
    rw [← selfEmbeddingPerm_apply f g i, e.symm_apply_apply] at hi
    exact hi

private abbrev SelfPatternEmbedding {α : Type*} [DecidableEq α]
    {n : ℕ} (x : Fin n → α) {r : ℕ} (a b : α) :=
  {f : (Fin r ⊕ Fin r) ↪ Fin n //
    ∀ i, x (f i) = pairPattern a b i}

private def selfPatternHitSigmaEquiv {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (k : α → ℕ) (a b : α) :
    (Σ f : (Fin r ⊕ Fin r) ↪ Fin n, SelfPatternHit k a b f) ≃
      (Σ x : Words n k, SelfPatternEmbedding (r := r) x.val a b) where
  toFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  invFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl

private abbrev SelfValueEmbedding {α : Type*} [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (a : α) (γ : Type*) :=
  γ ↪ {i : Fin n // x i = a}

private def selfSamePatternEmbeddingEquiv {α : Type*} [DecidableEq α]
    {n r : ℕ} (x : Fin n → α) (a : α) :
    SelfPatternEmbedding (r := r) x a a ≃
      SelfValueEmbedding x a (Fin r ⊕ Fin r) where
  toFun f :=
    { toFun := fun i => ⟨f.val i, by
        cases i with
        | inl i => simpa [pairPattern] using f.property (.inl i)
        | inr i => simpa [pairPattern] using f.property (.inr i)⟩
      inj' := fun _ _ h => f.val.injective (Subtype.ext_iff.mp h) }
  invFun f :=
    ⟨f.trans (Function.Embedding.subtype _), fun i => by
      cases i with
      | inl i => simpa [pairPattern] using (f (.inl i)).property
      | inr i => simpa [pairPattern] using (f (.inr i)).property⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    rfl
  right_inv f := by
    ext i
    rfl

private def selfDistinctPatternEmbeddingEquiv {α : Type*} [DecidableEq α]
    {n r : ℕ} (x : Fin n → α) (a b : α) (hab : a ≠ b) :
    SelfPatternEmbedding (r := r) x a b ≃
      SelfValueEmbedding x a (Fin r) × SelfValueEmbedding x b (Fin r) where
  toFun f :=
    ({ toFun := fun i => ⟨f.val (.inl i), f.property (.inl i)⟩
       inj' := by
         intro i j h
         exact Sum.inl_injective (f.val.injective (Subtype.ext_iff.mp h)) },
     { toFun := fun i => ⟨f.val (.inr i), f.property (.inr i)⟩
       inj' := by
         intro i j h
         exact Sum.inr_injective (f.val.injective (Subtype.ext_iff.mp h)) })
  invFun f :=
    ⟨{ toFun := fun z => match z with
         | .inl i => (f.1 i).val
         | .inr i => (f.2 i).val
       inj' := by
         intro i j h
         cases i with
         | inl i =>
             cases j with
             | inl j =>
                 exact congrArg Sum.inl (f.1.injective (Subtype.ext h))
             | inr j =>
                 exfalso
                 apply hab
                 calc
                   a = x (f.1 i).val := (f.1 i).property.symm
                   _ = x (f.2 j).val := congrArg x h
                   _ = b := (f.2 j).property
         | inr i =>
             cases j with
             | inl j =>
                 exfalso
                 apply hab
                 calc
                   a = x (f.1 j).val := (f.1 j).property.symm
                   _ = x (f.2 i).val := congrArg x h.symm
                   _ = b := (f.2 i).property
             | inr j =>
                 exact congrArg Sum.inr (f.2.injective (Subtype.ext h)) },
      by
        intro i
        cases i with
        | inl i => exact (f.1 i).property
        | inr i => exact (f.2 i).property⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    cases i <;> rfl
  right_inv f := by
    rcases f with ⟨f, g⟩
    rfl

private theorem self_card_valueEmbedding {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) (γ : Type*)
    [Fintype γ] :
    Fintype.card (SelfValueEmbedding x a γ) =
      (typeCnt x a).descFactorial (Fintype.card γ) := by
  classical
  rw [Fintype.card_embedding_eq]
  congr 1
  simpa [typeCnt] using Fintype.card_subtype (fun i : Fin n => x i = a)

private theorem self_card_patternEmbedding {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} {k : α → ℕ} (x : Words n k) (a b : α) :
    Fintype.card (SelfPatternEmbedding (r := r) x.val a b) =
      if a = b then (k a).descFactorial (2*r)
      else (k a).descFactorial r * (k b).descFactorial r := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
    rw [Fintype.card_congr (selfSamePatternEmbeddingEquiv x.val a),
      self_card_valueEmbedding, x.property a]
    simpa [two_mul]
  · simp only [if_neg hab]
    rw [Fintype.card_congr (selfDistinctPatternEmbeddingEquiv x.val a b hab),
      Fintype.card_prod, self_card_valueEmbedding, self_card_valueEmbedding,
      x.property a, x.property b]
    simp

private def selfOrientedEmbedding {n r : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n))
    (hS : ∀ i ∈ S, e i ∉ S) (f : Fin r ↪ {i : Fin n // i ∈ S}) :
    (Fin r ⊕ Fin r) ↪ Fin n where
  toFun z := match z with
    | .inl i => (f i).val
    | .inr i => e (f i).val
  inj' := by
    intro i j h
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            have hij : i = j := f.injective (Subtype.ext h)
            subst j
            rfl
        | inr j =>
            exfalso
            change (f i).val = e (f j).val at h
            apply hS (f j).val (f j).property
            rw [← h]
            exact (f i).property
    | inr i =>
        cases j with
        | inl j =>
            exfalso
            change e (f i).val = (f j).val at h
            apply hS (f i).val (f i).property
            rw [h]
            exact (f j).property
        | inr j =>
            change e (f i).val = e (f j).val at h
            have hij : i = j := f.injective (Subtype.ext (e.injective h))
            subst j
            rfl

private abbrev SelfPairHitEmbedding {α : Type*} [DecidableEq α]
    {n : ℕ} (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
    (x : Fin n → α) (a b : α) (r : ℕ) :=
  {f : Fin r ↪ {i : Fin n // i ∈ S} //
    ∀ i, x (f i).val = a ∧ x (e (f i).val) = b}

private def selfPairHitEmbeddingEquiv {α : Type*} [DecidableEq α]
    {n r : ℕ} (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
    (x : Fin n → α) (a b : α) :
    SelfPairHitEmbedding S e x a b r ≃
      (Fin r ↪ {i : Fin n // i ∈ S ∧ x i = a ∧ x (e i) = b}) where
  toFun f :=
    { toFun := fun i =>
        ⟨(f.val i).val, (f.val i).property, (f.property i).1,
          (f.property i).2⟩
      inj' := by
        intro i j h
        apply f.val.injective
        apply Subtype.ext
        exact congrArg
          (fun z : {i : Fin n // i ∈ S ∧ x i = a ∧ x (e i) = b} => z.val) h }
  invFun f :=
    ⟨{ toFun := fun i => ⟨(f i).val, (f i).property.1⟩
       inj' := by
         intro i j h
         apply f.injective
         apply Subtype.ext
         exact congrArg (fun z : {i : Fin n // i ∈ S} => z.val) h },
      fun i => ⟨(f i).property.2.1, (f i).property.2.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    rfl
  right_inv f := by
    ext i
    rfl

private theorem self_card_pairHitEmbedding {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (x : Fin n → α) (a b : α) :
    Fintype.card (SelfPairHitEmbedding S e x a b r) =
      (selfPairCount S e a b x).descFactorial r := by
  classical
  rw [Fintype.card_congr (selfPairHitEmbeddingEquiv S e x a b),
    Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  unfold selfPairCount
  apply congrArg Finset.card
  ext i
  simp

private def selfPairHitSigmaEquiv {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (hS : ∀ i ∈ S, e i ∉ S)
    (k : α → ℕ) (a b : α) :
    (Σ f : Fin r ↪ {i : Fin n // i ∈ S},
      SelfPatternHit k a b (selfOrientedEmbedding S e hS f)) ≃
    (Σ x : Words n k, SelfPairHitEmbedding S e x.val a b r) where
  toFun z :=
    ⟨z.2.val, ⟨z.1, fun i =>
      ⟨z.2.property (.inl i), z.2.property (.inr i)⟩⟩⟩
  invFun z :=
    ⟨z.2.val, ⟨z.1, fun i => by
      cases i with
      | inl i => exact (z.2.property i).1
      | inr i => exact (z.2.property i).2⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl

private def selfFinEmbeddingOfLE {r n : ℕ} (h : r ≤ n) : Fin r ↪ Fin n where
  toFun i := ⟨i.val, i.isLt.trans_le h⟩
  inj' i j hij := Fin.ext
    (congrArg (fun z : Fin n => z.val) hij)

/-- Exact falling-factorial moments for a uniform type-class word on an oriented
matching.  The two endpoints of every selected edge are disjoint. -/
theorem selfPairCount_descFactorial_sum {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (hS : ∀ i ∈ S, e i ∉ S)
    (k : α → ℕ) (a b : α) :
    (∑ x : Words n k, (selfPairCount S e a b x).descFactorial r) *
        n.descFactorial (2*r) =
      Fintype.card (Words n k) * S.card.descFactorial r *
        (if a = b then (k a).descFactorial (2*r)
         else (k a).descFactorial r * (k b).descFactorial r) := by
  classical
  by_cases hrS : r ≤ S.card
  · let eS : Fin S.card ≃ {i : Fin n // i ∈ S} :=
      Fintype.equivOfCardEq (by simp [Fintype.card_coe])
    let f₀ : Fin r ↪ {i : Fin n // i ∈ S} :=
      (selfFinEmbeddingOfLE hrS).trans eS.toEmbedding
    let g₀ := selfOrientedEmbedding S e hS f₀
    have hedge :
        (∑ x : Words n k, (selfPairCount S e a b x).descFactorial r) =
          S.card.descFactorial r * Fintype.card (SelfPatternHit k a b g₀) := by
      calc
        (∑ x : Words n k, (selfPairCount S e a b x).descFactorial r) =
            ∑ x : Words n k,
              Fintype.card (SelfPairHitEmbedding S e x.val a b r) := by
                apply Finset.sum_congr rfl
                intro x _
                exact (self_card_pairHitEmbedding S e x.val a b).symm
        _ = Fintype.card
              (Σ x : Words n k, SelfPairHitEmbedding S e x.val a b r) := by
                rw [Fintype.card_sigma]
        _ = Fintype.card
              (Σ f : Fin r ↪ {i : Fin n // i ∈ S},
                SelfPatternHit k a b (selfOrientedEmbedding S e hS f)) :=
              Fintype.card_congr (selfPairHitSigmaEquiv S e hS k a b).symm
        _ = ∑ f : Fin r ↪ {i : Fin n // i ∈ S},
              Fintype.card
                (SelfPatternHit k a b (selfOrientedEmbedding S e hS f)) := by
                rw [Fintype.card_sigma]
        _ = ∑ _f : Fin r ↪ {i : Fin n // i ∈ S},
              Fintype.card (SelfPatternHit k a b g₀) := by
                apply Finset.sum_congr rfl
                intro f _
                exact Fintype.card_congr
                  (selfPatternHitEquiv a b (selfOrientedEmbedding S e hS f) g₀)
        _ = S.card.descFactorial r *
              Fintype.card (SelfPatternHit k a b g₀) := by simp
    have hall :
        n.descFactorial (2*r) * Fintype.card (SelfPatternHit k a b g₀) =
          Fintype.card (Words n k) *
            (if a = b then (k a).descFactorial (2*r)
             else (k a).descFactorial r * (k b).descFactorial r) := by
      calc
        n.descFactorial (2*r) * Fintype.card (SelfPatternHit k a b g₀) =
            Fintype.card ((Fin r ⊕ Fin r) ↪ Fin n) *
              Fintype.card (SelfPatternHit k a b g₀) := by
                simpa [two_mul]
        _ = ∑ g : (Fin r ⊕ Fin r) ↪ Fin n,
              Fintype.card (SelfPatternHit k a b g₀) := by simp
        _ = ∑ g : (Fin r ⊕ Fin r) ↪ Fin n,
              Fintype.card (SelfPatternHit k a b g) := by
                apply Finset.sum_congr rfl
                intro g _
                exact Fintype.card_congr (selfPatternHitEquiv a b g₀ g)
        _ = Fintype.card
              (Σ g : (Fin r ⊕ Fin r) ↪ Fin n, SelfPatternHit k a b g) := by
                rw [Fintype.card_sigma]
        _ = Fintype.card
              (Σ x : Words n k, SelfPatternEmbedding x.val a b) :=
              Fintype.card_congr (selfPatternHitSigmaEquiv k a b)
        _ = ∑ x : Words n k,
              Fintype.card (SelfPatternEmbedding x.val a b) := by
                rw [Fintype.card_sigma]
        _ = ∑ _x : Words n k,
              (if a = b then (k a).descFactorial (2*r)
               else (k a).descFactorial r * (k b).descFactorial r) := by
                apply Finset.sum_congr rfl
                intro x _
                exact self_card_patternEmbedding x a b
        _ = Fintype.card (Words n k) *
              (if a = b then (k a).descFactorial (2*r)
               else (k a).descFactorial r * (k b).descFactorial r) := by simp
    rw [hedge]
    calc
      (S.card.descFactorial r * Fintype.card (SelfPatternHit k a b g₀)) *
          n.descFactorial (2*r) =
        S.card.descFactorial r *
          (n.descFactorial (2*r) *
            Fintype.card (SelfPatternHit k a b g₀)) := by ring
      _ = S.card.descFactorial r *
          (Fintype.card (Words n k) *
            (if a = b then (k a).descFactorial (2*r)
             else (k a).descFactorial r * (k b).descFactorial r)) := by
            rw [hall]
      _ = Fintype.card (Words n k) * S.card.descFactorial r *
          (if a = b then (k a).descFactorial (2*r)
           else (k a).descFactorial r * (k b).descFactorial r) := by ring
  · have hrS' : S.card < r := Nat.lt_of_not_ge hrS
    have hScard : S.card.descFactorial r = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hrS'
    have hcount : ∀ x : Words n k,
        (selfPairCount S e a b x.val).descFactorial r = 0 := by
      intro x
      apply Nat.descFactorial_eq_zero_iff_lt.mpr
      exact (Finset.card_filter_le S _).trans_lt hrS'
    simp [hScard, hcount]

private theorem self_words_card_pos {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (hn : 0 < n) (k : α → ℕ)
    (hk : ∑ a, k a = n) : 0 < Fintype.card (Words n k) := by
  have hbounds := type_class_bounds n k hk
  have hleft :
      0 < Real.exp ((n : ℝ) * entropyNats (fun a => (k a : ℝ) / n)) /
        ((n : ℝ) + 1) ^ Fintype.card α := by
    positivity
  have hcardR : 0 < (Fintype.card (Words n k) : ℝ) :=
    hleft.trans_le hbounds.1
  exact_mod_cast hcardR

/-- The normalized exact falling-factorial moments of an oriented self-pair count. -/
theorem avg_selfPairCount_descFactorial {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (hn : 0 < n) (hrn : 2*r ≤ n)
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
    (hS : ∀ i ∈ S, e i ∉ S) (k : α → ℕ) (hk : ∑ a, k a = n)
    (a b : α) :
    avg (fun x : Words n k =>
      ((selfPairCount S e a b x.val).descFactorial r : ℝ)) =
      ((S.card.descFactorial r *
          (if a = b then (k a).descFactorial (2*r)
           else (k a).descFactorial r * (k b).descFactorial r) : ℕ) : ℝ) /
        n.descFactorial (2*r) := by
  have hwords := self_words_card_pos hn k hk
  have hnat := selfPairCount_descFactorial_sum (r := r) S e hS k a b
  have hreal := congrArg (fun x : ℕ => (x : ℝ)) hnat
  simp only [Nat.cast_mul, Nat.cast_sum] at hreal
  have hD : (Fintype.card (Words n k) : ℝ) ≠ 0 := by
    exact_mod_cast hwords.ne'
  have hN : (n.descFactorial (2*r) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrn))
  unfold avg
  field_simp
  simpa only [Nat.cast_mul, mul_assoc] using hreal

/-- The corrected distinct-position mean.  Equal symbols consume two copies of the
same histogram entry, while distinct symbols consume one copy of each. -/
theorem avg_selfPairCount {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (hS : ∀ i ∈ S, e i ∉ S)
    (k : α → ℕ) (hk : ∑ a, k a = n) (a b : α) :
    avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) =
      (S.card : ℝ) * (k a : ℝ) *
        ((k b : ℝ) - if a = b then 1 else 0) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
  have h := avg_selfPairCount_descFactorial (n := n) (r := 1)
    (by omega) (by omega) S e hS k hk a b
  simp only [Nat.descFactorial_one] at h
  rw [h]
  by_cases hab : a = b
  · subst b
    simp only [if_true, Nat.reduceMul, Nat.cast_mul]
    have hka : ((k a).descFactorial 2 : ℝ) =
        (k a : ℝ) * ((k a : ℝ) - 1) :=
      Nat.cast_descFactorial_two ℝ (k a)
    rw [hka]
    rw [Nat.cast_descFactorial_two ℝ n]
    ring
  · simp only [if_neg hab]
    simp only [if_false, Nat.reduceMul, Nat.cast_mul]
    rw [Nat.cast_descFactorial_two ℝ n]
    push_cast
    ring

private theorem self_avg_add {D : Type*} [Fintype D] (f g : D → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib]
  ring

private theorem self_avg_mul_left {D : Type*} [Fintype D]
    (c : ℝ) (f : D → ℝ) : avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private theorem self_avg_const {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) (c : ℝ) : avg (fun _x : D => c) = c := by
  unfold avg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

private theorem self_avg_center_pow_four {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) (x : D → ℝ) (mu : ℝ) :
    avg (fun z => (x z - mu)^4) =
      avg (fun z => (x z)^4) - 4*mu*avg (fun z => (x z)^3) +
        6*mu^2*avg (fun z => (x z)^2) - 4*mu^3*avg x + mu^4 := by
  have hfun : (fun z => (x z - mu)^4) =
      (fun z => x z ^ 4 + (-4*mu) * x z ^ 3 +
        (6*mu^2) * x z ^ 2 + (-4*mu^3) * x z + mu^4) := by
    funext z
    ring
  rw [hfun]
  simp only [self_avg_add, self_avg_mul_left, self_avg_const hD]
  ring

private theorem self_pow_two_eq_desc (x : ℕ) :
    (x : ℝ)^2 = (x.descFactorial 2 : ℝ) + x := by
  rw [Nat.cast_descFactorial_two]
  push_cast
  ring

private theorem self_cast_descFactorial_three (x : ℕ) :
    (x.descFactorial 3 : ℝ) =
      (x : ℝ) * ((x : ℝ) - 1) * ((x : ℝ) - 2) := by
  by_cases hx : 2 ≤ x
  · rw [show 3 = 2 + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hx, Nat.cast_descFactorial_two]
    push_cast
    ring
  · have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl <;> norm_num [Nat.descFactorial]

private theorem self_cast_descFactorial_four (x : ℕ) :
    (x.descFactorial 4 : ℝ) =
      (x : ℝ) * ((x : ℝ) - 1) * ((x : ℝ) - 2) *
        ((x : ℝ) - 3) := by
  by_cases hx : 3 ≤ x
  · rw [show 4 = 3 + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hx, self_cast_descFactorial_three]
    push_cast
    ring
  · have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hx' with rfl | rfl | rfl <;> norm_num [Nat.descFactorial]

private theorem self_pow_three_eq_desc (x : ℕ) :
    (x : ℝ)^3 = (x.descFactorial 3 : ℝ) +
      3 * (x.descFactorial 2 : ℝ) + x := by
  rw [self_cast_descFactorial_three, Nat.cast_descFactorial_two]
  push_cast
  ring

private theorem self_pow_four_eq_desc (x : ℕ) :
    (x : ℝ)^4 = (x.descFactorial 4 : ℝ) +
      6 * (x.descFactorial 3 : ℝ) +
      7 * (x.descFactorial 2 : ℝ) + x := by
  rw [self_cast_descFactorial_four, self_cast_descFactorial_three,
    Nat.cast_descFactorial_two]
  ring

/-- Exact central fourth moment for the self-pair sample.  This is the algebraic
input to the remaining uniform `O(n²)` estimate. -/
theorem avg_selfPairCount_center_four_formula
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 8 ≤ n)
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
    (hS : ∀ i ∈ S, e i ∉ S) (k : α → ℕ) (hk : ∑ a, k a = n)
    (a b : α) :
    let F := fun r : ℕ =>
      ((S.card.descFactorial r *
          (if a = b then (k a).descFactorial (2*r)
           else (k a).descFactorial r * (k b).descFactorial r) : ℕ) : ℝ) /
        n.descFactorial (2*r)
    avg (fun x : Words n k =>
      ((selfPairCount S e a b x.val : ℝ) - F 1)^4) =
      (F 4 + 6*F 3 + 7*F 2 + F 1) -
        4*(F 1)*(F 3 + 3*F 2 + F 1) +
        6*(F 1)^2*(F 2 + F 1) - 4*(F 1)^3*(F 1) + (F 1)^4 := by
  dsimp only
  have hwords := self_words_card_pos (by omega) k hk
  have hA1 := avg_selfPairCount_descFactorial (n := n) (r := 1)
    (by omega) (by omega) S e hS k hk a b
  have hA2 := avg_selfPairCount_descFactorial (n := n) (r := 2)
    (by omega) (by omega) S e hS k hk a b
  have hA3 := avg_selfPairCount_descFactorial (n := n) (r := 3)
    (by omega) (by omega) S e hS k hk a b
  have hA4 := avg_selfPairCount_descFactorial (n := n) (r := 4)
    (by omega) (by omega) S e hS k hk a b
  simp only [Nat.descFactorial_one] at hA1
  have hpow2 :
      avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)^2) =
        avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) := by
    calc
      _ = avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 2 : ℝ) +
            (selfPairCount S e a b x.val : ℝ)) := by
              congr 1
              funext x
              exact self_pow_two_eq_desc (selfPairCount S e a b x.val)
      _ = _ := self_avg_add _ _
  have hpow3 :
      avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)^3) =
        avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 3 : ℝ)) +
        3 * avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) := by
    calc
      _ = avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 3 : ℝ) +
            3 * ((selfPairCount S e a b x.val).descFactorial 2 : ℝ) +
            (selfPairCount S e a b x.val : ℝ)) := by
              congr 1
              funext x
              exact self_pow_three_eq_desc (selfPairCount S e a b x.val)
      _ = _ := by rw [self_avg_add, self_avg_add, self_avg_mul_left]
  have hpow4 :
      avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)^4) =
        avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 4 : ℝ)) +
        6 * avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 3 : ℝ)) +
        7 * avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) := by
    calc
      _ = avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 4 : ℝ) +
            6 * ((selfPairCount S e a b x.val).descFactorial 3 : ℝ) +
            7 * ((selfPairCount S e a b x.val).descFactorial 2 : ℝ) +
            (selfPairCount S e a b x.val : ℝ)) := by
              congr 1
              funext x
              exact self_pow_four_eq_desc (selfPairCount S e a b x.val)
      _ = _ := by
        rw [self_avg_add, self_avg_add, self_avg_add,
          self_avg_mul_left, self_avg_mul_left]
  rw [self_avg_center_pow_four hwords, hpow4, hpow3, hpow2,
    hA4, hA3, hA2, hA1]
  push_cast
  simp only [Nat.descFactorial_one]

/-- An oriented self-pair sample is empty at lengths zero and one. -/
theorem selfPairCount_eq_zero_of_small {α : Type*} [DecidableEq α]
    {n : ℕ} (hn : n ≤ 1) (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (hS : ∀ i ∈ S, e i ∉ S)
    (a b : α) (x : Fin n → α) : selfPairCount S e a b x = 0 := by
  have hSempt : S = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    have hei : e i = i := by
      apply Fin.ext
      omega
    apply hS i hi
    rw [hei]
    exact hi
  simp [selfPairCount, hSempt]

end OmegaBound.ADVXXZGeneral
end
