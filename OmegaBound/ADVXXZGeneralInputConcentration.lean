import OmegaBound.ADVXXZGeneralCoarseTransportParent25
import OmegaBound.ADVXXZGeneralWords
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Logic.Equiv.Fintype
import OmegaBound.ADVXXZGeneralAmend25Parent

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem input_typeCnt_comp_perm {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (e : Equiv.Perm (Fin n)) (a : α) :
    typeCnt (fun i => x (e i)) a = typeCnt x a := by
  unfold typeCnt
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa using hi
  · intro i₁ _ i₂ _ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa using hj

private def inputWordPerm {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {k : α → ℕ} (e : Equiv.Perm (Fin n)) :
    Words n k ≃ Words n k where
  toFun x := ⟨fun i => x.val (e.symm i), fun a => by
    rw [input_typeCnt_comp_perm x.val e.symm a]
    exact x.property a⟩
  invFun x := ⟨fun i => x.val (e i), fun a => by
    rw [input_typeCnt_comp_perm x.val e a]
    exact x.property a⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

private noncomputable def inputEmbeddingPerm {r n : ℕ}
    (f g : Fin r ↪ Fin n) : Equiv.Perm (Fin n) := by
  classical
  let h : Set.range f ≃ Set.range g := f.toEquivRange.symm.trans g.toEquivRange
  exact h.extendSubtype

private theorem inputEmbeddingPerm_apply {r n : ℕ} (f g : Fin r ↪ Fin n)
    (i : Fin r) : inputEmbeddingPerm f g (f i) = g i := by
  classical
  unfold inputEmbeddingPerm
  rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self i)]
  simp only [Equiv.trans_apply, Function.Embedding.toEquivRange_symm_apply_self,
    Function.Embedding.toEquivRange_apply, Subtype.coe_mk]

private abbrev InputWordHit {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (k : α → ℕ) (a : α) {r : ℕ} (f : Fin r ↪ Fin n) :=
  {x : Words n k // ∀ i, x.val (f i) = a}

private noncomputable def inputWordHitEquiv {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} {k : α → ℕ} (a : α) {r : ℕ}
    (f g : Fin r ↪ Fin n) : InputWordHit k a f ≃ InputWordHit k a g := by
  classical
  let e := inputEmbeddingPerm f g
  refine (inputWordPerm e).subtypeEquiv ?_
  intro x
  constructor
  · intro hx i
    change x.val (e.symm (g i)) = a
    rw [← inputEmbeddingPerm_apply f g i, e.symm_apply_apply]
    exact hx i
  · intro hx i
    have hi := hx i
    change x.val (e.symm (g i)) = a at hi
    rw [← inputEmbeddingPerm_apply f g i, e.symm_apply_apply] at hi
    exact hi

private abbrev InputHitEmbedding {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (a : α) (r : ℕ) :=
  {f : Fin r ↪ Fin n // ∀ i, x (f i) = a}

private def inputHitEmbeddingEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {n r : ℕ} (x : Fin n → α) (a : α) :
    InputHitEmbedding x a r ≃ (Fin r ↪ {i : Fin n // x i = a}) where
  toFun f :=
    { toFun := fun i => ⟨f.val i, f.property i⟩
      inj' := fun _ _ h => f.val.injective (Subtype.ext_iff.mp h) }
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun i => (f i).property⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    rfl
  right_inv f := by
    ext i
    rfl

private theorem input_card_hitEmbedding {α : Type*} [Fintype α] [DecidableEq α]
    {n r : ℕ} (x : Fin n → α) (a : α) :
    Fintype.card (InputHitEmbedding x a r) = (typeCnt x a).descFactorial r := by
  classical
  rw [Fintype.card_congr (inputHitEmbeddingEquiv x a), Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  congr 1
  simpa [typeCnt] using Fintype.card_subtype (fun i : Fin n => x i = a)

private def inputWordHitSigmaEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {n r : ℕ} (k : α → ℕ) (a : α) :
    (Σ f : Fin r ↪ Fin n, InputWordHit k a f) ≃
      (Σ x : Words n k, InputHitEmbedding x.val a r) where
  toFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  invFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl

private theorem input_card_wordHit_identity {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (k : α → ℕ) (a : α) (f : Fin r ↪ Fin n) :
    n.descFactorial r * Fintype.card (InputWordHit k a f) =
      Fintype.card (Words n k) * (k a).descFactorial r := by
  classical
  calc
    n.descFactorial r * Fintype.card (InputWordHit k a f) =
        Fintype.card (Fin r ↪ Fin n) * Fintype.card (InputWordHit k a f) := by simp
    _ = ∑ g : Fin r ↪ Fin n, Fintype.card (InputWordHit k a f) := by simp
    _ = ∑ g : Fin r ↪ Fin n, Fintype.card (InputWordHit k a g) := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.card_congr (inputWordHitEquiv a f g)
    _ = Fintype.card (Σ g : Fin r ↪ Fin n, InputWordHit k a g) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card (Σ x : Words n k, InputHitEmbedding x.val a r) :=
      Fintype.card_congr (inputWordHitSigmaEquiv k a)
    _ = ∑ x : Words n k, Fintype.card (InputHitEmbedding x.val a r) := by
      rw [Fintype.card_sigma]
    _ = ∑ _x : Words n k, (k a).descFactorial r := by
      apply Finset.sum_congr rfl
      intro x _
      rw [input_card_hitEmbedding, x.property a]
    _ = Fintype.card (Words n k) * (k a).descFactorial r := by simp

private def inputFinEmbeddingOfLE {r n : ℕ} (h : r ≤ n) : Fin r ↪ Fin n where
  toFun i := ⟨i.val, i.isLt.trans_le h⟩
  inj' i j hxy := Fin.ext (congrArg (fun z : Fin n => z.val) hxy)

def inputSubsetCount {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (a : α) (x : Fin n → α) : ℕ :=
  (S.filter fun i => x i = a).card

private abbrev InputSubsetHitEmbedding {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (x : Fin n → α) (a : α) (r : ℕ) :=
  {f : Fin r ↪ {i : Fin n // i ∈ S} // ∀ i, x (f i).val = a}

private def inputSubsetHitEmbeddingEquiv {α : Type*} [DecidableEq α] {n r : ℕ}
    (S : Finset (Fin n)) (x : Fin n → α) (a : α) :
    InputSubsetHitEmbedding S x a r ≃
      (Fin r ↪ {i : Fin n // i ∈ S ∧ x i = a}) where
  toFun f :=
    { toFun := fun i => ⟨(f.val i).val, (f.val i).property, f.property i⟩
      inj' := by
        intro i j h
        have h' := congrArg
          (fun z : {i : Fin n // i ∈ S ∧ x i = a} => z.val) h
        exact f.val.injective (Subtype.ext h') }
  invFun f :=
    ⟨{ toFun := fun i => ⟨(f i).val, (f i).property.1⟩
       inj' := by
         intro i j h
         have h' := congrArg (fun z : {i : Fin n // i ∈ S} => z.val) h
         exact f.injective (Subtype.ext h') },
      fun i => (f i).property.2⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    rfl
  right_inv f := by
    ext i
    rfl

private theorem input_card_subsetHitEmbedding {α : Type*} [DecidableEq α]
    {n r : ℕ} (S : Finset (Fin n)) (x : Fin n → α) (a : α) :
    Fintype.card (InputSubsetHitEmbedding S x a r) =
      (inputSubsetCount S a x).descFactorial r := by
  classical
  rw [Fintype.card_congr (inputSubsetHitEmbeddingEquiv S x a),
    Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  rw [Fintype.card_subtype]
  unfold inputSubsetCount
  apply congrArg (fun z : ℕ => z.descFactorial r)
  apply congrArg Finset.card
  ext i
  simp

private def inputSubsetHitSigmaEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {n r : ℕ} (S : Finset (Fin n)) (k : α → ℕ) (a : α) :
    (Σ f : Fin r ↪ {i : Fin n // i ∈ S},
      InputWordHit k a (f.trans (Function.Embedding.subtype _))) ≃
    (Σ x : Words n k, InputSubsetHitEmbedding S x.val a r) where
  toFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  invFun z := ⟨z.2.val, ⟨z.1, z.2.property⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl

private theorem input_subsetCount_descFactorial_sum {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (hrn : r ≤ n) (S : Finset (Fin n))
    (k : α → ℕ) (a : α) :
    (∑ x : Words n k, (inputSubsetCount S a x).descFactorial r) *
        n.descFactorial r =
      Fintype.card (Words n k) * S.card.descFactorial r *
        (k a).descFactorial r := by
  classical
  let f₀ : Fin r ↪ Fin n := inputFinEmbeddingOfLE hrn
  have hf := input_card_wordHit_identity k a f₀
  have hsum :
      (∑ x : Words n k, (inputSubsetCount S a x).descFactorial r) =
        S.card.descFactorial r * Fintype.card (InputWordHit k a f₀) := by
    calc
      (∑ x : Words n k, (inputSubsetCount S a x).descFactorial r) =
          ∑ x : Words n k, Fintype.card (InputSubsetHitEmbedding S x.val a r) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (input_card_subsetHitEmbedding S x.val a).symm
      _ = Fintype.card (Σ x : Words n k, InputSubsetHitEmbedding S x.val a r) := by
        rw [Fintype.card_sigma]
      _ = Fintype.card (Σ f : Fin r ↪ {i : Fin n // i ∈ S},
          InputWordHit k a (f.trans (Function.Embedding.subtype _))) :=
        Fintype.card_congr (inputSubsetHitSigmaEquiv S k a).symm
      _ = ∑ f : Fin r ↪ {i : Fin n // i ∈ S},
          Fintype.card (InputWordHit k a (f.trans (Function.Embedding.subtype _))) := by
        rw [Fintype.card_sigma]
      _ = ∑ _f : Fin r ↪ {i : Fin n // i ∈ S},
          Fintype.card (InputWordHit k a f₀) := by
        apply Finset.sum_congr rfl
        intro f _
        exact Fintype.card_congr
          (inputWordHitEquiv a (f.trans (Function.Embedding.subtype _)) f₀)
      _ = S.card.descFactorial r * Fintype.card (InputWordHit k a f₀) := by simp
  rw [hsum]
  calc
    (S.card.descFactorial r * Fintype.card (InputWordHit k a f₀)) *
        n.descFactorial r =
      S.card.descFactorial r *
        (n.descFactorial r * Fintype.card (InputWordHit k a f₀)) := by ring
    _ = S.card.descFactorial r *
        (Fintype.card (Words n k) * (k a).descFactorial r) := by rw [hf]
    _ = Fintype.card (Words n k) * S.card.descFactorial r *
        (k a).descFactorial r := by ring

private theorem input_words_card_pos {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 0 < n) (k : α → ℕ) (hk : ∑ a, k a = n) :
    0 < Fintype.card (Words n k) := by
  have hbounds := type_class_bounds n k hk
  have hleft : 0 < Real.exp ((n : ℝ) * entropyNats (fun a => (k a : ℝ) / n)) /
      ((n : ℝ) + 1) ^ Fintype.card α := by positivity
  have hcardR : 0 < (Fintype.card (Words n k) : ℝ) := hleft.trans_le hbounds.1
  exact_mod_cast hcardR

private theorem input_avg_subset_descFactorial {α : Type*} [Fintype α]
    [DecidableEq α] {n r : ℕ} (hrn : r ≤ n) (S : Finset (Fin n))
    (k : α → ℕ) (a : α) (hwords : 0 < Fintype.card (Words n k)) :
    avg (fun x : Words n k => ((inputSubsetCount S a x).descFactorial r : ℝ)) =
      (S.card.descFactorial r : ℝ) * (k a).descFactorial r /
        n.descFactorial r := by
  have hnat := input_subsetCount_descFactorial_sum hrn S k a
  have hreal := congrArg (fun x : ℕ => (x : ℝ)) hnat
  simp only [Nat.cast_mul, Nat.cast_sum] at hreal
  have hD : (Fintype.card (Words n k) : ℝ) ≠ 0 := by
    exact_mod_cast hwords.ne'
  have hN : (n.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrn))
  unfold avg
  field_simp
  nlinarith

private theorem input_avg_add {D : Type*} [Fintype D] (f g : D → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib]
  ring

private theorem input_avg_mul_left {D : Type*} [Fintype D] (c : ℝ) (f : D → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private theorem input_avg_const {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) (c : ℝ) : avg (fun _x : D => c) = c := by
  unfold avg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

private theorem input_avg_center_pow_four {D : Type*} [Fintype D]
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
  simp only [input_avg_add, input_avg_mul_left, input_avg_const hD]
  ring

private theorem input_cast_descFactorial_three (x : ℕ) :
    (x.descFactorial 3 : ℝ) = (x : ℝ) * ((x : ℝ) - 1) * ((x : ℝ) - 2) := by
  by_cases hx : 2 ≤ x
  · rw [show 3 = 2 + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hx, Nat.cast_descFactorial_two]
    push_cast
    ring
  · have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl <;> norm_num [Nat.descFactorial]

private theorem input_cast_descFactorial_four (x : ℕ) :
    (x.descFactorial 4 : ℝ) =
      (x : ℝ) * ((x : ℝ) - 1) * ((x : ℝ) - 2) * ((x : ℝ) - 3) := by
  by_cases hx : 3 ≤ x
  · rw [show 4 = 3 + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hx, input_cast_descFactorial_three]
    push_cast
    ring
  · have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hx' with rfl | rfl | rfl <;> norm_num [Nat.descFactorial]

private theorem input_pow_two_eq_desc (x : ℕ) :
    (x : ℝ)^2 = (x.descFactorial 2 : ℝ) + x := by
  rw [Nat.cast_descFactorial_two]
  push_cast
  ring

private theorem input_pow_three_eq_desc (x : ℕ) :
    (x : ℝ)^3 = (x.descFactorial 3 : ℝ) +
      3 * (x.descFactorial 2 : ℝ) + x := by
  rw [input_cast_descFactorial_three, Nat.cast_descFactorial_two]
  push_cast
  ring

private theorem input_pow_four_eq_desc (x : ℕ) :
    (x : ℝ)^4 = (x.descFactorial 4 : ℝ) +
      6 * (x.descFactorial 3 : ℝ) +
      7 * (x.descFactorial 2 : ℝ) + x := by
  rw [input_cast_descFactorial_four, input_cast_descFactorial_three,
    Nat.cast_descFactorial_two]
  push_cast
  ring

private def inputFourthQ (N K L : ℝ) : ℝ :=
  N^4 + 3*N^3*K*L - 6*N^3*K - 6*N^3*L + N^3 -
    3*N^2*K^2*L + 6*N^2*K^2 - 3*N^2*K*L^2 + 18*N^2*K*L +
    6*N^2*L^2 + 3*N*K^2*L^2 - 18*N*K^2*L - 18*N*K*L^2 +
    18*K^2*L^2

private theorem input_subsetCount_fourth_formula {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n))
    (k : α → ℕ) (hk : ∑ a, k a = n) (a : α) :
    avg (fun x : Words n k =>
      ((inputSubsetCount S a x : ℝ) - (S.card : ℝ) * k a / n)^4) =
      (S.card : ℝ) * k a * ((n : ℝ) - S.card) * ((n : ℝ) - k a) *
        inputFourthQ n S.card (k a) /
          ((n : ℝ)^4 * ((n : ℝ)-3) * ((n : ℝ)-2) * ((n : ℝ)-1)) := by
  have hnpos : 0 < n := by omega
  have hwords := input_words_card_pos hnpos k hk
  have hA1 := input_avg_subset_descFactorial (show 1 ≤ n by omega) S k a hwords
  have hA2 := input_avg_subset_descFactorial (show 2 ≤ n by omega) S k a hwords
  have hA3 := input_avg_subset_descFactorial (show 3 ≤ n by omega) S k a hwords
  have hA4 := input_avg_subset_descFactorial hn S k a hwords
  have hmean :
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)) =
        (S.card : ℝ) * k a / n := by
    simpa only [Nat.descFactorial_one] using hA1
  have hpow2 :
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^2) =
        avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)) := by
    calc
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^2) =
          avg (fun x : Words n k =>
            ((inputSubsetCount S a x).descFactorial 2 : ℝ) +
              (inputSubsetCount S a x : ℝ)) := by
            congr 1
            funext x
            exact input_pow_two_eq_desc (inputSubsetCount S a x)
      _ = _ := input_avg_add _ _
  have hpow3 :
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^3) =
        avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 3 : ℝ)) +
        3 * avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)) := by
    calc
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^3) =
          avg (fun x : Words n k =>
            ((inputSubsetCount S a x).descFactorial 3 : ℝ) +
              3 * ((inputSubsetCount S a x).descFactorial 2 : ℝ) +
              (inputSubsetCount S a x : ℝ)) := by
            congr 1
            funext x
            exact input_pow_three_eq_desc (inputSubsetCount S a x)
      _ = _ := by rw [input_avg_add, input_avg_add, input_avg_mul_left]
  have hpow4 :
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^4) =
        avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 4 : ℝ)) +
        6 * avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 3 : ℝ)) +
        7 * avg (fun x : Words n k =>
          ((inputSubsetCount S a x).descFactorial 2 : ℝ)) +
        avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)) := by
    calc
      avg (fun x : Words n k => (inputSubsetCount S a x : ℝ)^4) =
          avg (fun x : Words n k =>
            ((inputSubsetCount S a x).descFactorial 4 : ℝ) +
              6 * ((inputSubsetCount S a x).descFactorial 3 : ℝ) +
              7 * ((inputSubsetCount S a x).descFactorial 2 : ℝ) +
              (inputSubsetCount S a x : ℝ)) := by
            congr 1
            funext x
            exact input_pow_four_eq_desc (inputSubsetCount S a x)
      _ = _ := by
        rw [input_avg_add, input_avg_add, input_avg_add,
          input_avg_mul_left, input_avg_mul_left]
  rw [input_avg_center_pow_four hwords]
  rw [hpow4, hpow3, hpow2, hA4, hA3, hA2, hmean]
  rw [input_cast_descFactorial_four, input_cast_descFactorial_four,
    input_cast_descFactorial_four, input_cast_descFactorial_three,
    input_cast_descFactorial_three, input_cast_descFactorial_three,
    Nat.cast_descFactorial_two, Nat.cast_descFactorial_two,
    Nat.cast_descFactorial_two]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
  have hn2 : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 2 by omega))
  have hn3 : (n : ℝ) - 3 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 3 by omega))
  unfold inputFourthQ
  field_simp
  ring

private theorem input_fourth_formula_le (N K L : ℝ) (hN : 6 ≤ N)
    (hK0 : 0 ≤ K) (hKN : K ≤ N) (hL0 : 0 ≤ L) (hLN : L ≤ N) :
    K * L * (N-K) * (N-L) * inputFourthQ N K L /
        (N^4 * (N-3) * (N-2) * (N-1)) ≤ 448 * N^2 := by
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNK0 : 0 ≤ N-K := by linarith
  have hNL0 : 0 ≤ N-L := by linarith
  have hNKle : N-K ≤ N := by linarith
  have hNLle : N-L ≤ N := by linarith
  have hpref0 : 0 ≤ K*L*(N-K)*(N-L) := by positivity
  have hpref : K*L*(N-K)*(N-L) ≤ N^4 := by
    calc
      K*L*(N-K)*(N-L) ≤ N*N*N*N := by gcongr
      _ = N^4 := by ring
  have hN4 : N^4 ≤ N^5 := by
    calc
      N^4 = N^4*1 := by ring
      _ ≤ N^4*N := by gcongr
      _ = N^5 := by ring
  have hN3 : N^3 ≤ N^5 := by
    calc
      N^3 = N^3*1*1 := by ring
      _ ≤ N^3*N*N := by gcongr
      _ = N^5 := by ring
  have hN3KL : N^3*K*L ≤ N^5 := by
    calc
      N^3*K*L ≤ N^3*N*N := by gcongr
      _ = N^5 := by ring
  have hN2K2 : N^2*K^2 ≤ N^5 := by
    calc
      N^2*K^2 ≤ N^2*N^2 := by gcongr
      _ ≤ N^5 := by nlinarith [hN4]
  have hN2KL : N^2*K*L ≤ N^5 := by
    calc
      N^2*K*L ≤ N^2*N*N := by gcongr
      _ ≤ N^5 := by nlinarith [hN4]
  have hN2L2 : N^2*L^2 ≤ N^5 := by
    calc
      N^2*L^2 ≤ N^2*N^2 := by gcongr
      _ ≤ N^5 := by nlinarith [hN4]
  have hNK2L2 : N*K^2*L^2 ≤ N^5 := by
    calc
      N*K^2*L^2 ≤ N*N^2*N^2 := by gcongr
      _ = N^5 := by ring
  have hK2L2 : K^2*L^2 ≤ N^5 := by
    calc
      K^2*L^2 ≤ N^2*N^2 := by gcongr
      _ ≤ N^5 := by nlinarith [hN4]
  have hneg1 : 0 ≤ N^3*K := by positivity
  have hneg2 : 0 ≤ N^3*L := by positivity
  have hneg3 : 0 ≤ N^2*K^2*L := by positivity
  have hneg4 : 0 ≤ N^2*K*L^2 := by positivity
  have hneg5 : 0 ≤ N*K^2*L := by positivity
  have hneg6 : 0 ≤ N*K*L^2 := by positivity
  have hQle : inputFourthQ N K L ≤ 56*N^5 := by
    unfold inputFourthQ
    nlinarith [hN4, hN3, hN3KL, hN2K2, hN2KL, hN2L2,
      hNK2L2, hK2L2, hneg1, hneg2, hneg3, hneg4, hneg5, hneg6]
  have hhalf3 : N/2 ≤ N-3 := by linarith
  have hhalf2 : N/2 ≤ N-2 := by linarith
  have hhalf1 : N/2 ≤ N-1 := by linarith
  have hhalf0 : 0 ≤ N/2 := by positivity
  have hNm3 : 0 < N-3 := by linarith
  have hNm2 : 0 < N-2 := by linarith
  have hNm1 : 0 < N-1 := by linarith
  have hpairhalf : (N/2)*(N/2) ≤ (N-3)*(N-2) :=
    mul_le_mul hhalf3 hhalf2 hhalf0 hNm3.le
  have hprod : N^3/8 ≤ (N-3)*(N-2)*(N-1) := by
    calc
      N^3/8 = (N/2)*(N/2)*(N/2) := by ring
      _ ≤ (N-3)*(N-2)*(N-1) :=
        mul_le_mul hpairhalf hhalf1 hhalf0 (mul_nonneg hNm3.le hNm2.le)
  have hden : N^7/8 ≤ N^4*(N-3)*(N-2)*(N-1) := by
    calc
      N^7/8 = N^4*(N^3/8) := by ring
      _ ≤ N^4*((N-3)*(N-2)*(N-1)) := by gcongr
      _ = N^4*(N-3)*(N-2)*(N-1) := by ring
  have hdenpos : 0 < N^4*(N-3)*(N-2)*(N-1) := by
    exact mul_pos (mul_pos (mul_pos (pow_pos (by linarith) 4) hNm3) hNm2) hNm1
  by_cases hQ : 0 ≤ inputFourthQ N K L
  · apply (div_le_iff₀ hdenpos).2
    calc
      K*L*(N-K)*(N-L)*inputFourthQ N K L ≤ N^4*(56*N^5) :=
        mul_le_mul hpref hQle hQ (by positivity)
      _ = 448*N^2*(N^7/8) := by ring
      _ ≤ 448*N^2*(N^4*(N-3)*(N-2)*(N-1)) := by gcongr
  · have hQ' : inputFourthQ N K L ≤ 0 := le_of_not_ge hQ
    have hnum : K*L*(N-K)*(N-L)*inputFourthQ N K L ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpref0 hQ'
    exact (div_nonpos_of_nonpos_of_nonneg hnum hdenpos.le).trans (by positivity)

private theorem input_count_le_of_words_card_pos {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (k : α → ℕ)
    (hcard : 0 < Fintype.card (Words n k)) (a : α) : k a ≤ n := by
  let ⟨x⟩ := Fintype.card_pos_iff.mp hcard
  rw [← x.property a]
  unfold typeCnt
  simpa using Finset.card_filter_le Finset.univ (fun i : Fin n => x.val i = a)

private theorem input_subsetCount_le {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (a : α) (x : Fin n → α) : inputSubsetCount S a x ≤ n := by
  unfold inputSubsetCount
  exact (Finset.card_filter_le S _).trans (by simpa using S.card_le_univ)

private theorem input_avg_le_const {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) (f : D → ℝ) (c : ℝ) (h : ∀ x, f x ≤ c) :
    avg f ≤ c := by
  unfold avg
  have hcard : 0 < (Fintype.card D : ℝ) := by exact_mod_cast hD
  apply (div_le_iff₀ hcard).2
  calc
    ∑ x, f x ≤ ∑ _x : D, c := Finset.sum_le_sum fun x _ => h x
    _ = c * Fintype.card D := by simp [mul_comm]

/-- Fourth-moment concentration for a fixed subset of a uniform finite type class. -/
theorem subset_fourth_moment {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hn : 0 < n) (S : Finset (Fin n))
      (k : α → ℕ) (hk : ∑ a, k a = n) (a : α),
      avg (fun x : Words n k =>
        ((inputSubsetCount S a x : ℝ) - (S.card : ℝ) * k a / n)^4) ≤
          C * (n : ℝ)^2 := by
  refine ⟨448, by norm_num, ?_⟩
  intro n hn S k hk a
  have hwords := input_words_card_pos hn k hk
  have hkaN := input_count_le_of_words_card_pos k hwords a
  have hSN : S.card ≤ n := by simpa using S.card_le_univ
  by_cases hn6 : 6 ≤ n
  · rw [input_subsetCount_fourth_formula (by omega) S k hk a]
    apply input_fourth_formula_le
    · exact_mod_cast hn6
    · positivity
    · exact_mod_cast hSN
    · positivity
    · exact_mod_cast hkaN
  · have hmean0 : 0 ≤ (S.card : ℝ) * k a / n := by positivity
    have hmul : (S.card : ℝ) * k a ≤ (n : ℝ) * n := by
      gcongr <;> exact_mod_cast (by assumption)
    have hmeanN : (S.card : ℝ) * k a / n ≤ n := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have hpoint : ∀ x : Words n k,
        ((inputSubsetCount S a x : ℝ) - (S.card : ℝ)*k a/n)^4 ≤ (n : ℝ)^4 := by
      intro x
      have hcount0 : 0 ≤ (inputSubsetCount S a x : ℝ) := by positivity
      have hcountN : (inputSubsetCount S a x : ℝ) ≤ n := by
        exact_mod_cast input_subsetCount_le S a x.val
      have habs : |(inputSubsetCount S a x : ℝ) - (S.card : ℝ)*k a/n| ≤ n := by
        rw [abs_le]
        constructor <;> linarith
      calc
        ((inputSubsetCount S a x : ℝ) - (S.card : ℝ)*k a/n)^4 =
            |(inputSubsetCount S a x : ℝ) - (S.card : ℝ)*k a/n|^4 := by
          rw [← abs_pow]
          exact (abs_of_nonneg (by positivity)).symm
        _ ≤ (n : ℝ)^4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
    calc
      avg (fun x : Words n k =>
          ((inputSubsetCount S a x : ℝ) - (S.card : ℝ)*k a/n)^4) ≤
          (n : ℝ)^4 := input_avg_le_const hwords _ _ hpoint
      _ ≤ 448*(n : ℝ)^2 := by
        have hn5 : n ≤ 5 := by omega
        interval_cases n <;> norm_num

/-- The number of matches of `(a,b)` whose first coordinate lies in a fixed subset. -/
def restrictedPairCount {α β : Type*} [DecidableEq α] [DecidableEq β]
    {n : ℕ} (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a : α) (b : β)
    (z : (Fin n → α) × (Fin n → β)) : ℕ :=
  (S.filter fun i => z.1 i = a ∧ z.2 (e i) = b).card

private def inputSelectedPositions {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a : α) (x : Fin n → α) :
    Finset (Fin n) := (S.filter fun i => x i = a).map e.toEmbedding

private theorem input_selectedPositions_card {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a : α) (x : Fin n → α) :
    (inputSelectedPositions S e a x).card = inputSubsetCount S a x := by
  simp only [inputSelectedPositions, Finset.card_map, inputSubsetCount]

private theorem input_restricted_eq_subset {α β : Type*}
    [DecidableEq α] [DecidableEq β] {n : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (a : α) (b : β) (x : Fin n → α) (y : Fin n → β) :
    restrictedPairCount S e a b (x,y) =
      inputSubsetCount (inputSelectedPositions S e a x) b y := by
  unfold restrictedPairCount inputSubsetCount inputSelectedPositions
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_map.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi'.1, hi'.2.1⟩, rfl⟩, hi'.2.2⟩
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    obtain ⟨i, hi, hieq⟩ := Finset.mem_map.mp hj'.1
    subst j
    have hi' := Finset.mem_filter.mp hi
    exact ⟨i, Finset.mem_filter.mpr ⟨hi'.1, hi'.2, hj'.2⟩, rfl⟩

private theorem input_avg_mono {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) {f g : D → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := by
  unfold avg
  have hcard : 0 < (Fintype.card D : ℝ) := by exact_mod_cast hD
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) hcard.le

private theorem input_avg_prod {A B : Type*} [Fintype A] [Fintype B]
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B) (f : A → B → ℝ) :
    avg (fun z : A × B => f z.1 z.2) = avg (fun x : A => avg (f x)) := by
  have hAr : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBr : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Nat.cast_mul, Finset.sum_div]
  field_simp

private theorem input_add_fourth_le (u v : ℝ) : (u+v)^4 ≤ 8*(u^4+v^4) := by
  nlinarith [sq_nonneg (u-v), sq_nonneg (u^2-v^2),
    sq_nonneg ((u+v)^2 - 2*(u^2+v^2))]

/-- Fourth-moment concentration for matching restricted to an arbitrary fixed subset. -/
theorem restricted_matching_fourth_moment
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hn : 0 < n)
    (k : α → ℕ) (l : β → ℕ) (hk : ∑ a, k a = n) (hl : ∑ b, l b = n)
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a : α) (b : β),
    avg (fun z : PairWords n k l =>
      ((restrictedPairCount S e a b (z.1.val,z.2.val) : ℝ) -
        (S.card : ℝ) * k a * l b / (n : ℝ)^2)^4) ≤ C*(n:ℝ)^2 := by
  obtain ⟨Cα, hCα, hα⟩ := (subset_fourth_moment (α := α))
  obtain ⟨Cβ, hCβ, hβ⟩ := (subset_fourth_moment (α := β))
  refine ⟨8*(Cα+Cβ), by positivity, ?_⟩
  intro n hn k l hk hl S e a b
  have hwordsα := input_words_card_pos hn k hk
  have hwordsβ := input_words_card_pos hn l hl
  have hlbN := input_count_le_of_words_card_pos l hwordsβ b
  have hcoef0 : 0 ≤ (l b : ℝ) / n := by positivity
  have hcoef1 : (l b : ℝ) / n ≤ 1 := by
    apply (div_le_one (by positivity)).2
    exact_mod_cast hlbN
  let devA : Words n k → ℝ := fun x =>
    (inputSubsetCount S a x.val : ℝ) - (S.card : ℝ) * k a / n
  let innerDev : Words n k → Words n l → ℝ := fun x y =>
    (restrictedPairCount S e a b (x.val,y.val) : ℝ) -
      (inputSubsetCount S a x.val : ℝ) * l b / n
  let totalDev : Words n k → Words n l → ℝ := fun x y =>
    (restrictedPairCount S e a b (x.val,y.val) : ℝ) -
      (S.card : ℝ) * k a * l b / (n : ℝ)^2
  have hsplit (x : Words n k) (y : Words n l) :
      totalDev x y = innerDev x y + ((l b : ℝ)/n) * devA x := by
    dsimp only [totalDev, innerDev, devA]
    field_simp
    ring
  have hinner (x : Words n k) :
      avg (fun y : Words n l => (innerDev x y)^4) ≤ Cβ*(n:ℝ)^2 := by
    have hy := hβ n hn (inputSelectedPositions S e a x.val) l hl b
    simpa only [innerDev, input_restricted_eq_subset,
      input_selectedPositions_card] using hy
  have hcoefPow : ((l b : ℝ)/n)^4 ≤ 1 := by
    exact pow_le_one₀ hcoef0 hcoef1
  have hscaled (x : Words n k) :
      (((l b : ℝ)/n) * devA x)^4 ≤ (devA x)^4 := by
    rw [mul_pow]
    have hdev : 0 ≤ (devA x)^4 := by positivity
    exact mul_le_of_le_one_left hdev hcoefPow
  have hperx (x : Words n k) :
      avg (fun y : Words n l => (totalDev x y)^4) ≤
        8*Cβ*(n:ℝ)^2 + 8*(devA x)^4 := by
    calc
      avg (fun y : Words n l => (totalDev x y)^4) =
          avg (fun y : Words n l =>
            (innerDev x y + ((l b : ℝ)/n) * devA x)^4) := by
        congr 1
        funext y
        rw [hsplit]
      _ ≤ avg (fun y : Words n l =>
          8*((innerDev x y)^4 + (((l b : ℝ)/n) * devA x)^4)) :=
        input_avg_mono hwordsβ (fun y => input_add_fourth_le _ _)
      _ = 8 * avg (fun y : Words n l => (innerDev x y)^4) +
          8 * (((l b : ℝ)/n) * devA x)^4 := by
        simp only [mul_add, input_avg_add, input_avg_mul_left,
          input_avg_const hwordsβ]
      _ ≤ 8*Cβ*(n:ℝ)^2 + 8*(devA x)^4 := by
        have h₁ := mul_le_mul_of_nonneg_left (hinner x) (by norm_num : (0:ℝ) ≤ 8)
        have h₂ := mul_le_mul_of_nonneg_left (hscaled x) (by norm_num : (0:ℝ) ≤ 8)
        nlinarith
  have hdevA : avg (fun x : Words n k => (devA x)^4) ≤ Cα*(n:ℝ)^2 := by
    simpa only [devA] using hα n hn S k hk a
  calc
    avg (fun z : PairWords n k l =>
        ((restrictedPairCount S e a b (z.1.val,z.2.val) : ℝ) -
          (S.card : ℝ) * k a * l b / (n : ℝ)^2)^4) =
        avg (fun x : Words n k => avg (fun y : Words n l => (totalDev x y)^4)) := by
      change avg (fun z : Words n k × Words n l => (totalDev z.1 z.2)^4) = _
      simpa using input_avg_prod hwordsα hwordsβ
        (fun x : Words n k => fun y : Words n l => (totalDev x y)^4)
    _ ≤ avg (fun x : Words n k =>
        8*Cβ*(n:ℝ)^2 + 8*(devA x)^4) := input_avg_mono hwordsα hperx
    _ = 8*Cβ*(n:ℝ)^2 + 8*avg (fun x : Words n k => (devA x)^4) := by
      simp only [input_avg_add, input_avg_mul_left, input_avg_const hwordsα]
    _ ≤ 8*Cβ*(n:ℝ)^2 + 8*(Cα*(n:ℝ)^2) := by gcongr
    _ = 8*(Cα+Cβ)*(n:ℝ)^2 := by ring

end OmegaBound.ADVXXZGeneral
end
