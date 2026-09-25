import OmegaBound.ADVXXZGeneralEndpoint
import OmegaBound.ADVXXZDegenTrans
import OmegaBound.ADVXXZGeneralAmend27N
import OmegaBound.ADVXXZGeneralCertScaleV22

section
universe u
open OmegaBound Tensor3 Polynomial
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def d7Z {ι : Type*} [DecidableEq ι] (a b : ι) : ℤ :=
  if a = b then 1 else 0

private lemma d7Z_comm {ι : Type*} [DecidableEq ι] (a b : ι) :
    d7Z a b = d7Z b a := by
  unfold d7Z
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

private lemma d7Z_self {ι : Type*} [DecidableEq ι] (a : ι) : d7Z a a = 1 := by
  simp [d7Z]

private lemma sum_d7Z {q : ℕ} (a : Fin q) : ∑ i : Fin q, d7Z a i = 1 := by
  simp [d7Z]

private lemma sum_d7Z_two {q : ℕ} (a b : Fin q) :
    ∑ i : Fin q, d7Z a i * d7Z b i = d7Z a b := by
  rw [Finset.sum_eq_single a]
  · rw [d7Z_comm b a, d7Z_self, one_mul]
  · intro i _ hi
    simp [d7Z, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ a) h

private lemma sum_d7Z_three {q : ℕ} (a b c : Fin q) :
    ∑ i : Fin q, d7Z a i * d7Z b i * d7Z c i = d7Z a b * d7Z a c := by
  rw [Finset.sum_eq_single a]
  · rw [d7Z_comm b a, d7Z_comm c a, d7Z_self, one_mul]
  · intro i _ hi
    simp [d7Z, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ a) h

private lemma sum_C_mul7Z {q m : ℕ} (f : Fin q → ℤ) :
    ∑ i : Fin q, Polynomial.C (f i) * X ^ m =
      Polynomial.C (∑ i : Fin q, f i) * X ^ m := by
  rw [map_sum, Finset.sum_mul]

private lemma sum_split7Z (q : ℕ) (f : CW90.Mul q → Polynomial ℤ) :
    ∑ l : CW90.Mul q, f l =
      (∑ i : Fin q, f (.inl i)) + (f (.inr false) + f (.inr true)) := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_bool]
  ring

private noncomputable def uuZ (q : ℕ) : Polynomial ℤ :=
  1 - Polynomial.C (q : ℤ) * X

private noncomputable def A1Z (q : ℕ) : CW90.Idx7 q → CW90.Mul q → Polynomial ℤ
  | .inl none, .inl _ => X
  | .inl (some j), .inl i => Polynomial.C (d7Z j i) * X ^ 2
  | .inr _, .inl _ => 0
  | .inl none, .inr false => -1
  | .inl (some _), .inr false => -X ^ 2
  | .inr _, .inr false => 0
  | .inl none, .inr true => uuZ q
  | .inl (some _), .inr true => 0
  | .inr _, .inr true => uuZ q * X ^ 3

private noncomputable def A2Z (q : ℕ) : CW90.Idx7 q → CW90.Mul q → Polynomial ℤ
  | .inl none, _ => 1
  | .inl (some j), .inl i => Polynomial.C (d7Z j i) * X
  | .inl (some _), .inr false => X ^ 2
  | .inl (some _), .inr true => 0
  | .inr _, .inl _ => 0
  | .inr _, .inr false => 0
  | .inr _, .inr true => X ^ 3

private noncomputable def BZ (q : ℕ) :
    CW90.Idx7 q → CW90.Idx7 q → CW90.Idx7 q → Polynomial ℤ := fun a b c =>
  match a, b, c with
  | .inl none, .inl (some i), .inl (some j) => Polynomial.C (d7Z i j) - X
  | .inl (some i), .inl none, .inl (some j) => Polynomial.C (d7Z i j) - X
  | .inl (some i), .inl (some j), .inl none => Polynomial.C (d7Z i j) - X
  | .inl (some i), .inl (some j), .inl (some k) =>
      Polynomial.C (d7Z i j) * Polynomial.C (d7Z i k) * X - X ^ 3
  | .inl none, .inl none, .inr _ => uuZ q
  | .inl none, .inr _, .inl none => uuZ q
  | .inr _, .inl none, .inl none => uuZ q
  | .inl none, .inr _, .inr _ => uuZ q * X ^ 3
  | .inr _, .inl none, .inr _ => uuZ q * X ^ 3
  | .inr _, .inr _, .inl none => uuZ q * X ^ 3
  | .inr _, .inr _, .inr _ => uuZ q * X ^ 6
  | _, _, _ => 0

private theorem cwZ_border_identity (q : ℕ) :
    (∀ a b c, ∑ l : CW90.Mul q, A1Z q a l * A2Z q b l * A2Z q c l =
      X ^ 3 * BZ q a b c) ∧
    ∀ a b c, (BZ q a b c).coeff 0 = cwZ q a b c := by
  constructor
  · intro a b c
    rw [sum_split7Z]
    rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
      rcases c with (_ | c) | c <;>
      simp only [A1Z, A2Z, BZ, uuZ, mul_one, one_mul, mul_zero, zero_mul,
        neg_mul, mul_neg]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Polynomial.C_eq_natCast]
      ring
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7Z c i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z c i) * X ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h, sum_C_mul7Z, sum_d7Z, map_one]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7Z b i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z b i) * X ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [h, sum_C_mul7Z, sum_d7Z, map_one]
      ring
    · have h : ∑ i : Fin q, X * (Polynomial.C (d7Z b i) * X) *
          (Polynomial.C (d7Z c i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z b i * d7Z c i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7Z, sum_d7Z_two]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · rw [sum_C_mul7Z, sum_d7Z, map_one]
      ring
    · have h : ∑ i : Fin q, Polynomial.C (d7Z a i) * X ^ 2 *
          (Polynomial.C (d7Z c i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z a i * d7Z c i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7Z, sum_d7Z_two]
      ring
    · simp only [Finset.sum_const_zero]
      ring
    · have h : ∑ i : Fin q, Polynomial.C (d7Z a i) * X ^ 2 *
          (Polynomial.C (d7Z b i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z a i * d7Z b i) * X ^ 3 :=
        Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul]; ring
      rw [h, sum_C_mul7Z, sum_d7Z_two]
      ring
    · have h : ∑ i : Fin q, Polynomial.C (d7Z a i) * X ^ 2 *
            (Polynomial.C (d7Z b i) * X) * (Polynomial.C (d7Z c i) * X) =
          ∑ i : Fin q, Polynomial.C (d7Z a i * d7Z b i * d7Z c i) * X ^ 4 :=
        Finset.sum_congr rfl fun i _ => by
          rw [Polynomial.C_mul, Polynomial.C_mul]
          ring
      rw [h, sum_C_mul7Z, sum_d7Z_three, Polynomial.C_mul]
      ring
    all_goals simp only [Finset.sum_const_zero] <;> ring
  · intro a b c
    rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
      rcases c with (_ | c) | c <;>
      simp only [BZ, cwZ, uuZ, d7Z] <;>
      first | rfl | (split_ifs <;> simp) | simp

private theorem identity_poly_sumZ {r : ℕ}
    (f g h : Fin r → Polynomial ℤ) :
    (∑ a : Fin r, ∑ b : Fin r, ∑ c : Fin r,
      f a * g b * h c * Polynomial.C (Tensor3.identity ℤ r a b c)) =
      ∑ l : Fin r, f l * g l * h l := by
  simp only [Tensor3.identity]
  simp only [apply_ite Polynomial.C, map_one, map_zero, mul_ite, mul_one, mul_zero]
  simp only [ite_and]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem polyDegeneratesAt_cwZ (q : ℕ) :
    PolyDegeneratesAt ℤ 3 (Tensor3.identity ℤ (q + 2)) (cwZ q) := by
  classical
  let e : Fin (q + 2) ≃ CW90.Mul q := Fintype.equivOfCardEq (by simp)
  refine ⟨fun a i => A1Z q a (e i), fun b j => A2Z q b (e j),
    fun c k => A2Z q c (e k), ?_, ?_⟩
  · intro a b c k hk
    rw [identity_poly_sumZ]
    rw [show (∑ l : Fin (q + 2), A1Z q a (e l) * A2Z q b (e l) * A2Z q c (e l)) =
        ∑ l : CW90.Mul q, A1Z q a l * A2Z q b l * A2Z q c l by
          rw [← Equiv.sum_comp e]]
    rw [(cwZ_border_identity q).1 a b c, Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hk]
  · intro a b c
    rw [identity_poly_sumZ]
    rw [show (∑ l : Fin (q + 2), A1Z q a (e l) * A2Z q b (e l) * A2Z q c (e l)) =
        ∑ l : CW90.Mul q, A1Z q a l * A2Z q b l * A2Z q c l by
          rw [← Equiv.sum_comp e]]
    rw [(cwZ_border_identity q).1 a b c, Polynomial.coeff_X_pow_mul']
    simpa using (cwZ_border_identity q).2 a b c

private theorem tensorPower_identity_reindex
    {R : Type*} [CommRing R] (r n : ℕ)
    (e : Fin (r ^ n) ≃ (Fin n → Fin r)) :
    Tensor3.identity R (r ^ n) = fun x y z =>
      tensorPower (Tensor3.identity R r) n (e x) (e y) (e z) := by
  funext x y z
  by_cases hxy : x = y
  · subst y
    by_cases hxz : x = z
    · subst z
      simp [Tensor3.identity, tensorPower]
    · have heq : e x ≠ e z := fun h => hxz (e.injective h)
      have hex : ∃ i, e x i ≠ e z i := by
        by_contra hn
        push_neg at hn
        exact heq (funext hn)
      obtain ⟨i, hi⟩ := hex
      rw [Tensor3.identity, if_neg (by simp [hxz])]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [Tensor3.identity, hi]
  · have heq : e x ≠ e y := fun h => hxy (e.injective h)
    have hex : ∃ i, e x i ≠ e y i := by
      by_contra hn
      push_neg at hn
      exact heq (funext hn)
    obtain ⟨i, hi⟩ := hex
    rw [Tensor3.identity, if_neg (by simp [hxy])]
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [Tensor3.identity, hi]

private theorem polyDegeneratesAt_tensorPower_identityZ
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {r : ℕ} {T : Tensor3 ℤ X Y Z}
    (h : ∃ D, PolyDegeneratesAt ℤ D (Tensor3.identity ℤ r) T) (n : ℕ) :
    ∃ M, PolyDegeneratesAt ℤ M (Tensor3.identity ℤ (r ^ n)) (tensorPower T n) := by
  classical
  obtain ⟨M, hM⟩ := polyDegeneratesAt_tensorPower h n
  let e : Fin (r ^ n) ≃ (Fin n → Fin r) := Fintype.equivOfCardEq (by simp)
  have hs := polyDegeneratesAt_source_equiv hM e e e
  exact ⟨M, polyDegeneratesAt_source_eq hs (tensorPower_identity_reindex r n e)⟩

private theorem polyDegeneratesAt_identity_reflZ (r : ℕ) :
    PolyDegeneratesAt ℤ 0 (Tensor3.identity ℤ r) (Tensor3.identity ℤ r) := by
  classical
  exact polyDegeneratesAt_of_restricts
    (ADVXXZ.restricts_of_sub id id id (fun _ _ _ => rfl))

private theorem copiesZ_tensor_eq (Q : ℕ) (T : ITensor) :
    (copiesZ Q T).tensor = tensorProd (Tensor3.identity ℤ Q) T.tensor := by
  funext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  simp only [copiesZ, famDS, tensorProd, Tensor3.identity, Finset.mem_univ, and_true]
  by_cases h : i = j ∧ j = k
  · simp [h, h.1.trans h.2]
  · have h' : ¬(i = j ∧ i = k) := by
      intro hh
      exact h ⟨hh.1, hh.1.symm.trans hh.2⟩
    simp [h, h']

private theorem source_pool_integral (q w N Q : ℕ) :
    ∃ D, PolyDegeneratesAt ℤ D
      (Tensor3.identity ℤ (Q * (q + 2) ^ (w * N)))
      (copiesZ Q (topZ q w N)).tensor := by
  classical
  have hw := polyDegeneratesAt_tensorPower_identityZ
    (h := ⟨3, polyDegeneratesAt_cwZ q⟩) w
  have hN := polyDegeneratesAt_tensorPower_identityZ (h := hw) N
  have htop : ∃ D, PolyDegeneratesAt ℤ D
      (Tensor3.identity ℤ ((q + 2) ^ (w * N))) (topZ q w N).tensor := by
    change ∃ D, PolyDegeneratesAt ℤ D
      (Tensor3.identity ℤ ((q + 2) ^ (w * N)))
      (tensorPower (tensorPower (cwZ q) w) N)
    rw [pow_mul]
    exact hN
  obtain ⟨D, hD⟩ := htop
  have hprod := polyDegeneratesAt_tensorProd (polyDegeneratesAt_identity_reflZ Q) hD
  have hprod' : PolyDegeneratesAt ℤ D
      (tensorProd (Tensor3.identity ℤ Q) (Tensor3.identity ℤ ((q + 2) ^ (w * N))))
      (tensorProd (Tensor3.identity ℤ Q) (topZ q w N).tensor) := by
    simpa only [Nat.zero_add] using hprod
  have hs := polyDegeneratesAt_source_equiv hprod'
    (finProdFinEquiv (m := Q) (n := (q + 2) ^ (w * N))).symm
    (finProdFinEquiv (m := Q) (n := (q + 2) ^ (w * N))).symm
    (finProdFinEquiv (m := Q) (n := (q + 2) ^ (w * N))).symm
  have hsource : Tensor3.identity ℤ (Q * (q + 2) ^ (w * N)) = fun x y z =>
      tensorProd (Tensor3.identity ℤ Q) (Tensor3.identity ℤ ((q + 2) ^ (w * N)))
        (finProdFinEquiv.symm x) (finProdFinEquiv.symm y) (finProdFinEquiv.symm z) := by
    funext x y z
    rw [identity_tensorProd]
    change Tensor3.identity ℤ (Q * (q + 2) ^ (w * N)) x y z =
      Tensor3.identity ℤ (Q * (q + 2) ^ (w * N))
        (finProdFinEquiv (finProdFinEquiv.symm x))
        (finProdFinEquiv (finProdFinEquiv.symm y))
        (finProdFinEquiv (finProdFinEquiv.symm z))
    rw [finProdFinEquiv.apply_symm_apply, finProdFinEquiv.apply_symm_apply,
      finProdFinEquiv.apply_symm_apply]
  refine ⟨D, polyDegeneratesAt_target_eq (polyDegeneratesAt_source_eq hs hsource) ?_⟩
  exact copiesZ_tensor_eq Q (topZ q w N)

private theorem source_pool_degenerates (F : Type u) [Field F] (q w N Q : ℕ) :
    Degenerates F (Tensor3.identity F (Q * (q + 2) ^ (w * N)))
      ((copiesZ Q (topZ q w N)).over F) := by
  have h := integral_degenerates F
    { X := Fin (Q * (q + 2) ^ (w * N))
      Y := Fin (Q * (q + 2) ^ (w * N))
      Z := Fin (Q * (q + 2) ^ (w * N))
      tensor := Tensor3.identity ℤ (Q * (q + 2) ^ (w * N)) }
    (copiesZ Q (topZ q w N)) (source_pool_integral q w N Q)
  simpa [ITensor.over, map_identity] using h


private theorem one_le_of_rankLE_rect (F : Type u) [Field F]
    {a b c r : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : RankLE (Tensor3.matMul (R := F) a b c) r) : 1 ≤ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exfalso
    have hz := eq_zero_of_rankLE_zero h
    have hone : Tensor3.matMul (R := F) a b c
        (⟨0, ha⟩, ⟨0, hb⟩) (⟨0, hb⟩, ⟨0, hc⟩) (⟨0, hc⟩, ⟨0, ha⟩) = 1 := by
      simp [Tensor3.matMul]
    rw [hz] at hone
    simp at hone
  · exact hr

private theorem isRectExponent_nonneg (F : Type u) [Field F] {κ τ : ℝ}
    (hκ : 0 < κ) (h : IsRectExponent F κ τ) : 0 ≤ τ := by
  obtain ⟨K, hK⟩ := h
  by_contra hτ
  push_neg at hτ
  set p : ℝ := -τ with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have key : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ p ≤ K := by
    intro n hn
    obtain ⟨r, hr, hrK⟩ := hK n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hmidR : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hnR hκ.le
    have hmid : 1 ≤ Nat.ceil ((n : ℝ) ^ κ) := by
      exact_mod_cast hmidR.trans (Nat.le_ceil ((n : ℝ) ^ κ))
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast one_le_of_rankLE_rect F hn hmid hn hr
    have hpowpos : (0 : ℝ) < (n : ℝ) ^ τ := Real.rpow_pos_of_pos hnpos τ
    have hone : (1 : ℝ) ≤ K * (n : ℝ) ^ τ := hr1.trans hrK
    have hdiv : (1 : ℝ) / (n : ℝ) ^ τ ≤ K := (div_le_iff₀ hpowpos).mpr (by
      nlinarith)
    rw [hp, Real.rpow_neg hnpos.le, ← one_div]
    exact hdiv
  have hK1 : (1 : ℝ) ≤ K := by simpa using key 1 le_rfl
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  obtain ⟨m, hm⟩ := exists_nat_gt (K ^ (1 / p))
  set n : ℕ := max m 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hmn : K ^ (1 / p) < (n : ℝ) :=
    hm.trans_le (by exact_mod_cast le_max_left m 1)
  have hbase : (0 : ℝ) ≤ K ^ (1 / p) := Real.rpow_nonneg hK0 _
  have hlt := Real.rpow_lt_rpow hbase hmn hp0
  have hcancel : K < (n : ℝ) ^ p := by
    rwa [← Real.rpow_mul hK0, one_div, inv_mul_cancel₀ (ne_of_gt hp0),
      Real.rpow_one] at hlt
  exact (not_lt_of_ge (key n hn1)) hcancel

private theorem bddBelow_isRectExponent (F : Type u) [Field F] (κ : ℝ) (hκ : 0 < κ) :
    BddBelow {τ | IsRectExponent F κ τ} :=
  ⟨0, fun _ h => isRectExponent_nonneg F hκ h⟩

private theorem omegaRect_le_of_isRectExponent (F : Type u) [Field F]
    {κ τ : ℝ} (hκ : 0 < κ) (h : IsRectExponent F κ τ) : omegaRect F κ ≤ τ := by
  exact csInf_le (bddBelow_isRectExponent F κ hκ) h

private theorem isRectExponent_of_geometric_rank (F : Type u) [Field F]
    (κ θ K L : ℝ) (d A B C : ℕ)
    (hκ : 0 < κ) (hθ : 0 ≤ θ) (hd : 2 ≤ d)
    (hdA : d ≤ A) (hdC : d ≤ C) (hdB : (d : ℝ) ^ κ ≤ (B : ℝ))
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hLθ : L ≤ (d : ℝ) ^ θ)
    (hrank : ∀ j : ℕ, ∃ r : ℕ,
      RankLE (Tensor3.matMul (R := F) (A ^ (j + 1)) (B ^ (j + 1))
        (C ^ (j + 1))) r ∧
      (r : ℝ) ≤ K * L ^ (j + 1)) : IsRectExponent F κ θ := by
  refine ⟨K * L ^ 2, ?_⟩
  intro n hn
  have hex : ∃ p : ℕ, n ≤ d ^ p :=
    ⟨n, Nat.le_of_lt_succ (Nat.lt_succ_of_le
      (Nat.le_of_lt (Nat.lt_pow_self (by omega))))⟩
  let p := Nat.find hex
  have hnp : n ≤ d ^ p := Nat.find_spec hex
  have hpmin : ∀ k, k < p → ¬ n ≤ d ^ k := fun k hk => Nat.find_min hex hk
  obtain ⟨r, hr, hrr⟩ := hrank p
  refine ⟨r, ?_, ?_⟩
  · have hA1 : 1 ≤ A := le_trans (by omega) hdA
    have hC1 : 1 ≤ C := le_trans (by omega) hdC
    have hfirst : n ≤ A ^ (p + 1) := by
      calc n ≤ d ^ p := hnp
        _ ≤ A ^ p := Nat.pow_le_pow_left hdA p
        _ ≤ A ^ (p + 1) := Nat.pow_le_pow_right hA1 (by omega)
    have hthird : n ≤ C ^ (p + 1) := by
      calc n ≤ d ^ p := hnp
        _ ≤ C ^ p := Nat.pow_le_pow_left hdC p
        _ ≤ C ^ (p + 1) := Nat.pow_le_pow_right hC1 (by omega)
    have hBR : (0 : ℝ) ≤ (B : ℝ) := by positivity
    have hmidReal : (n : ℝ) ^ κ ≤ ((B ^ (p + 1) : ℕ) : ℝ) := by
      have hnpR : (n : ℝ) ≤ ((d ^ p : ℕ) : ℝ) := by exact_mod_cast hnp
      have hpow := Real.rpow_le_rpow (by positivity) hnpR hκ.le
      have hcomm : (((d ^ p : ℕ) : ℝ)) ^ κ = ((d : ℝ) ^ κ) ^ p := by
        push_cast
        exact rpow_pow_comm (by positivity) p κ
      have hBp : ((d : ℝ) ^ κ) ^ p ≤ (B : ℝ) ^ p :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) κ) hdB p
      have hB1 : 1 ≤ B := by
        by_contra h
        have hB0 : B = 0 := by omega
        rw [hB0, Nat.cast_zero] at hdB
        exact (not_le_of_gt (Real.rpow_pos_of_pos (by positivity) κ)) hdB
      have hBstep : (B : ℝ) ^ p ≤ (B : ℝ) ^ (p + 1) := by
        exact_mod_cast Nat.pow_le_pow_right hB1 (show p ≤ p + 1 by omega)
      rw [hcomm] at hpow
      push_cast
      exact hpow.trans (hBp.trans hBstep)
    have hmid : Nat.ceil ((n : ℝ) ^ κ) ≤ B ^ (p + 1) := Nat.ceil_le.mpr hmidReal
    exact OmegaBound.RankLE.mono
      (matMul_restricts_of_le n (Nat.ceil ((n : ℝ) ^ κ)) n
        (A ^ (p + 1)) (B ^ (p + 1)) (C ^ (p + 1)) hfirst hmid hthird) hr
  · rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · have hn_le : n ≤ 1 := by simpa only [hp0, pow_zero] using hnp
      have hn_eq : n = 1 := by omega
      subst n
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      have hL0 : 0 ≤ L := zero_le_one.trans hL
      have hrr' : (r : ℝ) ≤ K * L := by simpa only [hp0, zero_add, pow_one] using hrr
      calc (r : ℝ) ≤ K * L := hrr'
        _ ≤ K * L ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hK
          rw [pow_two]
          calc L = L * 1 := by ring
            _ ≤ L * L := mul_le_mul_of_nonneg_left hL hL0
    · have hprev : d ^ (p - 1) < n := by
        push_neg at hpmin
        exact hpmin (p - 1) (by omega)
      have hprevR : ((d ^ (p - 1) : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hprev
      have hmono := Real.rpow_le_rpow (by positivity) hprevR.le hθ
      push_cast at hmono
      have hpowL : L ^ (p - 1) ≤ ((d : ℝ) ^ (p - 1)) ^ θ := by
        calc L ^ (p - 1) ≤ ((d : ℝ) ^ θ) ^ (p - 1) :=
              pow_le_pow_left₀ (zero_le_one.trans hL) hLθ (p - 1)
          _ = ((d : ℝ) ^ (p - 1)) ^ θ := by
              symm
              exact rpow_pow_comm (by positivity) (p - 1) θ
      have hsplit : L ^ (p + 1) = L ^ 2 * L ^ (p - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      calc (r : ℝ) ≤ K * L ^ (p + 1) := hrr
        _ = K * (L ^ 2 * L ^ (p - 1)) := by rw [hsplit]
        _ ≤ K * (L ^ 2 * ((n : ℝ) ^ θ)) := by
          gcongr
          exact hpowL.trans hmono
        _ = K * L ^ 2 * (n : ℝ) ^ θ := by ring

private theorem polyDegeneratesAt_tpow_identityF (F : Type u) [Field F]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (D r : ℕ) (T : Tensor3 F X Y Z)
    (h : PolyDegeneratesAt F D (Tensor3.identity F r) T) :
    ∀ n : ℕ, PolyDegeneratesAt F (n * D) (Tensor3.identity F (r ^ n)) (tpow T n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_, ?_⟩
      · intro x y z k hk
        omega
      · intro x y z
        rcases x with ⟨⟩
        rcases y with ⟨⟩
        rcases z with ⟨⟩
        simp [Tensor3.identity, tpow]
        rw [show ({x ∈ ({0} : Finset (Fin 1)) | (0 : Fin 1) = x}).card = 1 by
          decide +kernel]
        norm_num
  | succ n ih =>
      have hp := polyDegeneratesAt_tensorProd ih h
      let e : Fin (r ^ n * r) ≃ Fin (r ^ n) × Fin r :=
        (finProdFinEquiv (m := r ^ n) (n := r)).symm
      have hs := polyDegeneratesAt_source_equiv hp e e e
      have he : Tensor3.identity F (r ^ n * r) = fun x y z =>
          tensorProd (Tensor3.identity F (r ^ n)) (Tensor3.identity F r)
            (e x) (e y) (e z) := by
        funext x y z
        rw [identity_tensorProd]
        change Tensor3.identity F (r ^ n * r) x y z =
          Tensor3.identity F (r ^ n * r)
            (e.symm (e x)) (e.symm (e y)) (e.symm (e z))
        rw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
      have hs' := polyDegeneratesAt_source_eq hs he
      simpa only [Nat.succ_mul, pow_succ, tpow_succ] using hs'

private theorem blockDiag_tensorProd_bothF (F : Type u) [Field F]
    {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (m n : ℕ) (S : Tensor3 F X Y Z) (T : Tensor3 F X' Y' Z') :
    blockDiag (Fin (m * n)) (tensorProd S T) ≤ₜ
      tensorProd (blockDiag (Fin m) S) (blockDiag (Fin n) T) := by
  have h₁ := blockDiag_mul_le (tensorProd S T) m n
  have h₂ : blockDiag (Fin n) (tensorProd S T) ≤ₜ
      tensorProd S (blockDiag (Fin n) T) := blockDiag_tensorProd_le' n T S
  have h₃ := blockDiag_mono (R := F) m h₂
  have h₄ := blockDiag_tensorProd_le (ι := Fin m) S (blockDiag (Fin n) T)
  exact Tensor3.Restricts.trans h₁ (Tensor3.Restricts.trans h₃ h₄)

private theorem blockDiag_power_matMulF (F : Type u) [Field F]
    (A B C V : ℕ) : ∀ t : ℕ,
    blockDiag (Fin (V ^ t))
      (Tensor3.matMul (R := F) (A ^ t) (B ^ t) (C ^ t)) ≤ₜ
      tpow (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) t := by
  intro t
  induction t with
  | zero =>
      show blockDiag (Fin 1) (Tensor3.matMul (R := F) 1 1 1) ≤ₜ
        tpow (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) 0
      refine Restricts.of_eq (precomp_restricts
        (fun _ => (PUnit.unit : TIdx (Fin V × (Fin A × Fin B)) 0))
        (fun _ => (PUnit.unit : TIdx (Fin V × (Fin B × Fin C)) 0))
        (fun _ => (PUnit.unit : TIdx (Fin V × (Fin C × Fin A)) 0))
        (tpow (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) 0)) ?_
      funext x y z
      obtain ⟨i, a⟩ := x
      obtain ⟨j, b⟩ := y
      obtain ⟨k, c⟩ := z
      rw [blockDiag_apply, if_pos ⟨Subsingleton.elim i j, Subsingleton.elim i k⟩]
      exact matMul_one_apply a b c
  | succ t ih =>
      have hmm : Tensor3.matMul (R := F) (A ^ (t + 1)) (B ^ (t + 1)) (C ^ (t + 1))
          ≤ₜ tensorProd (Tensor3.matMul (R := F) (A ^ t) (B ^ t) (C ^ t))
            (Tensor3.matMul (R := F) A B C) :=
        matMul_congr_le (matMul_restricts_tensorProd (A ^ t) (B ^ t) (C ^ t) A B C)
          (by ring) (by ring) (by ring)
      have h₁ := blockDiag_mono (R := F) (V ^ t * V) hmm
      have h₂ := blockDiag_tensorProd_bothF F (V ^ t) V
        (Tensor3.matMul (R := F) (A ^ t) (B ^ t) (C ^ t))
        (Tensor3.matMul (R := F) A B C)
      have h₃ := OmegaBound.Restricts.tensorProd_right ih
        (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C))
      simpa only [pow_succ, tpow_succ] using
        (Tensor3.Restricts.trans h₁ (Tensor3.Restricts.trans h₂ h₃))

private theorem exists_ceil_mul_rect (r M : ℕ) (hM : 1 ≤ M) :
    ∃ K : ℕ, r ≤ K * M ∧ (K : ℝ) * (M : ℝ) ≤ (r : ℝ) + (M : ℝ) := by
  refine ⟨(r + M - 1) / M, ?_, ?_⟩
  · have h₁ : M * ((r + M - 1) / M) + (r + M - 1) % M = r + M - 1 :=
      Nat.div_add_mod _ _
    have h₂ : (r + M - 1) % M < M := Nat.mod_lt _ hM
    have h₃ : r ≤ M * ((r + M - 1) / M) := by
      generalize hp : M * ((r + M - 1) / M) = p at h₁
      omega
    rw [Nat.mul_comm]
    exact h₃
  · have h₁ : (r + M - 1) / M * M ≤ r + M - 1 := Nat.div_mul_le_self _ _
    have h₂ : (r + M - 1) / M * M ≤ r + M := by omega
    exact_mod_cast h₂

private theorem rankLE_step_rect (F : Type u) [Field F]
    {A B C M s r K : ℕ} (hr : r ≤ K * M)
    (hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) s)
    {j : ℕ} (h : RankLE
      (Tensor3.matMul (R := F) (A ^ j) (B ^ j) (C ^ j)) r) :
    RankLE (Tensor3.matMul (R := F) (A ^ (j + 1)) (B ^ (j + 1))
      (C ^ (j + 1))) (K * s) := by
  have h₁ : Tensor3.matMul (R := F) (A ^ (j + 1)) (B ^ (j + 1)) (C ^ (j + 1))
      ≤ₜ tensorProd (Tensor3.matMul (R := F) (A ^ j) (B ^ j) (C ^ j))
        (Tensor3.matMul (R := F) A B C) :=
    matMul_congr_le (matMul_restricts_tensorProd (A ^ j) (B ^ j) (C ^ j) A B C)
      (by ring) (by ring) (by ring)
  have h₂ : tensorProd (Tensor3.matMul (R := F) (A ^ j) (B ^ j) (C ^ j))
      (Tensor3.matMul (R := F) A B C) ≤ₜ
      tensorProd (Tensor3.identity F r) (Tensor3.matMul (R := F) A B C) :=
    OmegaBound.Restricts.tensorProd_right h _
  have h₃ : blockDiag (Fin r) (Tensor3.matMul (R := F) A B C) ≤ₜ
      blockDiag (Fin (K * M)) (Tensor3.matMul (R := F) A B C) :=
    blockDiag_le_of_injective _ (Fin.castLE_injective hr)
  have h₄ := blockDiag_mul_le (Tensor3.matMul (R := F) A B C) K M
  have h₅ : RankLE (blockDiag (Fin K)
      (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C))) (K * s) := hblk.blockDiag K
  refine OmegaBound.RankLE.mono (Tensor3.Restricts.trans h₁
    (Tensor3.Restricts.trans h₂ ?_)) h₅
  rw [← blockDiag_eq_tensorProd]
  exact Tensor3.Restricts.trans h₃ h₄

private theorem rankLE_geometric_of_blockDiag (F : Type u) [Field F]
    {A B C M s : ℕ} (hM : 1 ≤ M)
    (hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) s) :
    ∀ j : ℕ, ∃ r : ℕ,
      RankLE (Tensor3.matMul (R := F) (A ^ (j + 1)) (B ^ (j + 1))
        (C ^ (j + 1))) r ∧
      (r : ℝ) ≤ (M : ℝ) * (1 + (s : ℝ) / (M : ℝ)) ^ (j + 1) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  intro j
  induction j with
  | zero =>
      refine ⟨s, ?_, ?_⟩
      · have hs : Tensor3.matMul (R := F) A B C ≤ₜ
            blockDiag (Fin M) (Tensor3.matMul (R := F) A B C) :=
          restricts_blockDiag _ ⟨0, hM⟩
        exact (OmegaBound.RankLE.mono hs hblk).congr_matMul (by ring) (by ring) (by ring)
      · rw [pow_one, mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hMpos)]
        linarith
  | succ j ih =>
      obtain ⟨r, hr, hrb⟩ := ih
      obtain ⟨K, hK₁, hK₂⟩ := exists_ceil_mul_rect r M hM
      refine ⟨K * s, rankLE_step_rect F hK₁ hblk hr, ?_⟩
      set P : ℝ := (1 + (s : ℝ) / (M : ℝ)) ^ (j + 1) with hP
      have hP₁ : 1 + (s : ℝ) / (M : ℝ) ≤ P := by
        rw [hP]
        exact le_self_pow₀ (by
          have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
          have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith [div_nonneg hs0 hM0]) (by omega)
      have hMP : (s : ℝ) ≤ (M : ℝ) * P := by
        have ht : (M : ℝ) * (1 + (s : ℝ) / (M : ℝ)) ≤ (M : ℝ) * P :=
          mul_le_mul_of_nonneg_left hP₁ hMpos.le
        rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hMpos)] at ht
        linarith
      have hKb : (K : ℝ) ≤ (r : ℝ) / (M : ℝ) + 1 := by
        rw [div_add' _ _ _ (ne_of_gt hMpos), le_div_iff₀ hMpos]
        linarith [hK₂]
      have hrP : (r : ℝ) / (M : ℝ) ≤ P := by
        rw [div_le_iff₀ hMpos]
        calc (r : ℝ) ≤ (M : ℝ) * P := hrb
          _ = P * (M : ℝ) := by ring
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
      calc ((K * s : ℕ) : ℝ) = (K : ℝ) * (s : ℝ) := by push_cast; ring
        _ ≤ ((r : ℝ) / (M : ℝ) + 1) * (s : ℝ) :=
          mul_le_mul_of_nonneg_right hKb hs0
        _ ≤ (P + 1) * (s : ℝ) := by nlinarith [hrP, hs0]
        _ ≤ (M : ℝ) * (1 + (s : ℝ) / (M : ℝ)) ^ (j + 1 + 1) := by
          rw [pow_succ, ← hP]
          have ht : (M : ℝ) * (P * (1 + (s : ℝ) / (M : ℝ))) =
              (M : ℝ) * P + P * (s : ℝ) := by field_simp
          rw [ht]
          nlinarith [hMP, hs0]

private theorem exists_rect_overhead_scale (D : ℕ) {θ gap dlog : ℝ}
    (hθ : 0 < θ) (hgap : 0 < gap) (hdlog : 0 < dlog) :
    ∃ t : ℕ, 1 ≤ t ∧ Real.log 2 < (t : ℝ) * dlog ∧
      Real.log 2 ≤ θ * ((t : ℝ) * dlog - Real.log 2) ∧
      Real.log 2 + 2 * Real.log ((t * D + 1 : ℕ) : ℝ) + θ * Real.log 2 ≤
        gap * (t : ℝ) := by
  set K : ℝ := (1 + θ) * Real.log 2 + 4 * Real.sqrt ((D : ℝ) + 1) with hKdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < K := by
    rw [hKdef]
    have hsqrt : 0 ≤ Real.sqrt ((D : ℝ) + 1) := Real.sqrt_nonneg _
    nlinarith
  obtain ⟨t, ht⟩ := exists_nat_gt
    (max ((K / gap) ^ 2 + 1)
      (max (Real.log 2 / dlog + 1)
        ((1 + θ) * Real.log 2 / (θ * dlog) + 1)))
  have htK : (K / gap) ^ 2 + 1 < (t : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) ht
  have htlog : Real.log 2 / dlog + 1 < (t : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htθ : (1 + θ) * Real.log 2 / (θ * dlog) + 1 < (t : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    interval_cases t
    nlinarith [sq_nonneg (K / gap)]
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have htlog' : Real.log 2 < (t : ℝ) * dlog := by
    have : Real.log 2 / dlog < (t : ℝ) := by linarith
    rwa [div_lt_iff₀ hdlog] at this
  have htθ' : Real.log 2 ≤ θ * ((t : ℝ) * dlog - Real.log 2) := by
    have hden : 0 < θ * dlog := mul_pos hθ hdlog
    have h := show (1 + θ) * Real.log 2 / (θ * dlog) < (t : ℝ) by linarith
    rw [div_lt_iff₀ hden] at h
    nlinarith
  have hP : Real.log ((t * D + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (((D : ℝ) + 1) * (t : ℝ)) := by
    refine (log_le_two_sqrt (by positivity)).trans ?_
    have hle : ((t * D + 1 : ℕ) : ℝ) ≤ ((D : ℝ) + 1) * (t : ℝ) := by
      push_cast
      nlinarith [show (1 : ℝ) ≤ (t : ℝ) by exact_mod_cast ht1,
        Nat.cast_nonneg (α := ℝ) D]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)
  have hsqrt_mul : Real.sqrt (((D : ℝ) + 1) * (t : ℝ)) =
      Real.sqrt ((D : ℝ) + 1) * Real.sqrt (t : ℝ) :=
    Real.sqrt_mul (by positivity) _
  rw [hsqrt_mul] at hP
  have hsqrt_t_one : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast ht1)
  have hover : Real.log 2 + 2 * Real.log ((t * D + 1 : ℕ) : ℝ) +
      θ * Real.log 2 ≤ K * Real.sqrt (t : ℝ) := by
    rw [hKdef]
    have hθone : 0 ≤ 1 + θ := by linarith
    have hlogpart : (1 + θ) * Real.log 2 ≤
        ((1 + θ) * Real.log 2) * Real.sqrt (t : ℝ) :=
      calc (1 + θ) * Real.log 2 = ((1 + θ) * Real.log 2) * 1 := by ring
        _ ≤ ((1 + θ) * Real.log 2) * Real.sqrt (t : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_t_one (mul_nonneg hθone hlog2.le)
    nlinarith [hP, Real.sqrt_nonneg ((D : ℝ) + 1), Real.sqrt_nonneg (t : ℝ)]
  have hsqrt_t : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  have hKt : K / Real.sqrt (t : ℝ) < gap := by
    have hsq : (K / gap) ^ 2 < (t : ℝ) := by linarith
    have hsqrt_lt : K / gap < Real.sqrt (t : ℝ) := by
      have h := Real.sqrt_lt_sqrt (by positivity) hsq
      rwa [Real.sqrt_sq (by positivity)] at h
    rw [div_lt_iff₀ hgap] at hsqrt_lt
    rw [div_lt_iff₀ hsqrt_t]
    simpa only [mul_comm] using hsqrt_lt
  have hmul : K * Real.sqrt (t : ℝ) ≤ gap * (t : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hKt.le htpos.le
    have hsqrt_sq : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) :=
      Real.mul_self_sqrt htpos.le
    calc K * Real.sqrt (t : ℝ) =
          K / Real.sqrt (t : ℝ) *
            (Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ)) := by
          field_simp [ne_of_gt hsqrt_t]
        _ = K / Real.sqrt (t : ℝ) * (t : ℝ) := by rw [hsqrt_sq]
        _ ≤ gap * (t : ℝ) := hm
  exact ⟨t, ht1, htlog', htθ', hover.trans hmul⟩

private theorem floor_exp_rect_dimensions {κ dlog : ℝ} {t A B C : ℕ}
    (hκ : 0 < κ) (hdlog : 0 < dlog) (htlog : Real.log 2 < (t : ℝ) * dlog)
    (hA : dlog ≤ Real.log (A : ℝ))
    (hB : κ * dlog ≤ Real.log (B : ℝ))
    (hC : dlog ≤ Real.log (C : ℝ)) :
    let d := Nat.floor (Real.exp ((t : ℝ) * dlog))
    2 ≤ d ∧ d ≤ A ^ t ∧ d ≤ C ^ t ∧ (d : ℝ) ^ κ ≤ (B ^ t : ℕ) := by
  dsimp only
  set E : ℝ := Real.exp ((t : ℝ) * dlog) with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  have h2E : (2 : ℝ) < E := by
    rw [hE, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_lt_exp]
    exact htlog
  have hfloor_le : ((Nat.floor E : ℕ) : ℝ) ≤ E := Nat.floor_le hEpos.le
  have htwo : 2 ≤ Nat.floor E := by
    have hf : E < (Nat.floor E : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one E
    by_contra h
    have : Nat.floor E ≤ 1 := by omega
    exact (not_lt_of_ge (show (Nat.floor E : ℝ) + 1 ≤ 2 by exact_mod_cast Nat.succ_le_succ this))
      (lt_of_lt_of_le h2E hf.le)
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hApos : (0 : ℝ) < (A : ℝ) := by
    by_contra h
    have hAz : A = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hAp
      exact h (by exact_mod_cast hAp)
    rw [hAz, Nat.cast_zero, Real.log_zero] at hA
    nlinarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    by_contra h
    have hBz : B = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hBp
      exact h (by exact_mod_cast hBp)
    rw [hBz, Nat.cast_zero, Real.log_zero] at hB
    nlinarith [mul_pos hκ hdlog]
  have hCpos : (0 : ℝ) < (C : ℝ) := by
    by_contra h
    have hCz : C = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hCp
      exact h (by exact_mod_cast hCp)
    rw [hCz, Nat.cast_zero, Real.log_zero] at hC
    nlinarith
  have hEA : E ≤ ((A ^ t : ℕ) : ℝ) := by
    rw [hE, Nat.cast_pow]
    calc Real.exp ((t : ℝ) * dlog) ≤ Real.exp ((t : ℝ) * Real.log (A : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA ht0)
      _ = Real.exp (Real.log (A : ℝ)) ^ t := Real.exp_nat_mul _ _
      _ = (A : ℝ) ^ t := by rw [Real.exp_log hApos]
  have hEC : E ≤ ((C ^ t : ℕ) : ℝ) := by
    rw [hE, Nat.cast_pow]
    calc Real.exp ((t : ℝ) * dlog) ≤ Real.exp ((t : ℝ) * Real.log (C : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hC ht0)
      _ = Real.exp (Real.log (C : ℝ)) ^ t := Real.exp_nat_mul _ _
      _ = (C : ℝ) ^ t := by rw [Real.exp_log hCpos]
  have hdA : Nat.floor E ≤ A ^ t := by exact_mod_cast hfloor_le.trans hEA
  have hdC : Nat.floor E ≤ C ^ t := by exact_mod_cast hfloor_le.trans hEC
  have hpow : ((Nat.floor E : ℕ) : ℝ) ^ κ ≤ E ^ κ :=
    Real.rpow_le_rpow (by positivity) hfloor_le hκ.le
  have hEB : E ^ κ ≤ ((B ^ t : ℕ) : ℝ) := by
    rw [hE, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Nat.cast_pow]
    calc Real.exp ((t : ℝ) * dlog * κ) ≤
          Real.exp ((t : ℝ) * Real.log (B : ℝ)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hB ht0])
      _ = Real.exp (Real.log (B : ℝ)) ^ t := Real.exp_nat_mul _ _
      _ = (B : ℝ) ^ t := by rw [Real.exp_log hBpos]
  exact ⟨htwo, hdA, hdC, hpow.trans hEB⟩

private theorem log_floor_exp_lower {x : ℝ} (hx : Real.log 2 < x) :
    x - Real.log 2 ≤ Real.log ((Nat.floor (Real.exp x) : ℕ) : ℝ) := by
  set d : ℕ := Nat.floor (Real.exp x) with hd
  have hexp : (0 : ℝ) < Real.exp x := Real.exp_pos _
  have h2 : (2 : ℝ) < Real.exp x := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_lt_exp]
    exact hx
  have hd2 : 2 ≤ d := by
    have hf : Real.exp x < (d : ℝ) + 1 := by
      rw [hd]
      exact_mod_cast Nat.lt_floor_add_one (Real.exp x)
    by_contra h
    have hd1 : d ≤ 1 := by omega
    have : (d : ℝ) + 1 ≤ 2 := by exact_mod_cast Nat.succ_le_succ hd1
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hhalf : Real.exp x / 2 ≤ (d : ℝ) := by
    have hf : Real.exp x < (d : ℝ) + 1 := by
      rw [hd]
      exact_mod_cast Nat.lt_floor_add_one (Real.exp x)
    have hone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp x / 2) hhalf
  rw [Real.log_div (ne_of_gt hexp) (by norm_num), Real.log_exp] at hlog
  exact hlog

private theorem omegaRect_le_of_strict_blockDiag (F : Type u) [Field F]
    (κ θ dlog : ℝ) (S V A B C : ℕ)
    (hκ : 0 < κ) (hθ : 0 < θ) (hdlog : 0 < dlog)
    (hS : 1 ≤ S) (hV : 1 ≤ V)
    (hA : dlog ≤ Real.log (A : ℝ))
    (hB : κ * dlog ≤ Real.log (B : ℝ))
    (hC : dlog ≤ Real.log (C : ℝ))
    (hstrict : Real.log (S : ℝ) - Real.log (V : ℝ) < θ * dlog)
    (hdeg : Degenerates F (Tensor3.identity F S)
      (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C))) :
    omegaRect F κ ≤ θ := by
  classical
  obtain ⟨D, hD⟩ := CW90Eight.exists_degeneratesAt hdeg
  set gap : ℝ := θ * dlog - (Real.log (S : ℝ) - Real.log (V : ℝ)) with hgapdef
  have hgap : 0 < gap := by rw [hgapdef]; linarith
  obtain ⟨t, ht, htlog, htθfloor, hover⟩ :=
    exists_rect_overhead_scale D hθ hgap hdlog
  have hpow := polyDegeneratesAt_tpow_identityF F D S
    (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) hD t
  set srk : ℕ := S ^ t * (t * D + 1) ^ 2 with hsrk
  have hrankPow : RankLE
      (tpow (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) t) srk := by
    have hr := rankLE_of_degeneratesAt_identity F (t * D) (S ^ t)
      (tpow (blockDiag (Fin V) (Tensor3.matMul (R := F) A B C)) t) hpow
    simpa only [hsrk] using hr
  have hblk : RankLE
      (blockDiag (Fin (V ^ t))
        (Tensor3.matMul (R := F) (A ^ t) (B ^ t) (C ^ t))) srk :=
    OmegaBound.RankLE.mono (blockDiag_power_matMulF F A B C V t) hrankPow
  set M : ℕ := V ^ t with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.one_le_pow t V hV
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  set L : ℝ := 1 + (srk : ℝ) / (M : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have : (0 : ℝ) ≤ (srk : ℝ) / (M : ℝ) := div_nonneg (by positivity) hMpos.le
    linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hgeorank : ∀ j : ℕ, ∃ r : ℕ,
      RankLE (Tensor3.matMul (R := F) ((A ^ t) ^ (j + 1))
        ((B ^ t) ^ (j + 1)) ((C ^ t) ^ (j + 1))) r ∧
      (r : ℝ) ≤ (M : ℝ) * L ^ (j + 1) := by
    simpa only [hM, hL] using
      (rankLE_geometric_of_blockDiag F hM1 (by simpa only [hM] using hblk))
  let d : ℕ := Nat.floor (Real.exp ((t : ℝ) * dlog))
  have hdims : 2 ≤ d ∧ d ≤ A ^ t ∧ d ≤ C ^ t ∧
      (d : ℝ) ^ κ ≤ ((B ^ t : ℕ) : ℝ) := by
    exact floor_exp_rect_dimensions hκ hdlog htlog hA hB hC
  have hd2 : 2 ≤ d := hdims.1
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsrk1 : 1 ≤ srk := by
    have hAt1 : 1 ≤ A ^ t := le_trans (by omega) hdims.2.1
    have hCt1 : 1 ≤ C ^ t := le_trans (by omega) hdims.2.2.1
    have hBtpos : 0 < B ^ t := by
      have hdκpos : 0 < (d : ℝ) ^ κ := Real.rpow_pos_of_pos hdpos κ
      have : (0 : ℝ) < ((B ^ t : ℕ) : ℝ) :=
        lt_of_lt_of_le hdκpos hdims.2.2.2
      exact_mod_cast this
    have hBt1 : 1 ≤ B ^ t := hBtpos
    exact one_le_of_rankLE_rect F hAt1 hBt1 hCt1
      (OmegaBound.RankLE.mono (restricts_blockDiag _ (⟨0, hM1⟩ : Fin M))
        (by simpa only [hM] using hblk))
  have hsrkpos : (0 : ℝ) < (srk : ℝ) := by exact_mod_cast hsrk1
  set Z : ℝ := (srk : ℝ) / (M : ℝ) with hZ
  have hZpos : 0 < Z := by rw [hZ]; positivity
  set U : ℝ := (t : ℝ) * (Real.log (S : ℝ) - Real.log (V : ℝ)) +
      2 * Real.log ((t * D + 1 : ℕ) : ℝ) with hU
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hlogZ : Real.log Z = U := by
    rw [hZ, Real.log_div (ne_of_gt hsrkpos) (ne_of_gt hMpos), hsrk, hM,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow, hU]
    push_cast
    ring
  have hUbound : Real.log 2 + U ≤ θ * ((t : ℝ) * dlog - Real.log 2) := by
    rw [hU]
    rw [hgapdef] at hover
    nlinarith
  have hlogd : (t : ℝ) * dlog - Real.log 2 ≤ Real.log (d : ℝ) := by
    exact log_floor_exp_lower htlog
  have hlogL : Real.log L ≤ θ * Real.log (d : ℝ) := by
    by_cases hU0 : 0 ≤ U
    · have hZexp : Z = Real.exp U := by
        calc Z = Real.exp (Real.log Z) := (Real.exp_log hZpos).symm
          _ = Real.exp U := by rw [hlogZ]
      have hexp1 : 1 ≤ Real.exp U := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hU0
      have hLexp : L ≤ 2 * Real.exp U := by
        rw [hL, hZexp]
        linarith
      have hlogLe : Real.log L ≤ Real.log 2 + U := by
        calc Real.log L ≤ Real.log (2 * Real.exp U) :=
              Real.log_le_log hLpos hLexp
          _ = Real.log 2 + U := by
              rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos U)), Real.log_exp]
      exact hlogLe.trans (hUbound.trans
        (mul_le_mul_of_nonneg_left hlogd hθ.le))
    · have hZ1 : Z < 1 := (Real.log_neg_iff hZpos).mp (by rw [hlogZ]; linarith)
      have hL2 : L ≤ 2 := by rw [hL]; linarith
      have hlogL2 : Real.log L ≤ Real.log 2 := Real.log_le_log hLpos hL2
      exact hlogL2.trans (htθfloor.trans
        (mul_le_mul_of_nonneg_left hlogd hθ.le))
  have hLθ : L ≤ (d : ℝ) ^ θ := by
    rw [Real.rpow_def_of_pos hdpos]
    calc L = Real.exp (Real.log L) := (Real.exp_log hLpos).symm
      _ ≤ Real.exp (θ * Real.log (d : ℝ)) := Real.exp_le_exp.mpr hlogL
      _ = Real.exp (Real.log (d : ℝ) * θ) := by congr 1; ring
  apply omegaRect_le_of_isRectExponent F hκ
  exact isRectExponent_of_geometric_rank F κ θ (M : ℝ) L d
    (A ^ t) (B ^ t) (C ^ t) hκ hθ.le hd2 hdims.2.1 hdims.2.2.1
    hdims.2.2.2 (by positivity) hL1 hLθ hgeorank

private theorem famDS_univ_const_eq_blockDiag (F : Type u) [Field F]
    (V A B C : ℕ) :
    famDS Finset.univ (fun _ : Fin V => Tensor3.matMul (R := F) A B C) =
      blockDiag (Fin V) (Tensor3.matMul (R := F) A B C) := by
  funext x y z
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  obtain ⟨k, c⟩ := z
  simp only [famDS, blockDiag, Finset.mem_univ, and_true]
  by_cases h : i = j ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(i = j ∧ i = k) := by
      intro hh
      exact h ⟨hh.1, hh.1.symm.trans hh.2⟩
    rw [if_neg h, if_neg h']

set_option maxHeartbeats 8000000 in
theorem numerical_limit (F : Type u) [Field F]
    (C : Certificate) (hC : AdmissibleAt C) (Q V a b c : ℚ → ℕ → ℕ)
    (R x y z τ : ℝ) (hτ : 0 ≤ τ)
    (hQ : ∀ ε, 0 < ε → (∀ m, 1 ≤ Q ε m) ∧
      Sublinear (outerN C) (fun m => Real.log (Q ε m:ℝ)))
    (hprod : ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
      Degenerates F ((copiesZ (Q ε m) (topZ C.q C.width (outerN C m))).over F)
        (famDS Finset.univ (fun _ : Fin (V ε m) =>
          Tensor3.matMul (R := F) (a ε m) (b ε m) (c ε m))))
    (hV : LowerRate (outerN C) V R) (ha : LowerRate (outerN C) a x)
    (hb : LowerRate (outerN C) b y) (hc : LowerRate (outerN C) c z)
    (hgrowth : 0 < min x (min (y/C.kappa) z))
    (hfit : C.width*Real.log (C.q+2:ℝ) ≤
      R + τ*min x (min (y/C.kappa) z)) :
  omegaRect F C.kappa ≤ τ := by
  classical
  refine le_of_forall_pos_le_add ?_
  intro η hη
  set g : ℝ := min x (min (y / C.kappa) z) with hg
  have hgpos : 0 < g := by simpa only [hg] using hgrowth
  have htheta : 0 < τ + η := by linarith
  set denom : ℝ := 4 * (τ + η + 2) with hdenom
  have hdenompos : 0 < denom := by rw [hdenom]; positivity
  set ρ : ℝ := η * g / denom with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hηdenom : η < denom := by rw [hdenom]; nlinarith
  have hρg : ρ < g := by
    rw [hρ]
    calc η * g / denom < denom * g / denom :=
          div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hηdenom hgpos) hdenompos
      _ = g := by field_simp
  have hmargin : τ * g + 2 * ρ < (τ + η) * (g - ρ) := by
    have hid : denom * ρ = η * g := by
      rw [hρ]
      field_simp
    rw [hdenom] at hid
    nlinarith [mul_pos hη hgpos]
  obtain ⟨εV, hεV, hVevent⟩ := hV ρ hρpos
  obtain ⟨εa, hεa, haevent⟩ := ha ρ hρpos
  obtain ⟨εb, hεb, hbevent⟩ := hb (C.kappa * ρ) (mul_pos hC.kappa_pos hρpos)
  obtain ⟨εc, hεc, hcevent⟩ := hc ρ hρpos
  let ε : ℚ := min εV (min εa (min εb εc))
  have hε : 0 < ε := by
    dsimp only [ε]
    simp only [lt_min_iff]
    exact ⟨hεV, hεa, hεb, hεc⟩
  have hεVle : ε ≤ εV := by dsimp only [ε]; exact min_le_left _ _
  have hεale : ε ≤ εa := by
    dsimp only [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεble : ε ≤ εb := by
    dsimp only [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεcle : ε ≤ εc := by
    dsimp only [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨MV, hMV⟩ := hVevent ε hε hεVle
  obtain ⟨Ma, hMa⟩ := haevent ε hε hεale
  obtain ⟨Mb, hMb⟩ := hbevent ε hε hεble
  obtain ⟨Mc, hMc⟩ := hcevent ε hε hεcle
  obtain ⟨Mprod, hMprod⟩ := hprod ε hε
  obtain ⟨hQone, hQsub⟩ := hQ ε hε
  obtain ⟨Mq, hMq⟩ := hQsub ρ hρpos
  let m : ℕ := 1 + MV + Ma + Mb + Mc + Mprod + Mq
  have hmpos : 0 < m := by dsimp only [m]; omega
  have hmV : MV ≤ m := by dsimp only [m]; omega
  have hma : Ma ≤ m := by dsimp only [m]; omega
  have hmb : Mb ≤ m := by dsimp only [m]; omega
  have hmc : Mc ≤ m := by dsimp only [m]; omega
  have hmprod : Mprod ≤ m := by dsimp only [m]; omega
  have hmq : Mq ≤ m := by dsimp only [m]; omega
  obtain ⟨hVone, hVrate⟩ := hMV m hmV
  obtain ⟨haone, harate⟩ := hMa m hma
  obtain ⟨hbone, hbrate⟩ := hMb m hmb
  obtain ⟨hcone, hcrate⟩ := hMc m hmc
  have hQmone : 1 ≤ Q ε m := hQone m
  have hQrate : |Real.log (Q ε m : ℝ)| ≤ ρ * (outerN C m : ℝ) := hMq m hmq
  have hprodM := hMprod m hmprod
  have hOnat : 0 < outerN C m := by
    rw [outerN]
    exact Nat.mul_pos (pow_pos hC.D_pos _) hmpos
  have hOpos : (0 : ℝ) < (outerN C m : ℝ) := by exact_mod_cast hOnat
  have hOle : (0 : ℝ) ≤ (outerN C m : ℝ) := hOpos.le
  have hgx : g ≤ x := by rw [hg]; exact min_le_left _ _
  have hgy : g ≤ y / C.kappa := by
    rw [hg]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hgz : g ≤ z := by
    rw [hg]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  set dlog : ℝ := (g - ρ) * (outerN C m : ℝ) with hdlog
  have hdlogpos : 0 < dlog := by rw [hdlog]; exact mul_pos (sub_pos.mpr hρg) hOpos
  have hdlogA : dlog ≤ Real.log (a ε m : ℝ) := by
    rw [hdlog]
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hgx ρ) hOle).trans harate
  have hdlogC : dlog ≤ Real.log (c ε m : ℝ) := by
    rw [hdlog]
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hgz ρ) hOle).trans hcrate
  have hkgy : C.kappa * g ≤ y := by
    simpa only [mul_comm] using (le_div_iff₀ hC.kappa_pos).mp hgy
  have hdlogB : C.kappa * dlog ≤ Real.log (b ε m : ℝ) := by
    have hsub : C.kappa * (g - ρ) ≤ y - C.kappa * ρ := by nlinarith
    calc C.kappa * dlog = (C.kappa * (g - ρ)) * (outerN C m : ℝ) := by
          rw [hdlog]
          ring
      _ ≤ (y - C.kappa * ρ) * (outerN C m : ℝ) :=
          mul_le_mul_of_nonneg_right hsub hOle
      _ ≤ Real.log (b ε m : ℝ) := hbrate
  set S : ℕ := Q ε m * (C.q + 2) ^ (C.width * outerN C m) with hS
  have hSone : 1 ≤ S := by
    rw [hS]
    have hbpos : 0 < (C.q + 2) ^ (C.width * outerN C m) :=
      pow_pos (by omega) _
    have : 0 < Q ε m * (C.q + 2) ^ (C.width * outerN C m) :=
      Nat.mul_pos (by omega) hbpos
    omega
  have hsource := source_pool_degenerates F C.q C.width (outerN C m) (Q ε m)
  have hdeg0 := OmegaBound.ADVXXZDegenTrans.degenerates_trans hsource hprodM
  have hdeg : Degenerates F (Tensor3.identity F S)
      (blockDiag (Fin (V ε m))
        (Tensor3.matMul (R := F) (a ε m) (b ε m) (c ε m))) := by
    rw [hS]
    rw [famDS_univ_const_eq_blockDiag F] at hdeg0
    exact hdeg0
  have hSlog : Real.log (S : ℝ) = Real.log (Q ε m : ℝ) +
      ((C.width : ℝ) * (outerN C m : ℝ)) * Real.log (C.q + 2 : ℝ) := by
    rw [hS, Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hQlog : Real.log (Q ε m : ℝ) ≤ ρ * (outerN C m : ℝ) :=
    (le_abs_self _).trans hQrate
  have hfitg : (C.width : ℝ) * Real.log (C.q + 2 : ℝ) ≤ R + τ * g := by
    simpa only [hg] using hfit
  have hfitO := mul_le_mul_of_nonneg_right hfitg hOle
  have hcoarse : Real.log (S : ℝ) - Real.log (V ε m : ℝ) ≤
      (τ * g + 2 * ρ) * (outerN C m : ℝ) := by
    rw [hSlog]
    nlinarith
  have hstrict : Real.log (S : ℝ) - Real.log (V ε m : ℝ) <
      (τ + η) * dlog := by
    rw [hdlog]
    exact hcoarse.trans_lt (by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hmargin hOpos)
  exact omegaRect_le_of_strict_blockDiag F C.kappa (τ + η) dlog S (V ε m)
    (a ε m) (b ε m) (c ε m) hC.kappa_pos htheta hdlogpos hSone hVone
    hdlogA hdlogB hdlogC hstrict hdeg

end OmegaBound.ADVXXZGeneral
end
