import OmegaBound.ADVXXZGeneralTensor
import OmegaBound.TensorProduct

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem map_tensorProd
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (f : R →+* S) (T : Tensor3 R X Y Z) (U : Tensor3 R X' Y' Z') :
    mapTensor f (tensorProd T U) = tensorProd (mapTensor f T) (mapTensor f U) := by
  funext ⟨x, x'⟩ ⟨y, y'⟩ ⟨z, z'⟩
  exact f.map_mul (T x y z) (U x' y' z')

theorem map_tensorPower
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (f : R →+* S) (T : Tensor3 R X Y Z) (n : ℕ) :
    mapTensor f (tensorPower T n) = tensorPower (mapTensor f T) n := by
  funext x y z
  simp only [mapTensor, tensorPower, map_prod]

theorem map_piTensor
    {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}
    {X Y Z : Fin m → Type*} (f : R →+* S)
    (T : ∀ i, Tensor3 R (X i) (Y i) (Z i)) :
    mapTensor f (fun (x : (i : Fin m) → X i) (y : (i : Fin m) → Y i)
      (z : (i : Fin m) → Z i) => ∏ i, T i (x i) (y i) (z i)) =
      (fun (x : (i : Fin m) → X i) (y : (i : Fin m) → Y i)
        (z : (i : Fin m) → Z i) => ∏ i, mapTensor f (T i) (x i) (y i) (z i)) := by
  funext x y z
  simp only [mapTensor, map_prod]

theorem map_reindex
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z X' Y' Z' : Type*} (f : R →+* S) (T : Tensor3 R X Y Z)
    (eX : X' ≃ X) (eY : Y' ≃ Y) (eZ : Z' ≃ Z) :
    mapTensor f (fun x y z => T (eX x) (eY y) (eZ z)) =
      (fun x y z => mapTensor f T (eX x) (eY y) (eZ z)) := rfl

theorem map_dsumTensor
    {R S : Type*} [CommRing R] [CommRing S]
    {I : Type*} [DecidableEq I] {X Y Z : I → Type*} (f : R →+* S)
    (T : ∀ i, Tensor3 R (X i) (Y i) (Z i)) :
    mapTensor f
      (fun (x : (i : I) × X i) (y : (i : I) × Y i) (z : (i : I) × Z i) =>
        if h : y.1 = x.1 ∧ z.1 = x.1 then
        T x.1 x.2 (cast (congrArg Y h.1) y.2) (cast (congrArg Z h.2) z.2) else 0) =
      (fun (x : (i : I) × X i) (y : (i : I) × Y i) (z : (i : I) × Z i) =>
        if h : y.1 = x.1 ∧ z.1 = x.1 then
        mapTensor f (T x.1) x.2 (cast (congrArg Y h.1) y.2)
          (cast (congrArg Z h.2) z.2) else 0) := by
  funext x y z
  change f (if h : y.1 = x.1 ∧ z.1 = x.1 then
      T x.1 x.2 (cast (congrArg Y h.1) y.2) (cast (congrArg Z h.2) z.2) else 0) =
    (if h : y.1 = x.1 ∧ z.1 = x.1 then
      f (T x.1 x.2 (cast (congrArg Y h.1) y.2) (cast (congrArg Z h.2) z.2)) else 0)
  by_cases h : y.1 = x.1 ∧ z.1 = x.1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, map_zero]

theorem map_famDS
    {R S : Type*} [CommRing R] [CommRing S]
    {I : Type*} [DecidableEq I]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (f : R →+* S) (A : Finset I) (T : I → Tensor3 R X Y Z) :
    mapTensor f (famDS A T) = famDS A (fun i => mapTensor f (T i)) := by
  funext x y z
  change f (if x.1 = y.1 ∧ y.1 = z.1 ∧ x.1 ∈ A then
      T x.1 x.2 y.2 z.2 else 0) =
    (if x.1 = y.1 ∧ y.1 = z.1 ∧ x.1 ∈ A then
      f (T x.1 x.2 y.2 z.2) else 0)
  by_cases h : x.1 = y.1 ∧ y.1 = z.1 ∧ x.1 ∈ A
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem map_zoP
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (f : R →+* S) (T : Tensor3 R X Y Z)
    (pX : X → Prop) (pY : Y → Prop) (pZ : Z → Prop)
    [DecidablePred pX] [DecidablePred pY] [DecidablePred pZ] :
    mapTensor f (zoP pX pY pZ T) = zoP pX pY pZ (mapTensor f T) := by
  funext x y z
  by_cases h : pX x ∧ pY y ∧ pZ z
  · simp [mapTensor, zoP, h]
  · simp [mapTensor, zoP, h]

theorem map_identity
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    mapTensor f (Tensor3.identity R n) = Tensor3.identity S n := by
  funext i j k
  change f (if i = j ∧ j = k then 1 else 0) = (if i = j ∧ j = k then 1 else 0)
  by_cases h : i = j ∧ j = k <;> simp [h]

theorem map_matMul
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c : ℕ) :
    mapTensor f (Tensor3.matMul (R := R) a b c) = Tensor3.matMul (R := S) a b c := by
  funext ⟨i, j⟩ ⟨j', k⟩ ⟨k', i'⟩
  change f (if j = j' ∧ k = k' ∧ i = i' then 1 else 0) =
    (if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
  by_cases h : j = j' ∧ k = k' ∧ i = i' <;> simp [h]

theorem map_cw {S : Type*} [CommRing S] (f : ℤ →+* S) (q : ℕ) :
    mapTensor f (cwZ q) = fun a b c =>
      match a, b, c with
      | .inl none, .inl (some i), .inl (some j) => if i = j then 1 else 0
      | .inl (some i), .inl none, .inl (some j) => if i = j then 1 else 0
      | .inl (some i), .inl (some j), .inl none => if i = j then 1 else 0
      | .inl none, .inl none, .inr _ => 1
      | .inl none, .inr _, .inl none => 1
      | .inr _, .inl none, .inl none => 1
      | _, _, _ => 0 := by
  funext a b c
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
    rcases c with (_ | c) | c <;> simp [mapTensor, cwZ]

theorem map_con {S : Type*} [CommRing S] (f : ℤ →+* S) (q w i j k : ℕ) :
    mapTensor f (conZ q w i j k) =
      zoP (fun a => levOf a = i) (fun b => levOf b = j) (fun c => levOf c = k)
        (tensorPower (mapTensor f (cwZ q)) w) := by
  unfold conZ
  rw [map_zoP, map_tensorPower]

theorem map_iface {S : Type*} [CommRing S] (f : ℤ →+* S)
    (q w i j k n : ℕ) (bX bY bZ : SplitDist w) (ε : ℚ) :
    mapTensor f (ifaceTermZ q w i j k n bX bY bZ ε) = fun x y z =>
      if n = 0 then 1 else
      if ApproxConsistent ε bX (chunkSeq x) ∧
         ApproxConsistent ε bY (chunkSeq y) ∧
         ApproxConsistent ε bZ (chunkSeq z)
      then tensorPower (mapTensor f (conZ q w i j k)) n x y z else 0 := by
  funext x y z
  by_cases hn : n = 0
  · simp [mapTensor, ifaceTermZ, hn]
  · by_cases hc : ApproxConsistent ε bX (chunkSeq x) ∧
        ApproxConsistent ε bY (chunkSeq y) ∧
        ApproxConsistent ε bZ (chunkSeq z)
    · simp [mapTensor, ifaceTermZ, tensorPower, hn, hc, map_prod]
    · simp [mapTensor, ifaceTermZ, hn, hc]

theorem map_act
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (f : R →+* S) (A : X' → X → R) (B : Y' → Y → R)
    (C : Z' → Z → R) (T : Tensor3 R X Y Z) :
    mapTensor f (act A B C T) =
      act (fun x' x => f (A x' x)) (fun y' y => f (B y' y))
        (fun z' z => f (C z' z)) (mapTensor f T) := by
  funext x y z
  simp only [mapTensor, act, map_sum, map_mul]

theorem map_restricts
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (f : R →+* S) {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : Restricts U T) : Restricts (mapTensor f U) (mapTensor f T) := by
  obtain ⟨A, B, C, hU⟩ := h
  refine ⟨(fun x' x => f (A x' x)), (fun y' y => f (B y' y)),
    (fun z' z => f (C z' z)), ?_⟩
  calc
    mapTensor f U = mapTensor f (act A B C T) := congrArg (mapTensor f) hU
    _ = act (fun x' x => f (A x' x)) (fun y' y => f (B y' y))
        (fun z' z => f (C z' z)) (mapTensor f T) := map_act f A B C T

theorem polyDegeneratesAt_of_restricts
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'} (h : Restricts U T) :
    PolyDegeneratesAt R 0 T U := by
  obtain ⟨A, B, C, hU⟩ := h
  refine Exists.intro (fun x i => Polynomial.C (A x i)) ?_
  refine Exists.intro (fun y j => Polynomial.C (B y j)) ?_
  refine Exists.intro (fun z k => Polynomial.C (C z k)) ⟨?_, ?_⟩
  · intro x y z k hk
    omega
  · intro x y z
    rw [hU]
    simp only [act, Polynomial.finset_sum_coeff, ← Polynomial.C_mul,
      Polynomial.coeff_C_zero]

private theorem poly_exists_factor {R : Type*} [CommRing R] (P : Polynomial R) (N : ℕ)
    (h : ∀ m : ℕ, m < N → P.coeff m = 0) :
    ∃ ψ : Polynomial R, P = Polynomial.X ^ N * ψ ∧ ψ.coeff 0 = P.coeff N := by
  obtain ⟨ψ, hψ⟩ := Polynomial.X_pow_dvd_iff.mpr h
  refine ⟨ψ, hψ, ?_⟩
  rw [hψ, Polynomial.coeff_X_pow_mul']
  simp

private theorem poly_coeff_of_factor {R : Type*} [CommRing R]
    (P ψ : Polynomial R) (N : ℕ) (h : P = Polynomial.X ^ N * ψ) :
    (∀ m : ℕ, m < N → P.coeff m = 0) ∧ P.coeff N = ψ.coeff 0 := by
  constructor
  · intro m hm
    rw [h, Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hm]
  · rw [h, Polynomial.coeff_X_pow_mul']
    simp

private theorem poly_sum_prod_six {R : Type*} [CommRing R]
    {α β γ δ ε ζ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [Fintype ζ]
    (g : α → β → γ → R) (h : δ → ε → ζ → R) :
    (∑ a : α × δ, ∑ b : β × ε, ∑ c : γ × ζ, g a.1 b.1 c.1 * h a.2 b.2 c.2) =
      (∑ a : α, ∑ b : β, ∑ c : γ, g a b c) *
        (∑ d : δ, ∑ e : ε, ∑ f : ζ, h d e f) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem polyDegeneratesAt_tensorProd
    {R : Type*} [CommRing R]
    {α β γ α' β' γ' δ ε ζ δ' ε' ζ' : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
    [Fintype δ] [Fintype ε] [Fintype ζ] [Fintype δ'] [Fintype ε'] [Fintype ζ']
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    [DecidableEq δ] [DecidableEq ε] [DecidableEq ζ]
    [DecidableEq δ'] [DecidableEq ε'] [DecidableEq ζ']
    {A : Tensor3 R α β γ} {S : Tensor3 R α' β' γ'}
    {B : Tensor3 R δ ε ζ} {T : Tensor3 R δ' ε' ζ'} {N M : ℕ}
    (hA : PolyDegeneratesAt R N A S) (hB : PolyDegeneratesAt R M B T) :
    PolyDegeneratesAt R (N + M) (tensorProd A B) (tensorProd S T) := by
  obtain ⟨A₁, A₂, A₃, hvanA, hcoA⟩ := hA
  obtain ⟨B₁, B₂, B₃, hvanB, hcoB⟩ := hB
  choose ψ hψ hψ0 using fun (i : α') (j : β') (k : γ') =>
    poly_exists_factor (∑ a : α, ∑ b : β, ∑ c : γ,
      A₁ i a * A₂ j b * A₃ k c * Polynomial.C (A a b c)) N (hvanA i j k)
  choose φ hφ hφ0 using fun (i : δ') (j : ε') (k : ζ') =>
    poly_exists_factor (∑ a : δ, ∑ b : ε, ∑ c : ζ,
      B₁ i a * B₂ j b * B₃ k c * Polynomial.C (B a b c)) M (hvanB i j k)
  have key : ∀ (i : α' × δ') (j : β' × ε') (k : γ' × ζ'),
      (∑ a : α × δ, ∑ b : β × ε, ∑ c : γ × ζ,
        (A₁ i.1 a.1 * B₁ i.2 a.2) * (A₂ j.1 b.1 * B₂ j.2 b.2) *
          (A₃ k.1 c.1 * B₃ k.2 c.2) * Polynomial.C (tensorProd A B a b c)) =
        Polynomial.X ^ (N + M) * (ψ i.1 j.1 k.1 * φ i.2 j.2 k.2) := by
    intro i j k
    have hrw : ∀ (a : α × δ) (b : β × ε) (c : γ × ζ),
        (A₁ i.1 a.1 * B₁ i.2 a.2) * (A₂ j.1 b.1 * B₂ j.2 b.2) *
            (A₃ k.1 c.1 * B₃ k.2 c.2) * Polynomial.C (tensorProd A B a b c) =
          (A₁ i.1 a.1 * A₂ j.1 b.1 * A₃ k.1 c.1 * Polynomial.C (A a.1 b.1 c.1)) *
            (B₁ i.2 a.2 * B₂ j.2 b.2 * B₃ k.2 c.2 * Polynomial.C (B a.2 b.2 c.2)) := by
      rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩
      change _ * Polynomial.C (A a b c * B a' b' c') = _
      rw [Polynomial.C_mul]
      ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => hrw a b c]
    rw [poly_sum_prod_six
      (fun a b c => A₁ i.1 a * A₂ j.1 b * A₃ k.1 c * Polynomial.C (A a b c))
      (fun a b c => B₁ i.2 a * B₂ j.2 b * B₃ k.2 c * Polynomial.C (B a b c))]
    rw [hψ i.1 j.1 k.1, hφ i.2 j.2 k.2, pow_add]
    ring
  refine Exists.intro (fun i a => A₁ i.1 a.1 * B₁ i.2 a.2) ?_
  refine Exists.intro (fun j b => A₂ j.1 b.1 * B₂ j.2 b.2) ?_
  refine Exists.intro (fun k c => A₃ k.1 c.1 * B₃ k.2 c.2) ⟨?_, ?_⟩
  · intro i j k m hm
    rw [key i j k]
    exact (poly_coeff_of_factor _ _ (N + M) rfl).1 m hm
  · intro i j k
    rw [key i j k,
      (poly_coeff_of_factor _ (ψ i.1 j.1 k.1 * φ i.2 j.2 k.2) (N + M) rfl).2,
      Polynomial.mul_coeff_zero, hψ0, hφ0, hcoA, hcoB]
    rfl

theorem polyDegeneratesAt_precomp
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype X''] [Fintype Y''] [Fintype Z'']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    [DecidableEq X''] [DecidableEq Y''] [DecidableEq Z'']
    {N : ℕ} {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) (fX : X'' → X') (fY : Y'' → Y')
    (fZ : Z'' → Z') :
    PolyDegeneratesAt R N T (fun x y z => U (fX x) (fY y) (fZ z)) := by
  obtain ⟨A, B, C, hlow, htop⟩ := h
  exact ⟨fun x i => A (fX x) i, fun y j => B (fY y) j, fun z k => C (fZ z) k,
    fun x y z k hk => hlow _ _ _ k hk, fun x y z => htop _ _ _⟩

theorem polyDegeneratesAt_source_equiv
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' Xs Ys Zs : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype Xs] [Fintype Ys] [Fintype Zs]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    [DecidableEq Xs] [DecidableEq Ys] [DecidableEq Zs]
    {N : ℕ} {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) (eX : Xs ≃ X) (eY : Ys ≃ Y) (eZ : Zs ≃ Z) :
    PolyDegeneratesAt R N (fun x y z => T (eX x) (eY y) (eZ z)) U := by
  obtain ⟨A, B, C, hlow, htop⟩ := h
  refine Exists.intro (fun x i => A x (eX i)) ?_
  refine Exists.intro (fun y j => B y (eY j)) ?_
  refine Exists.intro (fun z k => C z (eZ k)) ⟨?_, ?_⟩
  · intro x y z k hk
    rw [show (∑ i : Xs, ∑ j : Ys, ∑ l : Zs,
        A x (eX i) * B y (eY j) * C z (eZ l) * Polynomial.C (T (eX i) (eY j) (eZ l))) =
        ∑ i : X, ∑ j : Y, ∑ l : Z,
          A x i * B y j * C z l * Polynomial.C (T i j l) from ?_]
    · exact hlow x y z k hk
    · rw [← Equiv.sum_comp eX]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp eY]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Equiv.sum_comp eZ]
  · intro x y z
    rw [show (∑ i : Xs, ∑ j : Ys, ∑ l : Zs,
        A x (eX i) * B y (eY j) * C z (eZ l) * Polynomial.C (T (eX i) (eY j) (eZ l))) =
        ∑ i : X, ∑ j : Y, ∑ l : Z,
          A x i * B y j * C z l * Polynomial.C (T i j l) from ?_]
    · exact htop x y z
    · rw [← Equiv.sum_comp eX]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp eY]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Equiv.sum_comp eZ]

theorem polyDegeneratesAt_source_eq
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {N : ℕ} {T T' : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) (he : T' = T) : PolyDegeneratesAt R N T' U := by
  rw [he]
  exact h

theorem polyDegeneratesAt_target_eq
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {N : ℕ} {T : Tensor3 R X Y Z} {U U' : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) (he : U' = U) : PolyDegeneratesAt R N T U' := by
  rw [he]
  exact h

private def polyConsEquiv (X : Type*) (n : ℕ) : (Fin (n + 1) → X) ≃ X × (Fin n → X) where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv a := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp
  right_inv p := by
    ext
    · simp
    · simp

private theorem tensorPower_succ {R : Type*} [CommRing R] {X Y Z : Type*}
    (T : Tensor3 R X Y Z) (n : ℕ) (x : Fin (n + 1) → X)
    (y : Fin (n + 1) → Y) (z : Fin (n + 1) → Z) :
    tensorPower T (n + 1) x y z = tensorProd T (tensorPower T n)
      (polyConsEquiv X n x) (polyConsEquiv Y n y) (polyConsEquiv Z n z) := by
  change (∏ j : Fin (n + 1), T (x j) (y j) (z j)) =
    T (x 0) (y 0) (z 0) * ∏ j : Fin n, T (x j.succ) (y j.succ) (z j.succ)
  rw [Fin.prod_univ_succ]

theorem polyDegeneratesAt_tensorPower
    {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : ∃ N, PolyDegeneratesAt R N T U) (n : ℕ) :
    ∃ M, PolyDegeneratesAt R M (tensorPower T n) (tensorPower U n) := by
  classical
  obtain ⟨N, hN⟩ := h
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      refine Exists.intro (fun _ _ => 1) ?_
      refine Exists.intro (fun _ _ => 1) ?_
      refine Exists.intro (fun _ _ => 1) ⟨?_, ?_⟩
      · intro x y z k hk
        omega
      · intro x y z
        simp [tensorPower]
  | succ n ih =>
      obtain ⟨M, hM⟩ := ih
      have hprod := polyDegeneratesAt_tensorProd hN hM
      have hsource := polyDegeneratesAt_source_equiv hprod
        (polyConsEquiv X n) (polyConsEquiv Y n) (polyConsEquiv Z n)
      have hsource' : PolyDegeneratesAt R (N + M) (tensorPower T (n + 1))
          (tensorProd U (tensorPower U n)) :=
        polyDegeneratesAt_source_eq hsource (by
          funext x y z
          exact tensorPower_succ T n x y z)
      have htarget := polyDegeneratesAt_precomp hsource'
        (polyConsEquiv X' n) (polyConsEquiv Y' n) (polyConsEquiv Z' n)
      refine ⟨N + M, polyDegeneratesAt_target_eq htarget ?_⟩
      funext x y z
      exact tensorPower_succ U n x y z

theorem map_zero_test (F : Type u) [Field F] (c : ℤ) (hc : c = 0 ∨ c = 1) :
    (((c : F) = 0 ↔ c = 0) ∧ ((c : F) = 1 ↔ c = 1)) := by
  rcases hc with rfl | rfl <;> simp

theorem map_polyDegeneratesAt
    {R S : Type*} [CommRing R] [CommRing S]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (f : R →+* S) {N : ℕ} {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) :
    PolyDegeneratesAt S N (mapTensor f T) (mapTensor f U) := by
  obtain ⟨A, B, C, hlow, htop⟩ := h
  refine Exists.intro (fun x i => (A x i).map f) ?_
  refine Exists.intro (fun y j => (B y j).map f) ?_
  refine Exists.intro (fun z l => (C z l).map f) ⟨?_, ?_⟩
  · intro x y z k hk
    have hmap :
        (∑ i, ∑ j, ∑ l, (A x i).map f * (B y j).map f * (C z l).map f *
          Polynomial.C (mapTensor f T i j l)) =
          (∑ i, ∑ j, ∑ l, A x i * B y j * C z l * Polynomial.C (T i j l)).map f := by
      symm
      simp only [mapTensor, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    rw [hmap, Polynomial.coeff_map, hlow x y z k hk, map_zero]
  · intro x y z
    have hmap :
        (∑ i, ∑ j, ∑ l, (A x i).map f * (B y j).map f * (C z l).map f *
          Polynomial.C (mapTensor f T i j l)) =
          (∑ i, ∑ j, ∑ l, A x i * B y j * C z l * Polynomial.C (T i j l)).map f := by
      symm
      simp only [mapTensor, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    rw [hmap, Polynomial.coeff_map, htop x y z]
    rfl

theorem integral_degenerates (F : Type u) [Field F] (T U : ITensor)
    (h : ∃ N, PolyDegeneratesAt ℤ N T.tensor U.tensor) :
    Degenerates F (T.over F) (U.over F) := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨A, B, C, hlow, htop⟩ :=
    map_polyDegeneratesAt (Int.castRingHom F) hN
  exact ⟨N, A, B, C, hlow, htop⟩

end OmegaBound.ADVXXZGeneral
end
