import OmegaBound.ADVXXZGeneralMap
import OmegaBound.ADVXXZStageDegen

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem coeff_sum_three_gp {R : Type*} [CommRing R]
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → Polynomial R) (m : ℕ) :
    (∑ a, ∑ b, ∑ c, f a b c).coeff m =
      ∑ a, ∑ b, ∑ c, (f a b c).coeff m := by
  simp only [Polynomial.finset_sum_coeff]

/-- Padding an integral polynomial degeneration to any larger error degree. -/
theorem polyDegeneratesAt_mono_degree {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    {N M : ℕ} {T : Tensor3 R X Y Z} {U : Tensor3 R X' Y' Z'}
    (h : PolyDegeneratesAt R N T U) (hNM : N ≤ M) :
    PolyDegeneratesAt R M T U := by
  obtain ⟨A₁, A₂, A₃, hvan, hco⟩ := h
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, M = N + d := ⟨M - N, by omega⟩
  have key : ∀ (i : X') (j : Y') (k : Z'),
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (Polynomial.X ^ d * A₁ i a) * A₂ j b * A₃ k c * Polynomial.C (T a b c)) =
        Polynomial.X ^ d * ∑ a : X, ∑ b : Y, ∑ c : Z,
          A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c) := by
    intro i j k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  refine ⟨fun i a => Polynomial.X ^ d * A₁ i a, A₂, A₃, ?_, ?_⟩
  · intro i j k m hm
    rw [key i j k, Polynomial.coeff_X_pow_mul']
    split_ifs with hd
    · exact hvan i j k (m - d) (by omega)
    · rfl
  · intro i j k
    rw [key i j k, Polynomial.coeff_X_pow_mul', if_pos (Nat.le_add_left d N),
      Nat.add_sub_cancel]
    exact hco i j k

/-- A polynomial degeneration followed by a coefficient-field restriction, without leaving
the source ring or changing its error degree. -/
theorem polyDegeneratesAt_trans_restricts {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype X''] [Fintype Y''] [Fintype Z'']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    [DecidableEq X''] [DecidableEq Y''] [DecidableEq Z'']
    {N : ℕ} {T : Tensor3 R X Y Z} {S : Tensor3 R X' Y' Z'}
    {S' : Tensor3 R X'' Y'' Z''}
    (h : PolyDegeneratesAt R N T S) (hr : Restricts S' S) :
    PolyDegeneratesAt R N T S' := by
  obtain ⟨A₁, A₂, A₃, hvan, hco⟩ := h
  obtain ⟨B₁, B₂, B₃, hS'⟩ := hr
  have hact : ∀ (i : X'') (j : Y'') (k : Z''),
      (∑ a : X, ∑ b : Y, ∑ c : Z,
          matMul' (fun (u : X'') (u' : X') => Polynomial.C (B₁ u u')) A₁ i a *
            matMul' (fun (v : Y'') (v' : Y') => Polynomial.C (B₂ v v')) A₂ j b *
            matMul' (fun (w : Z'') (w' : Z') => Polynomial.C (B₃ w w')) A₃ k c *
            Polynomial.C (T a b c)) =
        ∑ i' : X', ∑ j' : Y', ∑ k' : Z',
          Polynomial.C (B₁ i i') * Polynomial.C (B₂ j j') *
            Polynomial.C (B₃ k k') *
              (∑ a : X, ∑ b : Y, ∑ c : Z,
                A₁ i' a * A₂ j' b * A₃ k' c * Polynomial.C (T a b c)) :=
    fun i j k => congrFun (congrFun (congrFun
      (act_act (fun (u : X'') (u' : X') => Polynomial.C (B₁ u u'))
        (fun (v : Y'') (v' : Y') => Polynomial.C (B₂ v v'))
        (fun (w : Z'') (w' : Z') => Polynomial.C (B₃ w w')) A₁ A₂ A₃
        (fun a b c => Polynomial.C (T a b c))).symm i) j) k
  refine ⟨matMul' (fun u u' => Polynomial.C (B₁ u u')) A₁,
    matMul' (fun v v' => Polynomial.C (B₂ v v')) A₂,
    matMul' (fun w w' => Polynomial.C (B₃ w w')) A₃, ?_, ?_⟩
  · intro i j k m hm
    rw [hact i j k, coeff_sum_three_gp]
    refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ =>
      Finset.sum_eq_zero fun k' _ => ?_
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      hvan i' j' k' m hm, mul_zero]
  · intro i j k
    rw [hact i j k, coeff_sum_three_gp, hS']
    simp only [act]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun k' _ => ?_
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      hco i' j' k']

private theorem poly_famDS_block_action {R : Type*} [CommRing R]
    {I X Y Z X' Y' Z' : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor3 R X Y Z)
    (A : ∀ i, X' → X → Polynomial R)
    (B : ∀ i, Y' → Y → Polynomial R)
    (C : ∀ i, Z' → Z → Polynomial R)
    (p : I × X') (q : I × Y') (r : I × Z') :
    (∑ a : I × X, ∑ b : I × Y, ∑ c : I × Z,
      (if a.1 = p.1 then A p.1 p.2 a.2 else 0) *
        (if b.1 = q.1 then B q.1 q.2 b.2 else 0) *
        (if c.1 = r.1 then C r.1 r.2 c.2 else 0) *
        Polynomial.C (famDS (Finset.univ : Finset I) T a b c)) =
      if p.1 = q.1 ∧ q.1 = r.1 then
        ∑ x : X, ∑ y : Y, ∑ z : Z,
          A p.1 p.2 x * B p.1 q.2 y * C p.1 r.2 z * Polynomial.C (T p.1 x y z)
      else 0 := by
  change act
      (fun p a => if a.1 = p.1 then A p.1 p.2 a.2 else 0)
      (fun q b => if b.1 = q.1 then B q.1 q.2 b.2 else 0)
      (fun r c => if c.1 = r.1 then C r.1 r.2 c.2 else 0)
      (mapTensor (Polynomial.C : R →+* Polynomial R)
        (famDS (Finset.univ : Finset I) T)) p q r = _
  rw [map_famDS, act_famDS]
  rcases p with ⟨i, x'⟩
  rcases q with ⟨j, y'⟩
  rcases r with ⟨k, z'⟩
  simp only [Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single i]
      · simp [mapTensor]
      · intro l _ hli
        simp [hli]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [if_neg (fun h => hik h.2)]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hli : l = i
      · subst l; simp [hik]
      · simp [hli]
  · rw [if_neg (fun h => hij h.1)]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hli : l = i
    · subst l; simp [hij]
    · simp [hli]

/-- Direct sums of a finite family of polynomial degenerations at one common degree. -/
theorem polyDegeneratesAt_famDS {R : Type*} [CommRing R]
    {I X Y Z X' Y' Z' : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (T : I → Tensor3 R X Y Z) (U : I → Tensor3 R X' Y' Z') (N : ℕ)
    (h : ∀ i, PolyDegeneratesAt R N (T i) (U i)) :
    PolyDegeneratesAt R N (famDS (Finset.univ : Finset I) T)
      (famDS (Finset.univ : Finset I) U) := by
  choose A B C hvan hco using h
  refine ⟨fun p a => if a.1 = p.1 then A p.1 p.2 a.2 else 0,
    fun q b => if b.1 = q.1 then B q.1 q.2 b.2 else 0,
    fun r c => if c.1 = r.1 then C r.1 r.2 c.2 else 0, ?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ m hm
    rw [poly_famDS_block_action T A B C]
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        rw [if_pos ⟨rfl, rfl⟩]
        exact hvan i x y z m hm
      · rw [if_neg (fun h => hik h.2)]
        simp
    · rw [if_neg (fun h => hij h.1)]
      simp
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    rw [poly_famDS_block_action T A B C, famDS_apply]
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        rw [if_pos ⟨rfl, rfl⟩]
        simpa using hco i x y z
      · simp [hik]
    · simp [hij]

/-- Direct sums of finitely many polynomial degenerations, with their error degrees padded to
one finite supremum. -/
theorem exists_polyDegeneratesAt_famDS {R : Type*} [CommRing R]
    {I X Y Z X' Y' Z' : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (T : I → Tensor3 R X Y Z) (U : I → Tensor3 R X' Y' Z')
    (h : ∀ i, ∃ N, PolyDegeneratesAt R N (T i) (U i)) :
    ∃ N, PolyDegeneratesAt R N (famDS (Finset.univ : Finset I) T)
      (famDS (Finset.univ : Finset I) U) := by
  choose n hn using h
  let N := (Finset.univ : Finset I).sup n
  refine ⟨N, polyDegeneratesAt_famDS T U N (fun i => ?_)⟩
  exact polyDegeneratesAt_mono_degree (hn i) (Finset.le_sup (Finset.mem_univ i))

/-- Integral form of the finite-grid direct-sum argument: one input summand per grid, a common
truncated number of outputs per grid, then restriction of the labelled sum to the coefficient
sum on the common physical legs. -/
theorem exists_polyDegeneratesAt_famDS_of_sum
    {I XI YI ZI XO YO ZO : Type} [Fintype I] [DecidableEq I]
    [Fintype XI] [Fintype YI] [Fintype ZI]
    [Fintype XO] [Fintype YO] [Fintype ZO]
    [DecidableEq XI] [DecidableEq YI] [DecidableEq ZI]
    [DecidableEq XO] [DecidableEq YO] [DecidableEq ZO]
    (Inp : Tensor3 ℤ XI YI ZI) (out : I → Tensor3 ℤ XO YO ZO)
    (Tε : Tensor3 ℤ XO YO ZO)
    (hsum : ∀ x y z, Tε x y z = ∑ i : I, out i x y z) (C : ℕ)
    (h : ∀ i, ∃ N, PolyDegeneratesAt ℤ N Inp
      (famDS (Finset.univ : Finset (Fin C)) (fun _ => out i))) :
    ∃ N, PolyDegeneratesAt ℤ N
      (famDS (Finset.univ : Finset I) (fun _ => Inp))
      (famDS (Finset.univ : Finset (Fin C)) (fun _ => Tε)) := by
  obtain ⟨N, hbig⟩ := exists_polyDegeneratesAt_famDS (fun _ : I => Inp)
    (fun i => famDS (Finset.univ : Finset (Fin C)) (fun _ => out i)) h
  refine ⟨N, polyDegeneratesAt_trans_restricts hbig ?_⟩
  have h₁ : famDS (Finset.univ : Finset (Fin C)) (fun _ => Tε) ≤ₜ
      famDS (Finset.univ : Finset (Fin C))
        (fun _ => famDS (Finset.univ : Finset I) out) := by
    refine OmegaBound.ADVXXZStage.famDS_const_mono
      (R := ℤ) (ι := Fin C) (X := I × XO) (Y := I × YO) (Z := I × ZO)
      (X' := XO) (Y' := YO) (Z' := ZO) _ ?_
    have hT : Tε = fun x y z => ∑ i ∈ (Finset.univ : Finset I), out i x y z := by
      funext x y z
      simpa using hsum x y z
    rw [hT]
    exact OmegaBound.ADVXXZStage.sum_restricts_famDS
      (R := ℤ) (ι := I) (X := XO) (Y := YO) (Z := ZO) _ out
  exact Tensor3.Restricts.trans h₁ (OmegaBound.ADVXXZStage.famDS_swap
    (R := ℤ) (ι := I) (κ := Fin C) (X := XO) (Y := YO) (Z := ZO) out)

end
end OmegaBound.ADVXXZGeneral
end
