import OmegaBound.Schonhage2548Sum
import OmegaBound.CW90EightDBlk
import OmegaBound.CW90EightRungRot

/-!
# Degeneration at a fixed error degree, and rotation of degeneration values

* `DegeneratesAt F N T S` — the `Degenerates` predicate at a **fixed** error degree `N`;
  `exists_degeneratesAt` names the degree and `DegeneratesAt.mono` pads a witness up to any
  larger degree by multiplying `A₁` by `X^d`.
* `Degenerates.rot`, `DDecomp.rot`, `YieldsD.rot`, `HasValD.rot` — invariance under the cyclic
  rotation `rotT` of the legs.
* `powT_sub`, `HasValD.reindex` — the degeneration value passes along a substitution of variables.
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

/-! ## Degeneration at a fixed error degree -/

/-- **`Degenerates` at a fixed error degree `N`.**  Identical to `Tensor3.Degenerates` except
that `N` is a parameter rather than existentially quantified.  A family of degenerations can
only be summed when the degree is common to all summands, which is what this records. -/
def DegeneratesAt (F : Type*) [Field F] {α β γ α' β' γ' : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ'] (N : ℕ)
    (T : Tensor3 F α β γ) (S : Tensor3 F α' β' γ') : Prop :=
  ∃ (A₁ : α' → α → Polynomial F) (A₂ : β' → β → Polynomial F) (A₃ : γ' → γ → Polynomial F),
    (∀ i j k, ∀ m : ℕ, m < N →
      (∑ a : α, ∑ b : β, ∑ c : γ,
        A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)).coeff m = 0) ∧
    (∀ i j k,
      (∑ a : α, ∑ b : β, ∑ c : γ,
        A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)).coeff N = S i j k)

variable {F : Type*} [Field F] {α β γ α' β' γ' : Type*}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
  {T : Tensor3 F α β γ} {S : Tensor3 F α' β' γ'}


/-- Naming the degree. -/
theorem exists_degeneratesAt (h : Degenerates F T S) : ∃ N : ℕ, DegeneratesAt F N T S := by
  obtain ⟨N, A₁, A₂, A₃, hvan, hco⟩ := h
  exact ⟨N, A₁, A₂, A₃, hvan, hco⟩

/-- **Padding a degeneration up to a larger error degree**, by multiplying `A₁` by `X^d`.
This is what lets a family of degenerations of different degrees be brought to a common one. -/
theorem DegeneratesAt.mono {N M : ℕ} (h : DegeneratesAt F N T S) (hNM : N ≤ M) :
    DegeneratesAt F M T S := by
  obtain ⟨A₁, A₂, A₃, hvan, hco⟩ := h
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, M = N + d := ⟨M - N, by omega⟩
  have key : ∀ (i : α') (j : β') (k : γ'),
      (∑ a : α, ∑ b : β, ∑ c : γ,
        (Polynomial.X ^ d * A₁ i a) * A₂ j b * A₃ k c * Polynomial.C (T a b c))
        = Polynomial.X ^ d * ∑ a : α, ∑ b : β, ∑ c : γ,
            A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c) := by
    intro i j k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
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

section DSum

variable {ι : Type} [DecidableEq ι] {X Y Z X' Y' Z' : ι → Type}

section Sums

variable [Fintype ι] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

end Sums

end DSum

section Flatten

variable {σ : Type} [DecidableEq σ] {κ : σ → Type} [∀ u, DecidableEq (κ u)]


end Flatten

section Glue

variable {σ : Type} [Fintype σ] [DecidableEq σ] {Xs Ys Zs : σ → Type}
  [∀ u, Fintype (Xs u)] [∀ u, Fintype (Ys u)] [∀ u, Fintype (Zs u)]

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {A : Tensor3 ℚ X Y Z}

end Glue

/-! ## Relabelling and rotating a degeneration value

CW's `π` for the degeneration-witnessed value, together with the substitution law: the `(a)` blocks of §8 are `⟨1,1,1⟩` units and have to be reindexed away
rather than given a value of their own. -/

section Rot

open CW90

variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Moving the innermost of three summation variables to the outside. -/
private theorem sum_rot3 {A B C M : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid M] (f : A → B → C → M) :
    (∑ b : B, ∑ c : C, ∑ a : A, f a b c) = ∑ a : A, ∑ b : B, ∑ c : C, f a b c := by
  have h1 : ∀ b : B, (∑ c : C, ∑ a : A, f a b c) = ∑ a : A, ∑ c : C, f a b c :=
    fun _ => Finset.sum_comm
  simp only [h1]
  exact Finset.sum_comm

/-- **Degeneration commutes with the cyclic rotation of the legs.**  The three matrices are
cycled with them; the triple sum is the same one read in a different order. -/
theorem Degenerates.rot {A : Tensor3 ℚ X Y Z} {S : Tensor3 ℚ X' Y' Z'}
    (h : Degenerates ℚ A S) : Degenerates ℚ (rotT A) (rotT S) := by
  obtain ⟨N, A₁, A₂, A₃, hvan, hco⟩ := h
  have key : ∀ (j : Y') (k : Z') (i : X'),
      (∑ b : Y, ∑ c : Z, ∑ a : X,
        A₂ j b * A₃ k c * A₁ i a * Polynomial.C (rotT A b c a))
        = ∑ a : X, ∑ b : Y, ∑ c : Z,
            A₁ i a * A₂ j b * A₃ k c * Polynomial.C (A a b c) := by
    intro j k i
    have hterm : ∀ (b : Y) (c : Z) (a : X),
        A₂ j b * A₃ k c * A₁ i a * Polynomial.C (rotT A b c a)
          = A₁ i a * A₂ j b * A₃ k c * Polynomial.C (A a b c) := by
      intro b c a
      rw [rotT_apply]
      ring
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun a _ => hterm b c a]
    exact sum_rot3 _
  exact ⟨N, A₂, A₃, A₁, fun j k i m hm => by rw [key j k i]; exact hvan i j k m hm,
    fun j k i => by rw [key j k i]; exact hco i j k⟩

namespace DDecomp

variable {A : Tensor3 ℚ X Y Z}

/-- **A degeneration decomposition rotates.**  The formats are cycled together; the summand
volumes are permuted products, hence unchanged. -/
def rot (D : DDecomp A) : DDecomp (rotT A) where
  ι := D.ι
  fι := D.fι
  dι := D.dι
  ne := D.ne
  P := D.Q
  Q := D.R
  R := D.P
  fP := D.fQ
  fQ := D.fR
  fR := D.fP
  dP := D.dQ
  dQ := D.dR
  dR := D.dP
  big i := by
    have h := D.big i
    calc 2 ≤ Fintype.card (D.P i) * Fintype.card (D.Q i) * Fintype.card (D.R i) := h
      _ = Fintype.card (D.Q i) * Fintype.card (D.R i) * Fintype.card (D.P i) := by ring
  deg := by
    refine Degenerates.of_eq (Degenerates.rot D.deg) ?_
    funext y z x
    exact dsT_rot D.P D.Q D.R x y z

@[simp] theorem wt_rot (t : ℝ) (D : DDecomp A) : D.rot.wt t = D.wt t := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [DDecomp.vol, rot]
  ring

end DDecomp

theorem YieldsD.rot {t w : ℝ} {A : Tensor3 ℚ X Y Z} (h : YieldsD t A w) :
    YieldsD t (rotT A) w := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D.rot, by rwa [DDecomp.wt_rot]⟩

/-- **The degeneration value is invariant under a cyclic rotation of the legs.**  (CW90 §8's
`π`, for `HasValD`.) -/
theorem HasValD.rot {t v : ℝ} {A : Tensor3 ℚ X Y Z} (h : HasValD t A v) :
    HasValD t (rotT A) v := by
  obtain ⟨n, hn, hY⟩ := h
  refine ⟨n, hn, ?_⟩
  rw [powT_rot]
  exact hY.rot

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z'] in
/-- A substitution of variables passes to tensor powers. -/
theorem powT_sub (A : Tensor3 ℚ X Y Z) (A' : Tensor3 ℚ X' Y' Z') (f₁ : X' → X) (f₂ : Y' → Y)
    (f₃ : Z' → Z) (hsub : ∀ x y z, A' x y z = A (f₁ x) (f₂ y) (f₃ z)) (n : ℕ)
    (φ : Fin n → X') (ψ : Fin n → Y') (χ : Fin n → Z') :
    powT A' n φ ψ χ
      = powT A n (fun r => f₁ (φ r)) (fun r => f₂ (ψ r)) (fun r => f₃ (χ r)) := by
  rw [powT_apply, powT_apply]
  exact Finset.prod_congr rfl fun r _ => hsub (φ r) (ψ r) (χ r)

/-- **The degeneration value passes along a substitution of variables.**  If `A'` is obtained
from `A` by renaming variables then `A` has at least the value of `A'`; no injectivity is
required.  This is what removes the `⟨1,1,1⟩` blocks of §8. -/
theorem HasValD.reindex {t v : ℝ} {A : Tensor3 ℚ X Y Z} {A' : Tensor3 ℚ X' Y' Z'}
    (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z)
    (hsub : ∀ x y z, A' x y z = A (f₁ x) (f₂ y) (f₃ z)) (h : HasValD t A' v) :
    HasValD t A v := by
  obtain ⟨n, hn, D, hD⟩ := h
  exact ⟨n, hn, D.ofSub (fun φ r => f₁ (φ r)) (fun ψ r => f₂ (ψ r)) (fun χ r => f₃ (χ r))
    (powT_sub A A' f₁ f₂ f₃ hsub n), by rwa [DDecomp.wt_ofSub]⟩

end Rot

end CW90Eight

end OmegaBound
