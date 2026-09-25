import OmegaBound.ADVXXZT6Round130eTableBase
import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round26CountingSpine
import OmegaBound.ADVXXZT6Round82RealDisintegration
import OmegaBound.ADVXXZT6Round130Fenchel

/-!
# Exact symbolic evaluator

The evaluator keeps every coefficient in `Rat`, whose representation is a normalized integer
numerator and positive natural denominator.  Each constructor's value is computed below, and
`ADVXXZT6Round130fSoundness` proves the evaluator sound independently of all released rows.
-/

set_option maxRecDepth 1000000
set_library_suggestions Lean.LibrarySuggestions.empty

namespace OmegaBound.ADVXXZT6Round130f

open OmegaBound.ADVXXZT6Round130e

structure AtomQ130f where
  isExp : Bool
  arg : ℚ
  deriving DecidableEq, Repr, Ord

structure LinearQ130f where
  constant : ℚ
  terms : List (AtomQ130f × ℚ)
  deriving DecidableEq, Repr

/-- Exact binary64 Fenchel multipliers, padded to the paper's three five-level margins. -/
structure DualQ130f where
  coefficient : ℚ
  lambdaSum : ℚ
  lambdaMargin : Fin 3 → Fin 5 → ℚ
  deriving DecidableEq, Repr

def zero130f : LinearQ130f := ⟨0, []⟩

def pure130f (q : ℚ) : LinearQ130f := ⟨q, []⟩

def add130f (a b : LinearQ130f) : LinearQ130f :=
  ⟨a.constant + b.constant, a.terms ++ b.terms⟩

def neg130f (a : LinearQ130f) : LinearQ130f :=
  ⟨-a.constant, a.terms.map fun aq => (aq.1, -aq.2)⟩

def sub130f (a b : LinearQ130f) : LinearQ130f := add130f a (neg130f b)

def scale130f (q : ℚ) (a : LinearQ130f) : LinearQ130f :=
  ⟨q * a.constant, a.terms.map fun aq => (aq.1, q * aq.2)⟩

def atom130f (isExp : Bool) (q : ℚ) : LinearQ130f :=
  ⟨0, [(⟨isExp, q⟩, 1)]⟩

/-- The table generator erases the two identically zero entropy atoms. -/
def nmlAtom130f (q : ℚ) : LinearQ130f :=
  if q = 0 ∨ q = 1 then zero130f else atom130f false q

def sumList130f (xs : List LinearQ130f) : LinearQ130f :=
  xs.foldl add130f zero130f

def sumFin130f {n : Nat} (f : Fin n → LinearQ130f) : LinearQ130f :=
  sumList130f (List.ofFn f)

def entropyFin130f {n : Nat} (q : Fin n → ℚ) : LinearQ130f :=
  sumFin130f fun i => nmlAtom130f (q i)

def expSumFin130f {n : Nat} (q : Fin n → ℚ) : LinearQ130f :=
  sumFin130f fun i => atom130f true (q i)

noncomputable def AtomQ130f.value (a : AtomQ130f) : ℝ :=
  if a.isExp then Real.exp (a.arg : ℝ) else Real.negMulLog (a.arg : ℝ)

noncomputable def termsValue130f (xs : List (AtomQ130f × ℚ)) : ℝ :=
  (xs.map fun aq => (aq.2 : ℝ) * aq.1.value).sum


noncomputable def LinearQ130f.value (e : LinearQ130f) : ℝ :=
  (e.constant : ℝ) + termsValue130f e.terms

@[simp] theorem value_zero130f : LinearQ130f.value zero130f = 0 := by
  simp [LinearQ130f.value, zero130f, termsValue130f]

@[simp] theorem value_pure130f (q : ℚ) : LinearQ130f.value (pure130f q) = (q : ℝ) := by
  simp [LinearQ130f.value, pure130f, termsValue130f]

@[simp] theorem value_add130f (a b : LinearQ130f) :
    LinearQ130f.value (add130f a b) = LinearQ130f.value a + LinearQ130f.value b := by
  simp [LinearQ130f.value, add130f, termsValue130f]
  ring

@[simp] theorem value_neg130f (a : LinearQ130f) :
    LinearQ130f.value (neg130f a) = -LinearQ130f.value a := by
  have hterms : termsValue130f
      (a.terms.map fun aq => (aq.1, -aq.2)) = -termsValue130f a.terms := by
    induction a.terms with
    | nil => simp [termsValue130f]
    | cons x xs ih =>
        simp only [List.map_cons, termsValue130f, List.sum_cons, Rat.cast_neg]
        change -(x.2 : ℝ) * x.1.value +
            termsValue130f (xs.map fun aq => (aq.1, -aq.2)) =
          -((x.2 : ℝ) * x.1.value + termsValue130f xs)
        rw [ih]
        ring
  simp [LinearQ130f.value, neg130f, hterms]
  ring

@[simp] theorem value_sub130f (a b : LinearQ130f) :
    LinearQ130f.value (sub130f a b) = LinearQ130f.value a - LinearQ130f.value b := by
  rw [sub130f, value_add130f, value_neg130f, sub_eq_add_neg]

@[simp] theorem value_scale130f (q : ℚ) (a : LinearQ130f) :
    LinearQ130f.value (scale130f q a) = (q : ℝ) * LinearQ130f.value a := by
  have hterms : termsValue130f
      (a.terms.map fun aq => (aq.1, q * aq.2)) =
        (q : ℝ) * termsValue130f a.terms := by
    induction a.terms with
    | nil => simp [termsValue130f]
    | cons x xs ih =>
        simp only [List.map_cons, termsValue130f, List.sum_cons]
        change ((q * x.2 : ℚ) : ℝ) * x.1.value +
            termsValue130f (xs.map fun aq => (aq.1, q * aq.2)) =
          (q : ℝ) * ((x.2 : ℝ) * x.1.value + termsValue130f xs)
        rw [ih]
        push_cast
        ring
  simp [scale130f, LinearQ130f.value, hterms]
  push_cast
  ring

@[simp] theorem value_atom130f (isExp : Bool) (q : ℚ) :
    LinearQ130f.value (atom130f isExp q) =
      if isExp then Real.exp (q : ℝ) else Real.negMulLog (q : ℝ) := by
  simp [atom130f, LinearQ130f.value, termsValue130f, AtomQ130f.value]

@[simp] theorem value_nmlAtom130f (q : ℚ) :
    LinearQ130f.value (nmlAtom130f q) = Real.negMulLog (q : ℝ) := by
  unfold nmlAtom130f
  split
  · rename_i h
    rcases h with rfl | rfl <;> simp
  · simp

theorem value_sumList130f (xs : List LinearQ130f) :
    LinearQ130f.value (sumList130f xs) = (xs.map LinearQ130f.value).sum := by
  unfold sumList130f
  suffices ∀ (a : LinearQ130f),
      LinearQ130f.value (List.foldl add130f a xs) =
        LinearQ130f.value a + (xs.map LinearQ130f.value).sum by
    simpa using this zero130f
  intro a
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, value_add130f]
      ring

theorem value_sumFin130f {n : Nat} (f : Fin n → LinearQ130f) :
    LinearQ130f.value (sumFin130f f) = ∑ i, LinearQ130f.value (f i) := by
  rw [sumFin130f, value_sumList130f, List.map_ofFn, List.sum_ofFn]
  rfl

@[simp] theorem value_entropyFin130f {n : Nat} (q : Fin n → ℚ) :
    LinearQ130f.value (entropyFin130f q) =
      ∑ i, Real.negMulLog (q i : ℝ) := by
  rw [entropyFin130f, value_sumFin130f]
  apply Finset.sum_congr rfl
  intro i _
  simp

@[simp] theorem value_expSumFin130f {n : Nat} (q : Fin n → ℚ) :
    LinearQ130f.value (expSumFin130f q) = ∑ i, Real.exp (q i : ℝ) := by
  rw [expSumFin130f, value_sumFin130f]
  apply Finset.sum_congr rfl
  intro i _
  simp

def probQ130f {I : Type*} [Fintype I] (d : OmegaBound.ADVXXZ.RatDist I)
    (i : I) : ℚ := (d.num i : ℚ) / d.den

theorem probQ130f_cast {I : Type*} [Fintype I]
    (d : OmegaBound.ADVXXZ.RatDist I) (i : I) :
    (probQ130f d i : ℝ) = d.probR i := by
  unfold probQ130f OmegaBound.ADVXXZ.RatDist.probR
  push_cast
  rfl

end OmegaBound.ADVXXZT6Round130f
