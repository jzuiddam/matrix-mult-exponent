import OmegaBound.EntropyCount

/-!
# Complete split distributions, and the integrality convention

This file formalises §2 of Vassilevska Williams–Xu–Xu–Zhou, *New Bounds for Matrix
Multiplication: from Alpha to Omega* (arXiv:2307.07970) — `prelim.tex:203-241`, the section
"Complete Split Distributions" — which is the definitional layer that Alman–Duan–Vassilevska
Williams–Xu–Xu–Zhou, *More Asymmetry Yields Faster Matrix Multiplication* (arXiv:2404.16349)
inherits wholesale (`prelim.tex` there says the definitions "are the same as in prior work").

## The integrality convention — stated once, here

Both papers write `A_r · n`, `α(i,j,k) · n`, `β(σ) · n` for cardinalities of sets of
coordinates.  These are **real** numbers in the sources and the released certificate stores
them as binary64 doubles; nowhere is it said what happens when they are not integers.  The
convention adopted here, and inherited by every later level:

> A distribution parameter is a `RatDist`: a vector of **natural-number numerators** over a
> common **positive natural denominator**.  Lengths are required to be multiples of that
> denominator.

Concretely `RatDist ι` carries `num : ι → ℕ`, `den : ℕ`, `0 < den`, `∑ num = den`; the
probability is `num i / den`; and `P.cnt n i := num i * (n / den)` is a *natural number*
which satisfies `(P.cnt n i : ℝ) = P.probR i * n` as soon as `P.den ∣ n` (`RatDist.cnt_spec`).
That equation is verbatim the hypothesis `∀ i, (k i : ℝ) = a i * N` of
`Entropy.two_pow_le_multinomial_of_dist`, so the convention *discharges* that obligation; see `RatDist.two_pow_le_multinomial_cnt`.

Nothing is lost: every parameter in the released ADVXXZ certificate is a rational, and the
laser method is free to pass to a subsequence of `n`.  Nothing is fudged either: no rounding
is performed anywhere, and no real-valued cardinality ever appears.

## Complete split distributions

With `w = 2^(ℓ-1)`, a level-`ℓ` variable of `CW_q^{⊗w}` is a length-`w` word over the level-1
alphabet `{0,1,2}` — a `Chunk w` — and a *complete split distribution* is a distribution on
`Chunk w`, i.e. a `SplitDist w := RatDist (Chunk w)`.  A level-1 index sequence for a
length-`n` power is a function `Fin n → Chunk w` (the paper writes it as an element of
`{0,1,2}^{w·n}` and cuts it into consecutive chunks; currying is the same data and removes
all index arithmetic).  Its *complete split distribution* is then literally the empirical
type of that function, and consistency is equality of types.

## Main definitions

* `RatDist` — the integrality convention.
* `RatDist.cnt`, `RatDist.cnt_spec` — integral counts, and the bridge to `ℝ`.
* `RatDist.map`, `RatDist.pairWith`, `RatDist.mix` — marginals, joints and mixtures, all
  staying inside the convention.
* `Chunk`, `chunkLvl`, `chunkLev` — level-1 words and the level-`ℓ` index they carry.
* `SplitDist` — complete split distributions.
* `typeCnt`, `emp`, `empDist` — `split(Î)` and `split(Î, S)` of the source.
* `Consistent`, `ApproxConsistent` — the two consistency notions of `prelim.tex:213-238`.

## Main results

* `RatDist.two_pow_le_multinomial_cnt`, `RatDist.multinomial_cnt_le_two_pow` — the type-count
  sandwich `2^{n(H₂ − o(1))} ≤ binom ≤ 2^{n H₂}` **with no side hypothesis at all** beyond
  `P.den ∣ n`.  This is the payoff of the convention.
* `Consistent.map` — consistency pushes forward along a map of alphabets; this is what makes
  `α_X, α_Y, α_Z` marginals and the level-`ℓ` index sequence of a level-1 one legitimate.
* `consistent_empDist` — every index sequence *is* consistent with its own split distribution.
* `approxConsistent_iff_int`, `approxConsistent_zero_iff`, `Consistent.approx` — the ε-layer.
-/

open Finset

namespace OmegaBound
namespace ADVXXZ

/-! ## The integrality convention -/

/-- **A rational distribution in integral form.**  `num i / den` is the probability of `i`.

This is the integrality convention of the ADVXXZ route: every distribution parameter is
carried as natural-number numerators over one positive natural denominator, and lengths are
required to be multiples of the denominator (see `RatDist.cnt`).  The sources treat these
as reals and never address integrality. -/
structure RatDist (ι : Type*) [Fintype ι] where
  /-- The unnormalised weight of `i`. -/
  num : ι → ℕ
  /-- The common denominator. -/
  den : ℕ
  /-- The denominator is positive. -/
  den_pos : 0 < den
  /-- The numerators sum to the denominator, i.e. the probabilities sum to `1`. -/
  sum_num : ∑ i, num i = den

namespace RatDist

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The probability of `i`, as a rational. -/
def prob (P : RatDist ι) (i : ι) : ℚ := (P.num i : ℚ) / (P.den : ℚ)

/-- The probability of `i`, as a real.  This is the form the entropy layer consumes. -/
noncomputable def probR (P : RatDist ι) (i : ι) : ℝ := (P.num i : ℝ) / (P.den : ℝ)

theorem den_ne_zero (P : RatDist ι) : (P.den : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.2 P.den_pos.ne'

theorem denR_ne_zero (P : RatDist ι) : (P.den : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 P.den_pos.ne'

theorem prob_nonneg (P : RatDist ι) (i : ι) : 0 ≤ P.prob i :=
  div_nonneg (by positivity) (by positivity)

theorem probR_nonneg (P : RatDist ι) (i : ι) : 0 ≤ P.probR i :=
  div_nonneg (by positivity) (by positivity)

theorem sum_prob (P : RatDist ι) : ∑ i, P.prob i = 1 := by
  simp only [prob, ← Finset.sum_div]
  rw [← Nat.cast_sum, P.sum_num, div_self P.den_ne_zero]

theorem sum_probR (P : RatDist ι) : ∑ i, P.probR i = 1 := by
  simp only [probR, ← Finset.sum_div]
  rw [← Nat.cast_sum, P.sum_num, div_self P.denR_ne_zero]

/-- A `RatDist` forces its alphabet to be nonempty: an empty sum cannot be positive. -/
theorem nonempty (P : RatDist ι) : Nonempty ι := by
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.1 h
  have := P.sum_num
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact absurd this.symm P.den_pos.ne'

/-! ### Integral counts -/

/-- **The integral count**: the number of coordinates, out of `n`, carrying the letter `i`.
A natural number by construction; it equals `P.prob i * n` exactly when `P.den ∣ n`. -/
def cnt (P : RatDist ι) (n : ℕ) (i : ι) : ℕ := P.num i * (n / P.den)

theorem sum_cnt (P : RatDist ι) {n : ℕ} (h : P.den ∣ n) : ∑ i, P.cnt n i = n := by
  simp only [cnt, ← Finset.sum_mul, P.sum_num]
  exact Nat.mul_div_cancel' h

/-- **The bridge to `ℝ`.**  This equation is verbatim the hypothesis
`∀ i, (k i : ℝ) = a i * N` of `Entropy.two_pow_le_multinomial_of_dist`. -/
theorem cnt_spec (P : RatDist ι) {n : ℕ} (h : P.den ∣ n) (i : ι) :
    (P.cnt n i : ℝ) = P.probR i * n := by
  obtain ⟨m, rfl⟩ := h
  rw [cnt, Nat.mul_div_cancel_left _ P.den_pos, probR, div_mul_eq_mul_div,
    eq_div_iff P.denR_ne_zero]
  push_cast
  ring

theorem cnt_spec_rat (P : RatDist ι) {n : ℕ} (h : P.den ∣ n) (i : ι) :
    (P.cnt n i : ℚ) = P.prob i * n := by
  obtain ⟨m, rfl⟩ := h
  rw [cnt, Nat.mul_div_cancel_left _ P.den_pos, prob, div_mul_eq_mul_div,
    eq_div_iff P.den_ne_zero]
  push_cast
  ring

/-! ### The type-count sandwich, with the integrality obligation discharged -/

/-- **`binom(n; P.cnt n) ≤ 2^{n·H₂(P)}`.**  The laser method's upper count, with no
hypothesis beyond `P.den ∣ n`: the integrality convention supplies the rest. -/
theorem multinomial_cnt_le_two_pow (P : RatDist ι) {n : ℕ} (hn : 0 < n) (h : P.den ∣ n) :
    ((Nat.multinomial Finset.univ (P.cnt n) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((n : ℝ) * Entropy.H₂ Finset.univ P.probR) :=
  Entropy.multinomial_le_two_pow_of_dist P.probR (P.cnt n) n (P.sum_cnt h) hn (P.cnt_spec h)

/-- **`2^{n(H₂(P) − o(1))} ≤ binom(n; P.cnt n)`.**  The laser method's lower count.  The
`o(1)` is `Entropy.errRate (Fintype.card ι) n / log 2`, killed by `Entropy.tendsto_errRate`. -/
theorem two_pow_le_multinomial_cnt (P : RatDist ι) {n : ℕ} (hn : 0 < n) (h : P.den ∣ n) :
    (2 : ℝ) ^ ((n : ℝ) * (Entropy.H₂ Finset.univ P.probR
        - Entropy.errRate (Fintype.card ι) n / Real.log 2))
      ≤ ((Nat.multinomial Finset.univ (P.cnt n) : ℕ) : ℝ) :=
  Entropy.two_pow_le_multinomial_of_dist P.probR (P.cnt n) n (P.sum_cnt h) hn (P.cnt_spec h)

/-! ### Marginals, joints and mixtures -/

/-- **The pushforward of a distribution along a map of alphabets.**  Marginals of a joint
distribution — the `α_X, α_Y, α_Z` of the laser method — are this with `g = Prod.fst` etc.,
and the level-`ℓ` index distribution of a complete split distribution is this with
`g = chunkLev`. -/
def map [DecidableEq κ] (g : ι → κ) (P : RatDist ι) : RatDist κ where
  num j := ∑ i ∈ Finset.univ.filter fun i => g i = j, P.num i
  den := P.den
  den_pos := P.den_pos
  sum_num := by
    rw [← P.sum_num]
    exact (Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (g i)) P.num)

theorem map_num [DecidableEq κ] (g : ι → κ) (P : RatDist ι) (j : κ) :
    (P.map g).num j = ∑ i ∈ Finset.univ.filter fun i => g i = j, P.num i := rfl

@[simp] theorem map_den [DecidableEq κ] (g : ι → κ) (P : RatDist ι) :
    (P.map g).den = P.den := rfl

/-- **The joint distribution of a weight vector and a family of distributions**, all sharing
the denominator `d`.  This is the parameter package of the global stage: `κ = Fin 6` the six
regions, `A` the region weights, `P r` the level-`ℓ` distribution used in region `r`; the
count `pairWith .. |>.cnt n (r, i)` is exactly the source's `n · A_r · α^{(r)}(i)`, and it is
a natural number. -/
def pairWith (A : RatDist κ) (P : κ → RatDist ι) (d : ℕ) (hd : ∀ r, (P r).den = d) :
    RatDist (κ × ι) where
  num := fun p => A.num p.1 * (P p.1).num p.2
  den := A.den * d
  den_pos := by
    obtain ⟨r⟩ := A.nonempty
    have : 0 < d := hd r ▸ (P r).den_pos
    exact Nat.mul_pos A.den_pos this
  sum_num := by
    rw [Fintype.sum_prod_type]
    calc ∑ r : κ, ∑ i : ι, A.num r * (P r).num i
        = ∑ r : κ, A.num r * d := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.mul_sum, (P r).sum_num, hd r]
      _ = A.den * d := by rw [← Finset.sum_mul, A.sum_num]

theorem pairWith_num (A : RatDist κ) (P : κ → RatDist ι) (d : ℕ) (hd : ∀ r, (P r).den = d)
    (r : κ) (i : ι) : (pairWith A P d hd).num (r, i) = A.num r * (P r).num i := rfl

/-- **The mixture `∑_r A_r · P_r`**, the marginal of `pairWith` on the second factor.  The
source's constraint `∑_{r ∈ [6]} β^{(r)} A_r = β` is `mix A P d hd = β`. -/
def mix [DecidableEq ι] (A : RatDist κ) (P : κ → RatDist ι) (d : ℕ) (hd : ∀ r, (P r).den = d) :
    RatDist ι :=
  (pairWith A P d hd).map Prod.snd

theorem mix_num [DecidableEq ι] (A : RatDist κ) (P : κ → RatDist ι) (d : ℕ)
    (hd : ∀ r, (P r).den = d) (i : ι) :
    (mix A P d hd).num i = ∑ r : κ, A.num r * (P r).num i := by
  classical
  rw [mix, map_num, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ i fun j => (pairWith A P d hd).num (r, j)]
  simp [pairWith_num]

@[simp] theorem mix_den [DecidableEq ι] (A : RatDist κ) (P : κ → RatDist ι) (d : ℕ)
    (hd : ∀ r, (P r).den = d) : (mix A P d hd).den = A.den * d := rfl

end RatDist

/-! ## Empirical types of index sequences -/

section TypeCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The type (histogram) of a length-`n` sequence.**  For a level-1 index sequence
`Î : Fin n → Chunk w` this is `n · split(Î)` of the source. -/
def typeCnt (f : Fin n → ι) (i : ι) : ℕ := (Finset.univ.filter fun t => f t = i).card

/-- **The type of a sequence restricted to a subset**, the source's `split(Î, S)` before
normalisation. -/
def typeCntOn (S : Finset (Fin n)) (f : Fin n → ι) (i : ι) : ℕ :=
  (S.filter fun t => f t = i).card

omit [Fintype ι] in
theorem typeCnt_eq_sum (f : Fin n → ι) (i : ι) :
    typeCnt f i = ∑ t : Fin n, if f t = i then 1 else 0 := by
  rw [typeCnt, Finset.card_filter]

omit [Fintype ι] in
theorem typeCntOn_eq_sum (S : Finset (Fin n)) (f : Fin n → ι) (i : ι) :
    typeCntOn S f i = ∑ t ∈ S, if f t = i then 1 else 0 := by
  rw [typeCntOn, Finset.card_filter]

theorem sum_typeCntOn (S : Finset (Fin n)) (f : Fin n → ι) :
    ∑ i, typeCntOn S f i = S.card := by
  simp only [typeCntOn_eq_sum]
  rw [Finset.sum_comm]
  simp

theorem sum_typeCnt (f : Fin n → ι) : ∑ i, typeCnt f i = n := by
  have := sum_typeCntOn (Finset.univ : Finset (Fin n)) f
  simpa using this

omit [Fintype ι] in
@[simp] theorem typeCntOn_univ (f : Fin n → ι) (i : ι) :
    typeCntOn Finset.univ f i = typeCnt f i := rfl

omit [Fintype ι] in
theorem typeCnt_le (f : Fin n → ι) (i : ι) : typeCnt f i ≤ n := by
  rw [typeCnt]
  calc (Finset.univ.filter fun t => f t = i).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

/-- **`split(Î)`**: the empirical distribution of a sequence, as a rational vector. -/
def emp (f : Fin n → ι) (i : ι) : ℚ := (typeCnt f i : ℚ) / (n : ℚ)

omit [Fintype ι] in
/-- **Reweighting an empirical distribution by its own length.**  With `N` the length of an
ambient sequence and `f` a length-`L` piece of it, `(L/N)·split(f) = |f⁻¹(i)|/N`.  No
positivity hypothesis is needed: at `L = 0` the piece is empty and both sides vanish, and at
`N = 0` both sides are `0` by Lean's `x/0 = 0`. -/
theorem weight_mul_emp {L : ℕ} (g : Fin L → ι) (i : ι) (N : ℚ) :
    ((L : ℕ) : ℚ) / N * emp g i = (typeCnt g i : ℚ) / N := by
  rcases eq_or_ne N 0 with hN | hN
  · simp [hN]
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have h0 : typeCnt g i = 0 := Nat.le_zero.1 (typeCnt_le g i)
    simp [emp, h0]
  · have hLQ : ((L : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    rw [emp]
    field_simp

/-- **`split(Î)` as a `RatDist`** — a level-1 index sequence *is* a complete split
distribution, `prelim.tex` Definition `def:split-hatI`. -/
def empDist (hn : 0 < n) (f : Fin n → ι) : RatDist ι where
  num := typeCnt f
  den := n
  den_pos := hn
  sum_num := sum_typeCnt f

@[simp] theorem empDist_num (hn : 0 < n) (f : Fin n → ι) : (empDist hn f).num = typeCnt f := rfl

@[simp] theorem empDist_den (hn : 0 < n) (f : Fin n → ι) : (empDist hn f).den = n := rfl

theorem empDist_prob (hn : 0 < n) (f : Fin n → ι) (i : ι) :
    (empDist hn f).prob i = emp f i := rfl

end TypeCount

/-! ## Consistency -/

section Consistency

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **`f` is consistent with `P`** (`prelim.tex:213-218`): the proportion of each letter in
`f` equals its `P`-probability.  Stated division-free, so that it is an identity of natural
numbers and needs no positivity hypothesis on `n`. -/
def Consistent (P : RatDist ι) (f : Fin n → ι) : Prop :=
  ∀ i, typeCnt f i * P.den = P.num i * n

instance instDecidableConsistent (P : RatDist ι) (f : Fin n → ι) :
    Decidable (Consistent P f) :=
  inferInstanceAs (Decidable (∀ i, typeCnt f i * P.den = P.num i * n))

theorem consistent_iff_prob (P : RatDist ι) (f : Fin n → ι) (hn : 0 < n) :
    Consistent P f ↔ ∀ i, emp f i = P.prob i := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  constructor
  · intro h i
    have := h i
    rw [emp, RatDist.prob, div_eq_div_iff hnQ P.den_ne_zero]
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) this
  · intro h i
    have := h i
    rw [emp, RatDist.prob, div_eq_div_iff hnQ P.den_ne_zero] at this
    exact_mod_cast this

/-- Under the integrality convention, consistency says the type is *the* integral count. -/
theorem consistent_iff_cnt (P : RatDist ι) (f : Fin n → ι) (hd : P.den ∣ n) :
    Consistent P f ↔ ∀ i, typeCnt f i = P.cnt n i := by
  obtain ⟨m, rfl⟩ := hd
  constructor
  · intro h i
    have := h i
    rw [RatDist.cnt, Nat.mul_div_cancel_left _ P.den_pos]
    have hmul : typeCnt f i * P.den = P.num i * m * P.den := by
      rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_right P.den_pos hmul
  · intro h i
    rw [h i, RatDist.cnt, Nat.mul_div_cancel_left _ P.den_pos]
    ring

/-- Every index sequence is consistent with its own split distribution. -/
theorem consistent_empDist (hn : 0 < n) (f : Fin n → ι) : Consistent (empDist hn f) f :=
  fun _ => rfl

/-- **Consistency pushes forward along a map of alphabets.**  Applied to `Prod.fst`/`Prod.snd`
this is "the `X`-marginal of a distribution consistent triple is consistent with `α_X`";
applied to `chunkLev` it is "a level-1 index sequence consistent with a complete split
distribution has a level-`ℓ` index sequence consistent with its level-`ℓ` marginal". -/
theorem Consistent.map {κ : Type*} [Fintype κ] [DecidableEq κ] {P : RatDist ι}
    {f : Fin n → ι} (h : Consistent P f) (g : ι → κ) :
    Consistent (P.map g) (g ∘ f) := by
  intro j
  have hfib : typeCnt (g ∘ f) j = ∑ i ∈ Finset.univ.filter fun i => g i = j, typeCnt f i := by
    simp only [typeCnt_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [Function.comp_apply]
  rw [hfib, RatDist.map_num, RatDist.map_den, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => h i

end Consistency

/-! ## Approximate consistency -/

section Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **`f` is consistent with `P` up to `ε`** (`prelim.tex:231-238`): the `L∞` distance
between `split(f)` and `P` is at most `ε`. -/
def ApproxConsistent (ε : ℚ) (P : RatDist ι) (f : Fin n → ι) : Prop :=
  ∀ i, |emp f i - P.prob i| ≤ ε

instance instDecidableApproxConsistent (ε : ℚ) (P : RatDist ι) (f : Fin n → ι) :
    Decidable (ApproxConsistent ε P f) :=
  inferInstanceAs (Decidable (∀ i, |emp f i - P.prob i| ≤ ε))

/-- The division-free form of approximate consistency. -/
theorem approxConsistent_iff_int (ε : ℚ) (P : RatDist ι) (f : Fin n → ι) (hn : 0 < n) :
    ApproxConsistent ε P f ↔
      ∀ i, |(typeCnt f i : ℚ) * P.den - (n : ℚ) * P.num i| ≤ ε * ((n : ℚ) * P.den) := by
  have hnQ : (0 : ℚ) < n := Nat.cast_pos.2 hn
  have hdQ : (0 : ℚ) < P.den := Nat.cast_pos.2 P.den_pos
  refine forall_congr' fun i => ?_
  rw [emp, RatDist.prob, div_sub_div _ _ (ne_of_gt hnQ) (ne_of_gt hdQ), abs_div,
    abs_of_pos (mul_pos hnQ hdQ), div_le_iff₀ (mul_pos hnQ hdQ)]

/-- Exact consistency implies `ε`-approximate consistency, for every `ε ≥ 0`. -/
theorem Consistent.approx {ε : ℚ} (hε : 0 ≤ ε) {P : RatDist ι} {f : Fin n → ι}
    (h : Consistent P f) (hn : 0 < n) : ApproxConsistent ε P f := by
  rw [approxConsistent_iff_int _ _ _ hn]
  intro i
  have h0 : ((typeCnt f i * P.den : ℕ) : ℚ) = ((P.num i * n : ℕ) : ℚ) := by exact_mod_cast h i
  push_cast at h0
  have h1 : ((typeCnt f i : ℚ)) * P.den = (n : ℚ) * P.num i := by rw [h0]; ring
  rw [h1, sub_self, abs_zero]
  exact mul_nonneg hε (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg P.den))

/-- At `ε = 0`, approximate consistency is consistency. -/
theorem approxConsistent_zero_iff (P : RatDist ι) (f : Fin n → ι) (hn : 0 < n) :
    ApproxConsistent 0 P f ↔ Consistent P f := by
  rw [approxConsistent_iff_int _ _ _ hn]
  constructor
  · intro h i
    have h1 := h i
    rw [zero_mul, abs_nonpos_iff, sub_eq_zero] at h1
    have h2 : ((typeCnt f i * P.den : ℕ) : ℚ) = ((P.num i * n : ℕ) : ℚ) := by
      push_cast
      rw [h1]; ring
    exact_mod_cast h2
  · intro h i
    have h0 : ((typeCnt f i * P.den : ℕ) : ℚ) = ((P.num i * n : ℕ) : ℚ) := by exact_mod_cast h i
    push_cast at h0
    rw [zero_mul, abs_nonpos_iff, sub_eq_zero, h0]
    ring

theorem ApproxConsistent.mono {ε ε' : ℚ} (hle : ε ≤ ε') {P : RatDist ι} {f : Fin n → ι}
    (h : ApproxConsistent ε P f) : ApproxConsistent ε' P f :=
  fun i => le_trans (h i) hle

end Approx

/-! ## Level-1 words, and the level-`ℓ` index they carry -/

/-- The width of a level-`ℓ` block: `2^(ℓ-1)`.  Everything below is stated for a general
width `w`, which is both more general and free of `2^(ℓ-1)` arithmetic; `wid` is the
instantiation the papers use. -/
def wid (ℓ : ℕ) : ℕ := 2 ^ (ℓ - 1)

theorem two_mul_wid (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : 2 * wid ℓ = 2 ^ ℓ := by
  rw [wid, ← pow_succ']
  congr 1
  omega

@[simp] theorem wid_one : wid 1 = 1 := rfl

@[simp] theorem wid_two : wid 2 = 2 := rfl

/-- **A level-1 word of width `w`**: an element of `{0,1,2}^w`, indexing one part of the
partition of the variables of `CW_q^{⊗w}` induced by the level-1 partition of `CW_q`. -/
abbrev Chunk (w : ℕ) := Fin w → Fin 3

/-- **The level-`ℓ` index of a level-1 word**, `∑_p σ_p` — the coarsening
`prelim.tex:151-160` performs. -/
def chunkLvl {w : ℕ} (σ : Chunk w) : ℕ := ∑ p, (σ p : ℕ)

theorem chunkLvl_le {w : ℕ} (σ : Chunk w) : chunkLvl σ ≤ 2 * w := by
  calc chunkLvl σ ≤ ∑ _p : Fin w, 2 := Finset.sum_le_sum fun p _ => by omega
    _ = 2 * w := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- The level-`ℓ` index as an element of the finite index set `{0, …, 2^ℓ}`. -/
def chunkLev {w : ℕ} (σ : Chunk w) : Fin (2 * w + 1) := ⟨chunkLvl σ, by
  have := chunkLvl_le σ; omega⟩

@[simp] theorem chunkLev_val {w : ℕ} (σ : Chunk w) : (chunkLev σ : ℕ) = chunkLvl σ := rfl

/-- **A complete split distribution** (`prelim.tex:206-210`): a distribution on the length-`w`
level-1 words, `w = 2^(ℓ-1)`. -/
abbrev SplitDist (w : ℕ) := RatDist (Chunk w)

/-- **The level-`ℓ` marginal of a complete split distribution.**  `prelim.tex` requires (and
ADVXXZ `global.tex:105-112` re-requires) that a complete split distribution used for the
block `X_i` be supported on words of level `i`; `splitLev` is the distribution against which
that is a statement, and `Consistent.map` transports consistency to it. -/
noncomputable def splitLev {w : ℕ} (P : SplitDist w) : RatDist (Fin (2 * w + 1)) :=
  P.map chunkLev

/-- The level-`ℓ` index sequence carried by a level-1 index sequence. -/
def lvlSeq {w n : ℕ} (Î : Fin n → Chunk w) : Fin n → Fin (2 * w + 1) := fun t => chunkLev (Î t)

/-- **A level-1 index sequence consistent with `P` has a level-`ℓ` index sequence consistent
with `P`'s level-`ℓ` marginal.**  This is the compatibility `prelim.tex:186-190` states
without proof (`Î ∈ I`). -/
theorem Consistent.lvlSeq {w n : ℕ} {P : SplitDist w} {Î : Fin n → Chunk w}
    (h : Consistent P Î) : Consistent (splitLev P) (lvlSeq Î) := by
  classical
  exact h.map chunkLev

end ADVXXZ
end OmegaBound
