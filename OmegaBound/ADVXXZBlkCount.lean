import OmegaBound.ADVXXZSplitDist
import OmegaBound.Combinatorics.MethodOfTypes

/-!
# Block counts: `N_xblock = 2^{H(β)·n ± o(n)}`

Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou (`global.tex:147-152`,
`constituent.tex:186-190`), via Vassilevska Williams–Xu–Xu–Zhou's "well-known combinatorial
fact" (`prelim.tex:191-194`), count the level-1 variable blocks whose index sequence is
consistent with a complete split distribution `β`, and assert

  `N_xblock = binom(n; β(σ)·n : σ) = 2^{H(β)·n ± o(n)}`.

`ADVXXZSplitDist` already supplies the right-hand equality with the `o(1)` explicit
(`RatDist.two_pow_le_multinomial_cnt`, `RatDist.multinomial_cnt_le_two_pow`) and with the
integrality obligation discharged by the `RatDist` convention.  What was missing was the
*left*-hand equality — the purely combinatorial count of sequences of a prescribed type.
It is **not** in Mathlib, but it **is** in `OmegaBound.Combinatorics.MethodOfTypes`,

```lean
-- OmegaBound/Combinatorics/MethodOfTypes.lean, top level, no namespace
theorem typeClass_card_eq_multinomial (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    (TypeClass n P).ncard = Nat.multinomial Finset.univ (nTypeCount n P)
```

proved there by orbit–stabiliser.  This file bridges it to the `RatDist`/`typeCnt`
formulation and assembles the two-sided block count.

## The bridge

`TypeClass n P` is `{s | empiricalDist s = P}`, an equality of `PMF`s in `ℝ≥0∞`, and
`nTypeCount n P x = ⌊n·P(x)⌋₊`.  Given a count vector `k : ι → ℕ` with `∑ k = n` one
manufactures the `PMF` `σ ↦ k σ / n` (`cntPMF`), checks `IsNType`, identifies `nTypeCount`
with `k` and `TypeClass` with the type-`k` sequences, and reads off

`card {f : Fin n → ι | ∀ i, typeCnt f i = k i} = Nat.multinomial univ k`

(`card_filter_typeCnt`).  Everything downstream is then a `RatDist` restatement.

## Main definitions

* `blocks P n` — the level-1 variable blocks with index sequence consistent with `P`; the
  source's `X`-block set.

## Main results

* `card_filter_typeCnt` — sequences of a prescribed type are counted by the multinomial
  coefficient (the missing arithmetic input, bridged from `typeClass_card_eq_multinomial`).
* `card_blocks` — `N_xblock = binom(n; P.cnt n)` exactly.
* `card_blocks_le_two_pow`, `two_pow_le_card_blocks` — **the two-sided block count
  `2^{n(H(β) − o(1))} ≤ N_xblock ≤ 2^{n·H(β)}`**, the `o(1)` being
  `errRate (card ι) n / log 2 = (|ι|−1)·log₂(n+1)/n`.
* `tendsto_blockErr` — that `o(1)` really is `o(1)`.
* `card_blocks_splitDist_le_two_pow`, `two_pow_le_card_blocks_splitDist` — the same for a
  complete split distribution, where the alphabet size is `3^w`, `w = 2^{ℓ-1}`.

## A source under-specification

`prelim.tex:191-194` states the estimate for a **fixed** distribution `α` as `N → ∞`, but the
laser method applies it with `α` depending on `N` (indeed on `ℓ` and on the region), so the
`o(1)` must be uniform over the family.  It is: the bound proved here has the *explicit*
error `errRate s N = (s−1)·log(N+1)/N`, which depends on the alphabet size and the length
only, never on the distribution.  Nothing is lost, but the source's statement does not by
itself license the use it is put to.
-/

open Finset
open scoped ENNReal

namespace OmegaBound
namespace ADVXXZ

/-! ## Sequences of a prescribed type -/

section PrescribedType

variable {ι : Type*} [Fintype ι]

/-- The distribution `i ↦ k i / n` attached to a count vector, as a `PMF`.  This is the
object the type-counting theorem `typeClass_card_eq_multinomial` is stated about. -/
private noncomputable def cntPMF (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) (hn : 0 < n) :
    PMF ι :=
  PMF.ofFintype (fun i => (k i : ℝ≥0∞) / (n : ℝ≥0∞)) (by
    have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    calc ∑ i, ((k i : ℝ≥0∞) / (n : ℝ≥0∞))
        = ∑ i, (n : ℝ≥0∞)⁻¹ * (k i : ℝ≥0∞) :=
          Finset.sum_congr rfl fun i _ => ENNReal.div_eq_inv_mul
      _ = (n : ℝ≥0∞)⁻¹ * ∑ i, (k i : ℝ≥0∞) := by rw [Finset.mul_sum]
      _ = (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞) := by rw [← Nat.cast_sum, hk]
      _ = 1 := ENNReal.inv_mul_cancel hn0 hnt)

private theorem cntPMF_toReal (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) (hn : 0 < n) (i : ι) :
    (cntPMF k n hk hn i).toReal = (k i : ℝ) / (n : ℝ) := by
  rw [cntPMF, PMF.ofFintype_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

private theorem isNType_cntPMF (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) (hn : 0 < n) :
    IsNType n (cntPMF k n hk hn) := fun i => ⟨k i, cntPMF_toReal k n hk hn i⟩

private theorem nTypeCount_cntPMF (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) (hn : 0 < n) :
    nTypeCount n (cntPMF k n hk hn) = k := by
  funext i
  have h := nTypeCount_eq n (cntPMF k n hk hn) (isNType_cntPMF k n hk hn) i
  rw [cntPMF_toReal] at h
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h2 : ((nTypeCount n (cntPMF k n hk hn) i : ℕ) : ℝ) = ((k i : ℕ) : ℝ) := by
    rw [h]
    field_simp
  exact_mod_cast h2

private theorem typeClass_cntPMF [DecidableEq ι] [Nonempty ι]
    (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) (hn : 0 < n) :
    TypeClass n (cntPMF k n hk hn) = {f : Fin n → ι | ∀ i, typeCnt f i = k i} := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  ext f
  rw [mem_typeClass_iff hn, Set.mem_setOf_eq]
  refine forall_congr' fun i => ?_
  rw [cntPMF_toReal]
  constructor
  · intro h
    have h2 : ((typeCnt f i : ℕ) : ℝ) = ((k i : ℕ) : ℝ) := by
      rw [show ((typeCnt f i : ℕ) : ℝ) = ((Finset.univ.filter fun t => f t = i).card : ℝ) from rfl,
        h]
      field_simp
    exact_mod_cast h2
  · intro h
    rw [show ((Finset.univ.filter fun t => f t = i).card : ℝ) = ((typeCnt f i : ℕ) : ℝ) from rfl,
      h]
    field_simp

/-- **Sequences of a prescribed type are counted by the multinomial coefficient.**  This is
the arithmetic input the block count needs; Mathlib does not have it, and it is bridged here
from `typeClass_card_eq_multinomial` of `OmegaBound.Combinatorics.MethodOfTypes`. -/
theorem card_filter_typeCnt [DecidableEq ι] [Nonempty ι] {n : ℕ} (k : ι → ℕ)
    (hk : ∑ i, k i = n) :
    (Finset.univ.filter fun f : Fin n → ι => ∀ i, typeCnt f i = k i).card
      = Nat.multinomial Finset.univ k := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hall : ∀ i : ι, k i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff.1 hk) i (Finset.mem_univ i)
    have hfilter : (Finset.univ.filter fun f : Fin 0 → ι => ∀ i, typeCnt f i = k i)
        = Finset.univ := by
      refine Finset.filter_true_of_mem fun f _ i => ?_
      rw [hall i, typeCnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun t _ => absurd t.isLt (Nat.not_lt_zero _)
    rw [hfilter]
    have hcard : (Finset.univ : Finset (Fin 0 → ι)).card = 1 := by
      simp
    rw [hcard, Nat.multinomial]
    simp [hall]
  · have h := typeClass_card_eq_multinomial n (cntPMF k n hk hn) (isNType_cntPMF k n hk hn)
    rw [typeClass_cntPMF, nTypeCount_cntPMF] at h
    rw [← h]
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]

end PrescribedType

/-! ## The block count -/

section BlockCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The level-1 variable blocks with index sequence consistent with `P`.**  The source's
`X`-blocks: `N_xblock` is its cardinality. -/
def blocks (P : RatDist ι) (n : ℕ) : Finset (Fin n → ι) :=
  Finset.univ.filter fun f => Consistent P f

theorem mem_blocks {P : RatDist ι} {f : Fin n → ι} : f ∈ blocks P n ↔ Consistent P f := by
  rw [blocks, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩

/-- **`N_xblock = binom(n; β(σ)·n : σ)`**, exactly, under the integrality convention. -/
theorem card_blocks (P : RatDist ι) (hd : P.den ∣ n) :
    (blocks P n).card = Nat.multinomial Finset.univ (P.cnt n) := by
  haveI := P.nonempty
  have hfilter : blocks P n
      = Finset.univ.filter fun f : Fin n → ι => ∀ i, typeCnt f i = P.cnt n i := by
    rw [blocks]
    refine Finset.filter_congr fun f _ => ?_
    simpa using consistent_iff_cnt P f hd
  rw [hfilter]
  exact card_filter_typeCnt (P.cnt n) (P.sum_cnt hd)

/-- **`N_xblock ≤ 2^{n·H(β)}`.**  The upper half of `global.tex:147-152`. -/
theorem card_blocks_le_two_pow (P : RatDist ι) (hn : 0 < n) (hd : P.den ∣ n) :
    (((blocks P n).card : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * Entropy.H₂ Finset.univ P.probR) := by
  rw [card_blocks P hd]
  exact P.multinomial_cnt_le_two_pow hn hd

/-- **`2^{n(H(β) − o(1))} ≤ N_xblock`.**  The lower half of `global.tex:147-152`, with the
`o(1)` explicit: it is `errRate (card ι) n / log 2 = (|ι|−1)·log₂(n+1)/n`, which
`tendsto_blockErr` sends to `0`. -/
theorem two_pow_le_card_blocks (P : RatDist ι) (hn : 0 < n) (hd : P.den ∣ n) :
    (2 : ℝ) ^ ((n : ℝ) * (Entropy.H₂ Finset.univ P.probR
        - Entropy.errRate (Fintype.card ι) n / Real.log 2))
      ≤ (((blocks P n).card : ℕ) : ℝ) := by
  rw [card_blocks P hd]
  exact P.two_pow_le_multinomial_cnt hn hd

/-- The `o(1)` of the block count really is `o(1)`. -/
theorem tendsto_blockErr (s : ℕ) :
    Filter.Tendsto (fun N : ℕ => Entropy.errRate s N / Real.log 2) Filter.atTop (nhds 0) := by
  have h := Entropy.tendsto_errRate s
  simpa using h.div_const (Real.log 2)

end BlockCount

/-! ## The block count for a complete split distribution

The alphabet of a complete split distribution of width `w = 2^{ℓ-1}` is `Chunk w`, of size
`3^w`; that is the `s` in the error term. -/

section SplitBlockCount

variable {w n : ℕ}

theorem card_chunk (w : ℕ) : Fintype.card (Chunk w) = 3 ^ w := by
  simp [Chunk]

/-- **`N_xblock ≤ 2^{n·H(β)}` for a complete split distribution.** -/
theorem card_blocks_splitDist_le_two_pow (b : SplitDist w) (hn : 0 < n) (hd : b.den ∣ n) :
    (((blocks b n).card : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * Entropy.H₂ Finset.univ b.probR) :=
  card_blocks_le_two_pow b hn hd

/-- **`2^{n(H(β) − (3^w−1)·log₂(n+1)/n)} ≤ N_xblock` for a complete split distribution.** -/
theorem two_pow_le_card_blocks_splitDist (b : SplitDist w) (hn : 0 < n) (hd : b.den ∣ n) :
    (2 : ℝ) ^ ((n : ℝ) * (Entropy.H₂ Finset.univ b.probR
        - Entropy.errRate (3 ^ w) n / Real.log 2))
      ≤ (((blocks b n).card : ℕ) : ℝ) := by
  have h := two_pow_le_card_blocks b hn hd
  rwa [card_chunk w] at h

end SplitBlockCount

end ADVXXZ
end OmegaBound
