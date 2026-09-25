/-
Copyright (c) 2025-2026 Jeroen Zuiddam.
Released under the Apache License 2.0; see LICENSE.
Type classes of sequences (the method of types) and their multinomial count.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Int.NatAbs
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Suppress stylistic warnings
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.unreachableTactic false

/-!
# Type classes (the method of types)

* `IsNType n P`: the distribution `P` is an n-type, that is, `n · P x` is a natural number for
  every `x`;
* `empiricalDist s`: the empirical distribution (the type) of a sequence `s`;
* `TypeClass n P`: the sequences of length `n` whose type is `P`;
* `nTypeCount n P x`: the count `n · P x` of an n-type as a natural number;
* `typeClass_card_eq_multinomial`: the type class of an n-type has the multinomial coefficient
  `n! / ∏ₓ (n · P x)!` as its size.

The other lemmas of the file are steps of the proof of `typeClass_card_eq_multinomial`.

## References

* [Csiszár, Körner, *Information Theory*, Chapter 2]
-/

open scoped ENNReal NNReal

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ### n-Types -/

/-- A probability distribution P is an n-type if nP(x) ∈ ℕ for all x -/
def IsNType (n : ℕ) (P : PMF α) : Prop :=
  ∀ x, ∃ k : ℕ, (P x).toReal = k / n

/-! ### Type Classes -/

/-- The empirical distribution (type) of a sequence -/
noncomputable def empiricalDist (s : Fin n → α) : PMF α :=
  if hn : n = 0 then
    -- For empty sequences, use uniform distribution (arbitrary choice)
    PMF.uniformOfFintype α
  else
    PMF.ofFintype
      (fun x => (Finset.filter (fun i => s i = x) Finset.univ).card / n)
      (by
        -- The filters {i | s i = x} partition Fin n, so their cards sum to n
        -- and dividing by n gives 1
        have hn' : (n : ℝ≥0∞) ≠ 0 := by simp [hn]
        have hn'' : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
        have hsum : ∑ x : α, (Finset.filter (fun i => s i = x) Finset.univ).card = n := by
          trans (Finset.univ : Finset (Fin n)).card
          · rw [← Finset.card_biUnion]
            · congr 1
              ext i
              simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and,
                exists_eq']
            · intro x _ y _ hne
              exact Finset.disjoint_filter.mpr fun i _ hxi hyi => hne (hxi.symm.trans hyi)
          · exact Finset.card_fin n
        have goal_eq : ∀ x, (↑(Finset.filter (fun i => s i = x) Finset.univ).card / ↑n : ℝ≥0∞)
            = (↑n)⁻¹ * ↑(Finset.filter (fun i => s i = x) Finset.univ).card := by
          intro x
          rw [ENNReal.div_eq_inv_mul]
        simp only [goal_eq, ← Finset.mul_sum, ← Nat.cast_sum, hsum,
          ENNReal.inv_mul_cancel hn' hn''])

/-- The type class T^n_P is the set of sequences with empirical distribution P -/
def TypeClass (n : ℕ) (P : PMF α) : Set (Fin n → α) :=
  { s | empiricalDist s = P }

/-- Membership in type class in terms of counts (for n > 0) -/
theorem mem_typeClass_iff {n : ℕ} (hn : 0 < n) {P : PMF α} {s : Fin n → α} :
    s ∈ TypeClass n P ↔
    ∀ x, (Finset.filter (fun i => s i = x) Finset.univ).card = n * (P x).toReal := by
  -- TypeClass n P = { s | empiricalDist s = P }
  -- empiricalDist s = PMF.ofFintype (fun x => count(x) / n) _ when n > 0
  simp only [TypeClass, Set.mem_setOf_eq]
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hn_ne : (n : ℝ≥0∞) ≠ 0 := by exact Nat.cast_ne_zero.mpr hn'
  constructor
  · -- Forward: empiricalDist s = P implies count equality
    intro heq x
    -- empiricalDist s x = P x
    have h : empiricalDist s x = P x := by rw [heq]
    -- Unfold empiricalDist
    simp only [empiricalDist, hn', dite_false, PMF.ofFintype_apply] at h
    -- Now h : count(x) / n = P x (in ℝ≥0∞)
    -- From count(x) / n = P x, multiply both sides by n
    have hmul : ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞) = n * P x := by
      have h2 : (Finset.filter (fun i => s i = x) Finset.univ).card / (n : ℝ≥0∞) * n = P x * n := by
        rw [h]
      rw [ENNReal.div_mul_cancel hn_ne hn_ne_top] at h2
      rw [mul_comm] at h2
      exact h2
    -- Convert to toReal
    have hP_ne_top : P x ≠ ⊤ := PMF.apply_ne_top P x
    have hmul_ne_top : (n : ℝ≥0∞) * P x ≠ ⊤ := ENNReal.mul_ne_top hn_ne_top hP_ne_top
    calc (Finset.filter (fun i => s i = x) Finset.univ).card
        = ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞).toReal := by
            rw [ENNReal.toReal_natCast]
      _ = (n * P x).toReal := by rw [hmul]
      _ = n * (P x).toReal := by
            rw [ENNReal.toReal_mul]
            rw [ENNReal.toReal_natCast]
  · -- Backward: count equality implies empiricalDist s = P
    intro hcount
    ext x
    simp only [empiricalDist, hn', dite_false, PMF.ofFintype_apply]
    have hP_ne_top : P x ≠ ⊤ := PMF.apply_ne_top P x
    -- hcount x : count(x) = n * (P x).toReal
    have h := hcount x
    -- Convert back to ENNReal
    have hcount_ennreal :
        ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞) = n * P x := by
      have hP_nonneg : 0 ≤ (P x).toReal := ENNReal.toReal_nonneg
      have hn_real_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      calc ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞)
          = ENNReal.ofReal (Finset.filter (fun i => s i = x) Finset.univ).card := by
              rw [ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal (n * (P x).toReal) := by rw [h]
        _ = ENNReal.ofReal n * ENNReal.ofReal (P x).toReal := by
              rw [ENNReal.ofReal_mul hn_real_nonneg]
        _ = n * P x := by
              rw [ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hP_ne_top]
    rw [hcount_ennreal]
    rw [mul_comm, ENNReal.mul_div_cancel_right hn_ne hn_ne_top]


/-! ### Type Class Bounds -/

/-- For an n-type, we can compute the count function as a natural number -/
noncomputable def nTypeCount (n : ℕ) (P : PMF α) (x : α) : ℕ :=
  Nat.floor (n * (P x).toReal)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- For an n-type, n * P(x) equals its floor (i.e., is a natural number) -/
theorem nTypeCount_eq (n : ℕ) (P : PMF α) (hP : IsNType n P) (x : α) :
    (nTypeCount n P x : ℝ) = n * (P x).toReal := by
  obtain ⟨k, hk⟩ := hP x
  simp only [nTypeCount]
  by_cases hn : n = 0
  · simp [hn]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [hk]
    have hval : (n : ℝ) * (k / n) = k := by field_simp
    rw [hval]
    have hfloor : ⌊(k : ℝ)⌋₊ = k := Nat.floor_natCast k
    simp [hfloor]

omit [DecidableEq α] [Nonempty α] in
/-- The count function sums to n for an n-type -/
theorem nTypeCount_sum (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    ∑ x, nTypeCount n P x = n := by
  have h_real : (∑ x, nTypeCount n P x : ℝ) = n := by
    simp_rw [nTypeCount_eq n P hP]
    rw [← Finset.mul_sum]
    have hP_sum : ∑ x : α, (P x).toReal = 1 := by
      have h := PMF.tsum_coe P
      rw [tsum_fintype] at h
      have hne : ∀ x, (P x : ℝ≥0∞) ≠ ⊤ := fun x => PMF.apply_ne_top P x
      rw [← ENNReal.toReal_sum (fun x _ => hne x)]
      simp only [h]
      rfl
    simp [hP_sum]
  exact_mod_cast h_real

omit [DecidableEq α] [Nonempty α] in
/-- The sigma type for counting has cardinality n -/
theorem nTypeCount_sigma_card (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    Fintype.card (Σ x : α, Fin (nTypeCount n P x)) = n := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact nTypeCount_sum n P hP

/-- Construct a sequence with prescribed counts using an equivalence -/
noncomputable def sequenceFromCounts (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    Fin n → α := by
  -- The sigma type has cardinality n
  have hcard : Fintype.card (Σ x : α, Fin (nTypeCount n P x)) = n := nTypeCount_sigma_card n P hP
  have hcard' : Fintype.card (Fin n) = Fintype.card (Σ x : α, Fin (nTypeCount n P x)) := by
    simp [hcard]
  -- Use the equivalence
  exact fun i => (Fintype.equivOfCardEq hcard' i).1

/-- The sequence from counts has the right empirical distribution -/
theorem sequenceFromCounts_mem_typeClass (n : ℕ) (P : PMF α) (hP : IsNType n P) (hn : 0 < n) :
    sequenceFromCounts n P hP ∈ TypeClass n P := by
  rw [mem_typeClass_iff hn]
  intro x
  -- The count of x in the sequence equals nTypeCount n P x = n * P(x)
  -- This follows from the construction: equiv maps Fin n bijectively to the sigma type,
  -- where the fiber over x has exactly nTypeCount n P x elements
  have hcard : Fintype.card (Σ y : α, Fin (nTypeCount n P y)) = n := nTypeCount_sigma_card n P hP
  have hcard' : Fintype.card (Fin n) = Fintype.card (Σ y : α, Fin (nTypeCount n P y)) := by
    simp [hcard]
  let e := Fintype.equivOfCardEq hcard'
  -- The count of x equals the cardinality of the fiber {(x, k) | k : Fin (nTypeCount n P x)}
  have hcount : (Finset.filter (fun i => sequenceFromCounts n P hP i = x) Finset.univ).card =
      nTypeCount n P x := by
    -- The fiber over x in the sigma type has exactly nTypeCount n P x elements
    -- and the equivalence maps the preimage of this fiber to the fiber itself
    have hseq_def : ∀ i, sequenceFromCounts n P hP i = (e i).1 := fun _ => rfl
    simp_rw [hseq_def]
    -- Now we need: |{i : Fin n | (e i).1 = x}| = nTypeCount n P x
    -- The preimage under e of the fiber {(y, k) : Σ y, Fin (nTypeCount n P y) | y = x}
    -- is exactly Fintype.card (Fin (nTypeCount n P x)) = nTypeCount n P x
    have hfiber : (Finset.filter (fun i => (e i).1 = x) Finset.univ).card =
        Fintype.card (Fin (nTypeCount n P x)) := by
      -- Use that e is a bijection, so preimage of fiber has same cardinality as fiber
      let fiber := { s : Σ y : α, Fin (nTypeCount n P y) | s.1 = x }
      have heq : (Finset.filter (fun i => (e i).1 = x) Finset.univ) =
          Finset.univ.filter (fun i => e i ∈ fiber) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, fiber]
      rw [heq]
      -- The preimage of fiber under e has cardinality = |fiber|
      have hbij : (Finset.filter (fun i => e i ∈ fiber) Finset.univ).card =
          (Finset.filter (fun s => s ∈ fiber) Finset.univ).card := by
        rw [← Finset.card_map e.toEmbedding]
        congr 1
        ext s
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact hi
        · intro hs
          refine ⟨e.symm s, ?_, by simp⟩
          simp only [Equiv.apply_symm_apply]
          exact hs
      rw [hbij]
      -- The fiber is isomorphic to Fin (nTypeCount n P x)
      have hfib_card :
          (Finset.filter (fun s => s ∈ fiber) Finset.univ).card =
          Fintype.card (Fin (nTypeCount n P x)) := by
        -- Define the embedding from Fin (nTypeCount n P x) to the sigma type
        let embed : Fin (nTypeCount n P x) ↪ (Σ y : α, Fin (nTypeCount n P y)) :=
          ⟨fun k => ⟨x, k⟩,
           fun k1 k2 h => by simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h⟩
        have himage :
            (Finset.filter (fun s => s ∈ fiber)
              (Finset.univ : Finset (Σ y, Fin (nTypeCount n P y)))) =
            (Finset.univ : Finset (Fin (nTypeCount n P x))).map embed := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Function.Embedding.coeFn_mk, embed, fiber]
          constructor
          · intro hs
            -- hs : s.fst = x, so s = ⟨x, s.2⟩ with the right cast
            subst hs
            exact ⟨s.2, rfl⟩
          · rintro ⟨k, rfl⟩
            rfl
        rw [himage, Finset.card_map, Finset.card_univ]
      exact hfib_card
    simp only [Fintype.card_fin] at hfiber
    exact hfiber
  rw [hcount, nTypeCount_eq n P hP]


omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- For n = 0, IsNType 0 P is vacuously false for any valid PMF -/
theorem not_isNType_zero (P : PMF α) : ¬ IsNType 0 P := by
  intro hP
  have h : ∀ x, (P x).toReal = 0 := fun x => by
    obtain ⟨k, hk⟩ := hP x
    simp only [Nat.cast_zero, div_zero] at hk
    exact hk
  have hzero : ∀ x, P x = 0 := fun x =>
    ((ENNReal.toReal_eq_zero_iff (P x)).mp (h x)).resolve_right (PMF.apply_ne_top P x)
  have hsum1 : (∑' x, P x) = 1 := PMF.tsum_coe P
  have hsum0 : (∑' x, P x) = 0 := by
    simp [hzero]
  rw [hsum1] at hsum0
  exact one_ne_zero hsum0

omit [DecidableEq α] [Nonempty α] in
/-- The multinomial identity: n! = multinomial × (∏ k_x!) -/
theorem multinomial_factorial_identity (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    n.factorial =
    Nat.multinomial Finset.univ (nTypeCount n P) * (∏ x : α, (nTypeCount n P x).factorial) := by
  have h := Nat.multinomial_spec (Finset.univ : Finset α) (nTypeCount n P)
  rw [nTypeCount_sum n P hP] at h
  linarith

/-- Permuting a sequence preserves its empirical distribution -/
theorem perm_preserves_empiricalDist (n : ℕ) (s : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    empiricalDist (s ∘ σ) = empiricalDist s := by
  by_cases hn : n = 0
  · simp [empiricalDist, hn]
  · simp only [empiricalDist, hn, dite_false]
    apply PMF.ext
    intro x
    simp only [PMF.ofFintype_apply]
    congr 2
    -- Count of x in s ∘ σ = count of x in s (σ is a bijection)
    conv_lhs => rw [← Finset.card_map σ.toEmbedding]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Equiv.toEmbedding_apply, Function.comp_apply]
    constructor
    · intro ⟨i, hi, heq⟩; rw [← heq, hi]
    · intro hj; exact ⟨σ.symm j, by simp [hj], by simp⟩

omit [Fintype α] [Nonempty α] in
/-- Helper: Finset filter card equals Fintype card of the subtype -/
theorem filter_card_eq_fintype_card (n : ℕ) (s : Fin n → α) (x : α) :
    (Finset.filter (fun i => s i = x) Finset.univ).card = Fintype.card {i : Fin n | s i = x} := by
  rw [Fintype.card_subtype]; congr

/-- For s ∈ TypeClass n P, the count of x equals nTypeCount n P x -/
theorem typeClass_count_eq (n : ℕ) (P : PMF α) (hP : IsNType n P) (hn : 0 < n)
    (s : Fin n → α) (hs : s ∈ TypeClass n P) (x : α) :
    (Finset.filter (fun i => s i = x) Finset.univ).card = nTypeCount n P x := by
  rw [mem_typeClass_iff hn] at hs
  have h := hs x
  have hnTypeCount := nTypeCount_eq n P hP x
  -- h : count = n * P(x).toReal (as ℝ)
  -- hnTypeCount : nTypeCount n P x = n * P(x).toReal (as ℝ)
  have : (Finset.filter (fun i => s i = x) Finset.univ).card = nTypeCount n P x := by
    have heq : ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ) =
               (nTypeCount n P x : ℝ) := by rw [h, hnTypeCount]
    exact_mod_cast heq
  exact this

/-- Construct a permutation between two sequences with the same fiber counts -/
noncomputable def matchingPerm (n : ℕ) (s t : Fin n → α)
    (h : ∀ x, (Finset.filter (fun i => s i = x) Finset.univ).card =
              (Finset.filter (fun i => t i = x) Finset.univ).card) :
    Equiv.Perm (Fin n) := by
  classical
  have hcard : ∀ x, Fintype.card {i : Fin n | s i = x} = Fintype.card {i : Fin n | t i = x} := by
    intro x
    rw [← filter_card_eq_fintype_card, ← filter_card_eq_fintype_card]
    exact h x
  let fiberEq := fun x => Fintype.equivOfCardEq (hcard x)
  let sigmaEq := Equiv.sigmaCongrRight fiberEq
  exact (Equiv.sigmaFiberEquiv s).symm.trans (sigmaEq.trans (Equiv.sigmaFiberEquiv t))

omit [Fintype α] [Nonempty α] in
/-- The matching permutation satisfies t ∘ σ = s -/
theorem matchingPerm_spec (n : ℕ) (s t : Fin n → α)
    (h : ∀ x, (Finset.filter (fun i => s i = x) Finset.univ).card =
              (Finset.filter (fun i => t i = x) Finset.univ).card) :
    t ∘ (matchingPerm n s t h) = s := by
  classical
  funext i
  simp only [Function.comp_apply, matchingPerm, Equiv.trans_apply]
  have hcard : ∀ x, Fintype.card {i : Fin n | s i = x} = Fintype.card {i : Fin n | t i = x} := by
    intro x; rw [← filter_card_eq_fintype_card, ← filter_card_eq_fintype_card]; exact h x
  exact (Fintype.equivOfCardEq (hcard (s i)) ⟨i, rfl⟩).prop

/-- Two sequences in TypeClass have the same fiber counts -/
theorem typeClass_same_counts (n : ℕ) (P : PMF α) (s t : Fin n → α)
    (hs : s ∈ TypeClass n P) (ht : t ∈ TypeClass n P) :
    ∀ x, (Finset.filter (fun i => s i = x) Finset.univ).card =
         (Finset.filter (fun i => t i = x) Finset.univ).card := by
  classical
  by_cases hn : n = 0
  · subst hn
    intro x
    -- Both filters are over Fin 0 = ∅, so both are empty with card 0
    rfl
  · intro x
    simp only [TypeClass, Set.mem_setOf_eq] at hs ht
    have hs_count : (Finset.filter (fun i => s i = x) Finset.univ).card / (n : ℝ≥0∞) = P x := by
      have : empiricalDist s x = P x := by rw [hs]
      simp only [empiricalDist, hn, dite_false, PMF.ofFintype_apply] at this
      exact this
    have ht_count : (Finset.filter (fun i => t i = x) Finset.univ).card / (n : ℝ≥0∞) = P x := by
      have : empiricalDist t x = P x := by rw [ht]
      simp only [empiricalDist, hn, dite_false, PMF.ofFintype_apply] at this
      exact this
    have hn_ne : (n : ℝ≥0∞) ≠ 0 := by simp [hn]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    -- From a/n = b/n, derive a = b (multiply both sides by n)
    have heq_div : (Finset.filter (fun i => s i = x) Finset.univ).card / (n : ℝ≥0∞) =
                   (Finset.filter (fun i => t i = x) Finset.univ).card / (n : ℝ≥0∞) := by
      rw [hs_count, ht_count]
    have hmul : ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞) =
                (Finset.filter (fun i => t i = x) Finset.univ).card := by
      have hs_mul : (Finset.filter (fun i => s i = x) Finset.univ).card / (n : ℝ≥0∞) * n =
                    (Finset.filter (fun i => s i = x) Finset.univ).card :=
        ENNReal.div_mul_cancel hn_ne hn_ne_top
      have ht_mul : (Finset.filter (fun i => t i = x) Finset.univ).card / (n : ℝ≥0∞) * n =
                    (Finset.filter (fun i => t i = x) Finset.univ).card :=
        ENNReal.div_mul_cancel hn_ne hn_ne_top
      calc ((Finset.filter (fun i => s i = x) Finset.univ).card : ℝ≥0∞)
          = (Finset.filter (fun i => s i = x) Finset.univ).card / n * n := hs_mul.symm
        _ = (Finset.filter (fun i => t i = x) Finset.univ).card / n * n := by rw [heq_div]
        _ = (Finset.filter (fun i => t i = x) Finset.univ).card := ht_mul
    exact_mod_cast hmul

/-- Two sequences in the same TypeClass are related by a permutation -/
theorem typeClass_related_by_perm (n : ℕ) (P : PMF α) (s t : Fin n → α)
    (hs : s ∈ TypeClass n P) (ht : t ∈ TypeClass n P) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, t i = s (σ i) := by
  classical
  have hcount := typeClass_same_counts n P s t hs ht
  refine ⟨(matchingPerm n s t hcount).symm, fun i => ?_⟩
  have hspec := matchingPerm_spec n s t hcount
  have h := congr_fun hspec ((matchingPerm n s t hcount).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h

/-- Subgroup Nat.card equals Set ncard. -/
theorem subgroup_nat_card_eq_ncard (G : Type*) [Group G] (H : Subgroup G) :
    Nat.card ↥H = ((H : Set G)).ncard := by
  have : (H : Set G) = {x : G | x ∈ H} := rfl
  rw [this]
  congr 1

/-- The type class cardinality equals the multinomial coefficient.
    For an n-type P with counts k_x = nP(x), we have |T^n_P| = n! / ∏_x k_x!

    The proof uses the orbit-stabilizer theorem:
    - TypeClass n P is the orbit of any s₀ ∈ TypeClass under permutation action
    - |orbit| × |stabilizer| = |Perm (Fin n)| = n!
    - |stabilizer of s₀| = ∏_x (k_x)! by DomMulAct.stabilizer_card
    - Therefore |TypeClass| = n! / ∏_x k_x! = multinomial

    The key lemmas are:
    - typeClass_related_by_perm: sequences in TypeClass differ by a permutation
    - DomMulAct.stabilizer_card: stabilizer size is product of factorial of fiber sizes
    - multinomial_factorial_identity: n! = multinomial × ∏_x k_x! -/
theorem typeClass_card_eq_multinomial (n : ℕ) (P : PMF α) (hP : IsNType n P) :
    (TypeClass n P).ncard = Nat.multinomial Finset.univ (nTypeCount n P) := by
  -- Handle n = 0 case: IsNType 0 P is false
  by_cases hn : n = 0
  · exfalso; subst hn; exact not_isNType_zero P hP
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  classical
  -- The TypeClass is finite
  have hfin : (TypeClass n P).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  -- Get a representative sequence in TypeClass
  let s₀ := sequenceFromCounts n P hP
  have hs₀ : s₀ ∈ TypeClass n P := sequenceFromCounts_mem_typeClass n P hP hn_pos
  -- The stabilizer of s₀ (perms σ with s₀ ∘ σ = s₀) has cardinality ∏_x k_x!
  have hstab_card : {σ : Equiv.Perm (Fin n) | s₀ ∘ σ = s₀}.ncard =
      ∏ x : α, (nTypeCount n P x).factorial := by
    rw [DomMulAct.stabilizer_ncard]
    congr 1
    funext x
    congr 1
    -- Need to show {i | s₀ i = x}.ncard = nTypeCount n P x
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    -- Now we have (Finset.filter (fun i => s₀ i = x) Finset.univ).card = nTypeCount n P x
    exact typeClass_count_eq n P hP hn_pos s₀ hs₀ x
  -- The key equation: |TypeClass| × ∏_x k_x! = n!
  -- This follows from the fiber-counting argument:
  -- - Map φ : Perm (Fin n) → (Fin n → α), φ(σ) = s₀ ∘ σ
  -- - Image is TypeClass (by typeClass_related_by_perm and perm_preserves_empiricalDist)
  -- - Each fiber has size |{σ | s₀ ∘ σ = t}| = |{τ | s₀ ∘ τ = s₀}| = ∏_x k_x!
  -- - Therefore n! = |TypeClass| × ∏_x k_x!
  have h_id := multinomial_factorial_identity n P hP
  -- From h_id: n! = multinomial × ∏_x k_x!
  -- From hstab_card: |stabilizer| = ∏_x k_x!
  -- The counting argument:
  -- - proj : Perm (Fin n) → TypeClass, proj(σ) = s₀ ∘ σ is surjective
  --   (by typeClass_related_by_perm)
  -- - Each fiber has size |stabilizer| = ∏_x k_x!
  --   (fiber(t) ≃ stabilizer via σ ↦ σ ∘ τ⁻¹)
  -- - n! = |Perm (Fin n)| = ∑_{t ∈ TypeClass} |fiber(t)| = |TypeClass| × |stabilizer|
  -- - Therefore |TypeClass| = n! / ∏_x k_x! = multinomial
  have hstab_formula := hstab_card
  have hprod_pos : 0 < ∏ x : α, (nTypeCount n P x).factorial := by
    apply Finset.prod_pos
    intro x _
    exact Nat.factorial_pos _
  -- The counting equation |TypeClass| × |stabilizer| = n! follows from:
  -- 1. The projection map σ ↦ s₀ ∘ σ partitions Perm (Fin n) into fibers
  --    over TypeClass
  -- 2. All fibers have size |stabilizer|
  --    (bijection σ ↦ σ ∘ τ⁻¹ between fiber(t) and stabilizer)
  -- 3. Sum of fiber sizes = n!
  -- Combined with h_id: n! = multinomial × |stabilizer|
  -- Therefore |TypeClass| = multinomial
  -- This requires orbit-stabilizer identity with technical Set.ncard work.
  -- The key lemmas are already proven above.
  have hcount : (TypeClass n P).ncard * ∏ x : α, (nTypeCount n P x).factorial = n.factorial := by
    rw [← hstab_formula]
    -- Use orbit-stabilizer theorem with arrowAction
    letI inst := @arrowAction (Equiv.Perm (Fin n)) (Fin n) α _ _
    -- orbit-stabilizer: index(stabilizer) * |stabilizer| = |G|
    have h_orbit_stab := Subgroup.index_mul_card (MulAction.stabilizer (Equiv.Perm (Fin n)) s₀)
    -- index(stabilizer) = orbit.ncard
    have h_index := MulAction.index_stabilizer (Equiv.Perm (Fin n)) s₀
    -- Nat.card (Perm (Fin n)) = n!
    have h_perm_card : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    -- orbit = TypeClass
    have h_orbit : (MulAction.orbit (Equiv.Perm (Fin n)) s₀ : Set (Fin n → α)) = TypeClass n P := by
      ext t
      simp only [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨σ, rfl⟩
        have hsmul : σ • s₀ = s₀ ∘ σ.symm := by ext i; rfl
        rw [hsmul]
        have := perm_preserves_empiricalDist n s₀ σ.symm
        simp only [TypeClass, Set.mem_setOf_eq] at hs₀ ⊢
        rw [this, hs₀]
      · intro ht
        obtain ⟨τ, hτ⟩ := typeClass_related_by_perm n P s₀ t hs₀ ht
        use τ.symm
        ext i
        change s₀ (τ.symm.symm i) = t i
        rw [Equiv.symm_symm]
        exact (hτ i).symm
    -- stabilizer = {σ | s₀ ∘ σ = s₀}
    have h_stab : (MulAction.stabilizer (Equiv.Perm (Fin n)) s₀ : Set (Equiv.Perm (Fin n))) =
        {σ : Equiv.Perm (Fin n) | s₀ ∘ σ = s₀} := by
      ext σ
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      simp only [Set.mem_setOf_eq]
      have hsmul : σ • s₀ = s₀ ∘ σ.symm := by ext i; rfl
      rw [hsmul]
      constructor
      · intro h; ext i
        have h' := congr_fun h (σ i)
        simp only [Function.comp_apply, Equiv.symm_apply_apply] at h'
        exact h'.symm
      · intro h; ext i
        have h' := congr_fun h (σ.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at h'
        exact h'.symm
    -- Combine orbit-stabilizer equations
    rw [h_index] at h_orbit_stab
    rw [h_orbit] at h_orbit_stab
    rw [h_perm_card] at h_orbit_stab
    have h_stab_ncard : Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) s₀) =
        {σ : Equiv.Perm (Fin n) | s₀ ∘ σ = s₀}.ncard := by
      rw [subgroup_nat_card_eq_ncard, h_stab]
    rw [h_stab_ncard] at h_orbit_stab
    exact h_orbit_stab
  -- From hcount: |TypeClass| × ∏_x k_x! = n!
  -- From h_id: n! = multinomial × ∏_x k_x!
  -- Therefore: |TypeClass| × ∏_x k_x! = multinomial × ∏_x k_x!
  -- Since ∏_x k_x! > 0, we have |TypeClass| = multinomial
  have heq : (TypeClass n P).ncard * ∏ x : α, (nTypeCount n P x).factorial =
      Nat.multinomial Finset.univ (nTypeCount n P) * ∏ x : α, (nTypeCount n P x).factorial := by
    rw [hcount, h_id]
  exact Nat.eq_of_mul_eq_mul_right hprod_pos heq
