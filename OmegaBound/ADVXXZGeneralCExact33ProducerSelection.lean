import OmegaBound.ADVXXZGeneralActiveEmbeddingsContinuation
import OmegaBound.ADVXXZGeneralCExact33Guard
import OmegaBound.ADVXXZGeneralCExact33ProducerEmpty
import OmegaBound.ADVXXZGeneralRepairFibresAssembly

set_option autoImplicit false

/-!
# Restriction lemmas for the constituent good broken family

The product/sum interchange over the six regions, monotonicity of the six-region product and of
reindexed dependent sums under restriction, the valid and invalid branches of
`goodBrokenFamilyZ25`, and `goodBrokenFamily_mono33`: shrinking the selection is a restriction
of the good broken family.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The three-fold product/sum interchange over the six regions.  (Constituent copy of the
private `prod_sum3IntGB27` of `ADVXXZGeneralGlobalExactBrokenAssembly.lean`.) -/
theorem prod_sum3Int33 {n : ℕ}
    {X Y Z : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, Fintype (Z i)] (f : ∀ i, X i → Y i → Z i → ℤ) :
    (∏ i, ∑ a : X i, ∑ b : Y i, ∑ c : Z i, f i a b c) =
      ∑ a : (∀ i, X i), ∑ b : (∀ i, Y i), ∑ c : (∀ i, Z i),
        ∏ i, f i (a i) (b i) (c i) := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (X i)))
      (fun i a => ∑ b : Y i, ∑ c : Z i, f i a b c), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Y i)))
      (fun i b => ∑ c : Z i, f i (a i) b c), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Z i)))
      (fun i c => f i (a i) (b i) c), Fintype.piFinset_univ]

/-- The six-region product is monotone under restriction.  (Constituent copy of the private
`regionProductZ_restrictsGB27`.) -/
theorem regionProductZ_restricts33 (S T : Fin 6 → ITensor)
    (h : ∀ r, Restricts (S r).tensor (T r).tensor) :
    Restricts (regionProductZ S).tensor (regionProductZ T).tensor := by
  classical
  choose A1 A2 A3 hA using h
  refine ⟨fun x a => ∏ r, A1 r (x r) (a r),
    fun y b => ∏ r, A2 r (y r) (b r),
    fun z c => ∏ r, A3 r (z r) (c r), ?_⟩
  funext x y z
  have hfac : ∀ r, (S r).tensor (x r) (y r) (z r) =
      ∑ a : (T r).X, ∑ b : (T r).Y, ∑ c : (T r).Z,
        A1 r (x r) a * A2 r (y r) b * A3 r (z r) c *
          (T r).tensor a b c := by
    intro r
    rw [hA r]
    rfl
  have hleft : (regionProductZ S).tensor x y z =
      ∏ r, ∑ a : (T r).X, ∑ b : (T r).Y, ∑ c : (T r).Z,
        A1 r (x r) a * A2 r (y r) b * A3 r (z r) c *
          (T r).tensor a b c := by
    simp only [regionProductZ]
    exact Finset.prod_congr rfl fun r _ => hfac r
  rw [hleft, prod_sum3Int33]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [regionProductZ, Finset.prod_mul_distrib]

/-- Reindexing a dependent sum along an injection is a restriction.  (Constituent copy of the
private `dependentSumZ_restricts_injectiveGB27`.) -/
theorem dependentSumZ_restricts_injective33
    {iota kappa : Type} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (T : kappa → ITensor) (e : iota → kappa) (he : Function.Injective e) :
    Restricts (dependentSumZ fun i => T (e i)).tensor (dependentSumZ T).tensor := by
  classical
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨e x.1, x.2⟩) (fun y => ⟨e y.1, y.2⟩)
    (fun z => ⟨e z.1, z.2⟩) ?_
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
  simp only [dependentSumZ]
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp
    · have heac : e a ≠ e c := fun h => hac (he h)
      simp [hac, heac]
  · have heab : e a ≠ e b := fun h => hab (he h)
    simp [hab, heab]

/-- The valid branch of the good broken family. -/
theorem goodBrokenFamilyZ25_valid_eq {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hvalid : ValidStageHashes p d b m M B) :
    goodBrokenFamilyZ25 q p d b ε m M B ω J =
      regionProductZ (fun r =>
        if (stagePopulationAt q p d b m r).n = 0 then unitFamilyZ else
          dependentSumZ fun j : {j // j ∈ J r} =>
            stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val) := by
  classical
  unfold goodBrokenFamilyZ25
  exact if_pos hvalid

/-- The invalid branch of the good broken family. -/
theorem goodBrokenFamilyZ25_invalid_eq {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hvalid : ¬ ValidStageHashes p d b m M B) :
    goodBrokenFamilyZ25 q p d b ε m M B ω J = emptyFamilyZ := by
  classical
  unfold goodBrokenFamilyZ25
  exact if_neg hvalid

/-- Shrinking the selection is a restriction of the good broken family. -/
theorem goodBrokenFamily_mono33 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J K : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hJK : ∀ r, J r ⊆ K r) :
    Restricts (goodBrokenFamilyZ25 q p d b ε m M B ω J).tensor
      (goodBrokenFamilyZ25 q p d b ε m M B ω K).tensor := by
  classical
  by_cases hvalid : ValidStageHashes p d b m M B
  · rw [goodBrokenFamilyZ25_valid_eq q p d b ε m M B ω J hvalid,
      goodBrokenFamilyZ25_valid_eq q p d b ε m M B ω K hvalid]
    refine regionProductZ_restricts33 _ _ (fun r => ?_)
    by_cases hn : (stagePopulationAt q p d b m r).n = 0
    · rw [if_pos hn, if_pos hn]
      exact ADVXXZ.restricts_of_sub (fun x => x) (fun y => y) (fun z => z) (fun _ _ _ => rfl)
    · rw [if_neg hn, if_neg hn]
      refine dependentSumZ_restricts_injective33
        (iota := {j // j ∈ J r}) (kappa := {j // j ∈ K r})
        (fun j => stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val)
        (fun j => ⟨j.1, hJK r j.2⟩) ?_
      intro a c hac
      exact Subtype.ext (congrArg (fun t : {j // j ∈ K r} => t.val) hac)
  · rw [goodBrokenFamilyZ25_invalid_eq q p d b ε m M B ω J hvalid]
    exact restricts_of_isEmpty_X _ _ emptyFamilyZ_isEmpty_X

end
end OmegaBound.ADVXXZGeneral
end
