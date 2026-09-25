import OmegaBound.ADVXXZGeneralGlobalExactRegionalRepair
import OmegaBound.ADVXXZGeneralMap

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

/-- The literal regional branch occurring inside `globalBrokenFamilyZ`. -/
def globalSelectedRegionFamily27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M) : ITensor :=
  if (globalPopulation g n xi r).n = 0 then unitFamilyZ else
    dependentSumZ fun j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega} =>
      globalBrokenCopyZ q g n xi r M B omega j.val


private theorem dependentSumZ_restricts_injectiveGB27
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

set_option maxHeartbeats 1000000 in
-- Both dependent sums carry label-indexed leg types.
/-- The paper-good broken copies embed in the actual selected regional broken family. -/
theorem globalPaperGoodTargets_restricts_region27 {w b M : ℕ} (q : ℕ)
    (g : GlobalSpec w) (m : ℕ) (xi : ExactGrid g (b * m)) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b * m) xi r) M)
    (j0 : GlobalTargetLabel27 g xi r)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    Restricts
      (dependentSumZ fun k : {k // k ∈ globalPaperGoodTargets27 g m xi r B omega j0} =>
        globalBrokenCopyZ q g (b * m) xi r M B omega k.val.val).tensor
      (globalSelectedRegionFamily27 q g xi r B omega).tensor := by
  let J := globalPaperGoodTargets27 g m xi r B omega j0
  let S := selected (rolePopulation (globalPopulation g (b * m) xi r) (g.perm r))
    M B omega
  let e : {k // k ∈ J} → {j // j ∈ S} := fun k =>
    ⟨k.val.val, by
      have hselectedTarget : k.val ∈ globalSelectedTargets27 g xi r B omega :=
        (Finset.mem_filter.mp (by simpa only [J, globalPaperGoodTargets27] using k.property)).1
      simpa only [S, globalSelectedTargets27, Finset.mem_filter,
        Finset.mem_attach, true_and] using hselectedTarget⟩
  have he : Function.Injective e := by
    intro a c h
    have hraw : a.val.val = c.val.val :=
      congrArg (fun x : {j // j ∈ S} => x.val) h
    exact Subtype.ext (Subtype.ext hraw)
  have hsum := dependentSumZ_restricts_injectiveGB27
    (fun j : {j // j ∈ S} =>
      globalBrokenCopyZ q g (b * m) xi r M B omega j.val) e he
  rw [globalSelectedRegionFamily27, if_neg hn]
  simpa only [J, S, e] using hsum

set_option maxHeartbeats 1000000 in
-- The chosen hash outcome occurs in the dependent target tensor.

private theorem prod_sum3IntGB27 {n : ℕ}
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

private theorem regionProductZ_restrictsGB27 (S T : Fin 6 → ITensor)
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
  rw [hleft, prod_sum3IntGB27]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [regionProductZ, Finset.prod_mul_distrib]


end
end OmegaBound.ADVXXZGeneral
end
