import OmegaBound.ADVXXZGeneralGlobalExactFallback37
import OmegaBound.ADVXXZGeneralGlobalExactScaleBridge
import OmegaBound.ADVXXZGeneralCExact33ProducerSelection

set_option autoImplicit false

open OmegaBound Tensor3 OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem rawRegionalTop37 {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m)) :
    Restricts (regionProductZ fun r =>
      topZ q w (globalPopulation g (b*m) xi r).n).tensor (topZ q w (b*m)).tensor := by
  have hn : ∑ r, (globalPopulation g (b*m) xi r).n = b*m := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    simp_rw [globalPopulation_n_cast27 g hg hb xi]
    rw [← Finset.mul_sum, g.A.sum_probR, mul_one]
    simp only [Nat.cast_mul]
  let e : ((r : Fin 6) × Fin (globalPopulation g (b*m) xi r).n) ≃ Fin (b*m) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sigma, Fintype.card_fin] using hn)
  apply ADVXXZ.restricts_of_sub
    (fun x a => x (e.symm a).1 (e.symm a).2)
    (fun y a => y (e.symm a).1 (e.symm a).2)
    (fun z a => z (e.symm a).1 (e.symm a).2)
  intro x y z
  simpa only [regionProductZ, topZ, tensorPower, Fintype.prod_sigma] using
    (Equiv.prod_comp e.symm (fun ri =>
      ∏ i, cwZ q (x ri.1 ri.2 i) (y ri.1 ri.2 i) (z ri.1 ri.2 i))).symm

/-- Mix direct and repaired regions at their unrestricted sources. -/
theorem globalRegionalTop_exactGrid37 {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m))
    (j : (r : Fin 6) → GlobalTargetLabel27 g xi r) (V : Fin 6 → ℕ)
    (hregion : ∀ r,
      Restricts (copiesZ (V r) (globalExactITensor27 q g xi r (j r).val)).tensor
        (topZ q w (globalPopulation g (b*m) xi r).n).tensor) :
  PolyDegeneratesAt ℤ 0 (topZ q w (b*m)).tensor
    (copiesZ (∏ r, V r) (exactGridTensor q g (b*m) xi)).tensor := by
  apply polyDegeneratesAt_of_restricts
  have hgrid := globalSixRegionExactGrid27 (q := q) g xi (fun r => (j r).val)
    (fun r => (j r).property)
  have hcopies : Restricts (copiesZ (∏ r, V r) (exactGridTensor q g (b*m) xi)).tensor
      (copiesZ (∏ r, V r) (regionProductZ fun r =>
        globalExactITensor27 q g xi r (j r).val)).tensor := by
    simpa only [copiesZ] using
      (ADVXXZStage.famDS_const_mono (Finset.univ : Finset (Fin (∏ r, V r))) hgrid)
  exact hcopies.trans ((copiesZ_regionProductZ_restricts V _).trans
    ((regionProductZ_restricts33 _ _ hregion).trans (rawRegionalTop37 q m g hg hb xi)))

theorem globalExactGrid_direct37 {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m)) :
    PolyDegeneratesAt ℤ 0 (topZ q w (b*m)).tensor
      (copiesZ 1 (exactGridTensor q g (b*m) xi)).tensor := by
  let j : (r : Fin 6) → GlobalTargetLabel27 g xi r :=
    fun r => Classical.choice (globalTargetLabel_nonempty27 g xi r)
  simpa using globalRegionalTop_exactGrid37 q m g hg hb xi j (fun _ => 1)
    (fun r => globalExactRegion_direct37 q g xi r (j r).val)

theorem globalRegionalTop_exactGrid37_matches_display :
    GlobalExactEnvelope37.globalRegionalTop_exactGrid37 :=
  @globalRegionalTop_exactGrid37

end
end OmegaBound.ADVXXZGeneral
