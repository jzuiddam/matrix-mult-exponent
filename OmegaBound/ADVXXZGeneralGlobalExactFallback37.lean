import OmegaBound.ADVXXZGeneralGlobalExactDirect37
import OmegaBound.ADVXXZGeneralGlobalExactSelectedRegion37

set_option autoImplicit false

open OmegaBound Tensor3 OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem below_reserve37 (T B M R : ℝ) (hM : 0 < M) (hR : 0 < R)
    (h : (11 / 20 : ℝ) * T * B / M^2 < R) :
    (11 / 40 : ℝ) * T * B / (M^2 * R) ≤ 1 := by
  rw [div_lt_iff₀ (sq_pos_of_pos hM)] at h
  rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hM) hR)]
  nlinarith [mul_pos (sq_pos_of_pos hM) hR]

/-- Quantitative repair when the reserve fits, direct copy otherwise. -/
theorem globalRegionCopies_fallback37 {w b M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (hb : GlobalIntegral g b) (floor m : ℕ) (hm : 0 < m)
    (xi : ExactGrid g (b*m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hgrade : (globalPopulation g (b*m) xi r).grade < M)
    (hAP : HashAPFree B) (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (j0 : GlobalTargetLabel27 g xi r) (b0 : GlobalBucketLabel27 B)
    (hn : (globalPopulation g (b*m) xi r).n ≠ 0) :
  ∃ V : ℕ, 0 < V ∧
    (11 / 40 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
      Fintype.card (GlobalBucketLabel27 B) /
      ((M : ℝ)^2 * (repairReserve (2 * (globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ))
      ≤ (V : ℝ) ∧
    Restricts (copiesZ V (globalExactITensor27 q g xi r j0.val)).tensor
      (topZ q w (globalPopulation g (b*m) xi r).n).tensor := by
  by_cases hR :
      (repairReserve (2 * (globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ) ≤
      (11 / 20 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
        Fintype.card (GlobalBucketLabel27 B) / (M : ℝ)^2
  · obtain ⟨omega, V, hV, hQ, hres⟩ := globalGoodFamily_repair_selected_region_bound27
      q g hg hw hb floor m hm xi hxi r B hprime hodd hgrade hdemand j0 b0 hn hR
    exact ⟨V, hV, hQ, hres.trans
      (globalSelectedRegion_restrict_top37 q m g hg hb xi hxi r B omega
        hprime hodd hgrade hAP)⟩
  · refine ⟨1, Nat.zero_lt_one, ?_, globalExactRegion_direct37 q g xi r j0.val⟩
    simp only [Nat.cast_one]
    exact below_reserve37 _ _ (M : ℝ)
      (repairReserve (2 * (globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ)
      (by exact_mod_cast hprime.pos)
      (by exact_mod_cast (repairReserve_pos (2 * (globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W))))
      (lt_of_not_ge hR)

theorem globalRegionCopies_fallback37_matches_display :
    GlobalExactEnvelope37.globalRegionCopies_fallback37 :=
  @globalRegionCopies_fallback37

end
end OmegaBound.ADVXXZGeneral
