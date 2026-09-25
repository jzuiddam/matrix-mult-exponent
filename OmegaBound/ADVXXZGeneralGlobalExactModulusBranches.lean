import OmegaBound.ADVXXZGeneralGlobalExactGridReindex
import OmegaBound.ADVXXZGeneralGlobalExactDemand

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem rothNumberNat_posGrid27 {k : ℕ} (hk : 1 ≤ k) :
    0 < rothNumberNat k := by
  have hb := CW90.card_apFree_zmod_lower k
  have hpos : (0 : ℝ) < (k : ℝ) * Real.exp (-4 * Real.sqrt (Real.log k)) := by
    have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hreal : (0 : ℝ) < (rothNumberNat k : ℝ) := lt_of_lt_of_le hpos hb
  exact_mod_cast hreal

/-- The simultaneous modulus choice also provides an actual AP-free bucket index in every
    region, including zero-population regions. -/
theorem global_demand_valid_hashes_with_buckets27 {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b * m)) :
    ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2 * k r + 1))),
      ValidGlobalHashes g (b * m) xi (fun r => 2 * k r + 1) B ∧
      (∀ r,
        2 * globalDemand g b floor m xi r ≤ 2 * k r + 1 ∧
        2 * k r + 1 ≤ 2 * max (max floor (2 * w + 3))
          (2 * globalDemand g b floor m xi r) ∧
        (B r).card = rothNumberNat (k r)) ∧
      ∀ r, Nonempty (GlobalBucketLabel27 (B r)) := by
  obtain ⟨k, B, hvalid, hbounds⟩ := global_demand_valid_hashes g floor m xi
  refine ⟨k, B, hvalid, hbounds, ?_⟩
  intro r
  apply Finset.nonempty_coe_sort.mpr
  apply Finset.card_pos.mp
  rw [(hbounds r).2.2]
  apply rothNumberNat_posGrid27
  have hodd : 2 < 2 * k r + 1 := (hvalid r).2.1
  omega


-- The branch result retains the dependent regional target tensor.

end
end OmegaBound.ADVXXZGeneral
end
