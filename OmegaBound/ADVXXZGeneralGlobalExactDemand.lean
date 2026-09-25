import OmegaBound.ADVXXZGeneralAmend25Rates
import OmegaBound.ADVXXZHashRung
import OmegaBound.CW90Hash

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

/-- The literal floor used in the global natural demand is always covered by that demand. -/
theorem globalDemand_floor_le {w b : ℕ} (g : GlobalSpec w) (floor m : ℕ)
    (xi : ExactGrid g (b*m)) (r : Fin 6) :
    max floor (2*w+3) ≤ globalDemand g b floor m xi r := by
  unfold globalDemand natural_demand
  dsimp only
  exact le_max_left _ _

/--
The per-region prime/AP-free instantiation at the *actual* global natural demand.

This is the finite modulus choice used before the analytic estimate on `globalDemand`: the
modulus is odd prime, clears the grade floor, dominates twice the demand, is within Bertrand's
factor two, and carries the literal Salem--Spencer set.
-/
theorem global_demand_bound_instance {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b*m)) (r : Fin 6) :
    ∃ (k : ℕ) (B : Finset (ZMod (2*k+1))),
      Nat.Prime (2*k+1) ∧
      max floor (2*w+3) < 2*k+1 ∧
      2 * globalDemand g b floor m xi r ≤ 2*k+1 ∧
      2*k+1 ≤ 2 * max (max floor (2*w+3))
        (2 * globalDemand g b floor m xi r) ∧
      B.card = rothNumberNat k ∧ HashAPFree B := by
  let L := max floor (2*w+3)
  let D := globalDemand g b floor m xi r
  have hL : 2 ≤ L := by
    dsimp only [L]
    omega
  obtain ⟨k, hp, hLM, hDM, hupper⟩ :=
    OmegaBound.ADVXXZHash.exists_prime_modulus L D hL
  obtain ⟨B, hcard, hap⟩ := CW90.exists_apFree_zmod k
  refine ⟨k, B, hp, hLM, hDM, hupper, hcard, ?_⟩
  intro a ha b' hb' c hc heq
  obtain ⟨hac, hcb⟩ := hap a (by simpa using ha) c (by simpa using hc)
    b' (by simpa using hb') heq
  exact ⟨hac.trans hcb, hcb⟩

/-- The preceding choice supplies exactly the local fields of `ValidGlobalHashes`. -/
theorem global_demand_bound_instance_valid {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b*m)) (r : Fin 6) :
    ∃ (k : ℕ) (B : Finset (ZMod (2*k+1))),
      Nat.Prime (2*k+1) ∧ 2 < 2*k+1 ∧
      (globalPopulation g (b*m) xi r).grade < 2*k+1 ∧
      HashAPFree B ∧
      2 * globalDemand g b floor m xi r ≤ 2*k+1 ∧
      2*k+1 ≤ 2 * max (max floor (2*w+3))
        (2 * globalDemand g b floor m xi r) ∧
      B.card = rothNumberNat k := by
  obtain ⟨k, B, hp, hfloor, hdemand, hupper, hcard, hfree⟩ :=
    global_demand_bound_instance g floor m xi r
  refine ⟨k, B, hp, ?_, ?_, hfree, hdemand, hupper, hcard⟩
  · omega
  · change 2*w < 2*k+1
    omega

/-- Simultaneous per-region choices give the exact `ValidGlobalHashes` package. -/
theorem global_demand_valid_hashes {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b*m)) :
    ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2*k r+1))),
      ValidGlobalHashes g (b*m) xi (fun r => 2*k r+1) B ∧
      ∀ r,
        2 * globalDemand g b floor m xi r ≤ 2*k r+1 ∧
        2*k r+1 ≤ 2 * max (max floor (2*w+3))
          (2 * globalDemand g b floor m xi r) ∧
        (B r).card = rothNumberNat (k r) := by
  let Good := fun (r : Fin 6) (k : ℕ) (B : Finset (ZMod (2*k+1))) =>
    Nat.Prime (2*k+1) ∧ 2 < 2*k+1 ∧
      (globalPopulation g (b*m) xi r).grade < 2*k+1 ∧
      HashAPFree B ∧
      2 * globalDemand g b floor m xi r ≤ 2*k+1 ∧
      2*k+1 ≤ 2 * max (max floor (2*w+3))
        (2 * globalDemand g b floor m xi r) ∧
      B.card = rothNumberNat k
  have hex : ∀ r, ∃ k, ∃ B, Good r k B := fun r =>
    global_demand_bound_instance_valid g floor m xi r
  let k : Fin 6 → ℕ := fun r => Classical.choose (hex r)
  have hexB : ∀ r, ∃ B, Good r (k r) B := fun r =>
    Classical.choose_spec (hex r)
  let B : (r : Fin 6) → Finset (ZMod (2*k r+1)) := fun r =>
    Classical.choose (hexB r)
  have hB : ∀ r, Good r (k r) (B r) := fun r => Classical.choose_spec (hexB r)
  refine ⟨k, B, ?_, ?_⟩
  · intro r
    exact ⟨(hB r).1, (hB r).2.1, (hB r).2.2.1, (hB r).2.2.2.1⟩
  · intro r
    exact ⟨(hB r).2.2.2.2.1, (hB r).2.2.2.2.2.1, (hB r).2.2.2.2.2.2⟩

end
end OmegaBound.ADVXXZGeneral
end
