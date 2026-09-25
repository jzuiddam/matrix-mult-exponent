import OmegaBound.ADVXXZGeneralCExact37Orbit
import OmegaBound.ADVXXZHashRung
import OmegaBound.CW90Hash

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem stageDemand_floor_le37 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (floor : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) :
    max floor (2 * (w + w) + 3) ≤ stageDemand25 p d b floor ε m r := by
  unfold stageDemand25 natural_demand
  dsimp only
  exact le_max_left _ _

/-- Per-region prime/AP-free instantiation at the actual paired-parent demand. -/
theorem stage_demand_bound_instance37 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (floor : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) :
    ∃ (k : ℕ) (B : Finset (ZMod (2*k+1))),
      Nat.Prime (2*k+1) ∧ 2 < 2*k+1 ∧
      (stagePopulationAt 0 p d b m r).grade < 2*k+1 ∧ HashAPFree B ∧
      2 * stageDemand25 p d b floor ε m r ≤ 2*k+1 ∧
      2*k+1 ≤ 2 * max (max floor (2 * (w+w) + 3))
        (2 * stageDemand25 p d b floor ε m r) ∧
      B.card = rothNumberNat k := by
  let L := max floor (2 * (w+w) + 3)
  let D := stageDemand25 p d b floor ε m r
  have hL : 2 ≤ L := by dsimp only [L]; omega
  obtain ⟨k, hp, hLM, hDM, hupper⟩ :=
    OmegaBound.ADVXXZHash.exists_prime_modulus L D hL
  obtain ⟨B, hcard, hap⟩ := CW90.exists_apFree_zmod k
  refine ⟨k, B, hp, by omega, ?_, ?_, hDM, hupper, hcard⟩
  · change 2*w < 2*k+1
    have hbase : 2*w < L := by dsimp only [L]; omega
    omega
  · intro a ha b' hb' c hc heq
    obtain ⟨hac, hcb⟩ := hap a (by simpa using ha) c (by simpa using hc)
      b' (by simpa using hb') heq
    exact ⟨hac.trans hcb, hcb⟩

/-- Six simultaneous demand-sized moduli and literal Salem--Spencer bucket sets. -/
theorem stage_demand_valid_hashes37 {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (floor : ℕ) (ε : ℚ) (m : ℕ) :
    ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2*k r+1))),
      ValidStageHashes p d b m (fun r => 2*k r+1) B ∧
      (∀ r, 2 * stageDemand25 p d b floor ε m r ≤ 2*k r+1 ∧
        2*k r+1 ≤ 2 * max (max floor (2 * (w+w) + 3))
          (2 * stageDemand25 p d b floor ε m r) ∧
        (B r).card = rothNumberNat (k r)) := by
  let Good := fun (r : Fin 6) (k : ℕ) (B : Finset (ZMod (2*k+1))) =>
    Nat.Prime (2*k+1) ∧ 2 < 2*k+1 ∧
      (stagePopulationAt 0 p d b m r).grade < 2*k+1 ∧ HashAPFree B ∧
      2 * stageDemand25 p d b floor ε m r ≤ 2*k+1 ∧
      2*k+1 ≤ 2 * max (max floor (2 * (w+w) + 3))
        (2 * stageDemand25 p d b floor ε m r) ∧
      B.card = rothNumberNat k
  have hex : ∀ r, ∃ k, ∃ B, Good r k B := fun r =>
    stage_demand_bound_instance37 p d floor ε m r
  let k : Fin 6 → ℕ := fun r => Classical.choose (hex r)
  have hexB : ∀ r, ∃ B, Good r (k r) B := fun r => Classical.choose_spec (hex r)
  let B : (r : Fin 6) → Finset (ZMod (2*k r+1)) := fun r => Classical.choose (hexB r)
  have hB : ∀ r, Good r (k r) (B r) := fun r => Classical.choose_spec (hexB r)
  refine ⟨k, B, ?_, ?_⟩
  · intro r
    exact ⟨(hB r).1, (hB r).2.1, (hB r).2.2.1, (hB r).2.2.2.1⟩
  · intro r
    exact ⟨(hB r).2.2.2.2.1, (hB r).2.2.2.2.2.1,
      (hB r).2.2.2.2.2.2⟩

theorem stage_roth_bucket_nonempty37 {k : ℕ} (B : Finset (ZMod (2*k+1)))
    (hcard : B.card = rothNumberNat k) (hodd : 2 < 2*k+1) : B.Nonempty := by
  apply Finset.card_pos.mp
  rw [hcard]
  have hb := CW90.card_apFree_zmod_lower k
  have hk : 1 ≤ k := by omega
  have hpos : (0 : ℝ) < (k : ℝ) * Real.exp (-4 * Real.sqrt (Real.log k)) := by
    have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hreal : (0 : ℝ) < (rothNumberNat k : ℝ) := lt_of_lt_of_le hpos hb
  exact_mod_cast hreal

end
end OmegaBound.ADVXXZGeneral
