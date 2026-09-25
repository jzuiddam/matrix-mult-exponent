import OmegaBound.ADVXXZGeneralAmend25Population
import OmegaBound.ADVXXZGeneralAmend25Stage
import OmegaBound.ADVXXZGeneralRepair
import OmegaBound.ADVXXZGeneralStageDefinitionsV22
import OmegaBound.ADVXXZGeneralTensor
import OmegaBound.ADVXXZGeneralTensorCopiesZ
import OmegaBound.ADVXXZGeneralCoarseTransportParent25

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable section

private theorem selected_mem_stage_target {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω) :
    j ∈ (stagePopulationAt q p d b m r).target := by
  classical
  simp only [selected, Finset.mem_filter] at hj
  exact hj.2.1

set_option maxHeartbeats 1000000 in
-- The dependent stage-population type itself exceeds the default elaboration budget.
/-- Exact part alphabets have the same cardinality for any two selected labels in one region. -/
theorem selected_exactPartsAt_card_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (W : Side) :
    (exactPartsAt q b m p d r j W).card =
      (exactPartsAt q b m p d r k W).card := by
  classical
  have hjt := selected_mem_stage_target q b m M p d r B ω j hj
  have hkt := selected_mem_stage_target q b m M p d r B ω k hk
  let J : AlphaLabel p d b m r := ⟨j, hjt⟩
  let K : AlphaLabel p d b m r := ⟨k, hkt⟩
  obtain ⟨e, _he⟩ := coarse_transport_parent25 q m p d hd hb r J K W
  have hcard : Fintype.card (RepresentedParts p d b m J W) =
      Fintype.card (RepresentedParts p d b m K W) := Fintype.card_congr e
  change Fintype.card {a // a ∈ exactPartsAt q b m p d r j W} =
      Fintype.card {a // a ∈ exactPartsAt q b m p d r k W} at hcard
  simpa only [Fintype.card_coe] using hcard

set_option maxHeartbeats 1000000 in
-- As above, elaborating both dependent stage labels needs the larger local allowance.
/-- On a nonempty good family, the stored maximum is the exact part cardinality of every member. -/
theorem selected_exactPartsAt_sup_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (ε : ℚ)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b ε m r M B ω j)
    (j : (stagePopulationAt q p d b m r).Label) (hj : j ∈ J) (W : Side) :
    J.sup (fun k => (exactPartsAt q b m p d r k W).card) =
      (exactPartsAt q b m p d r j W).card := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    exact (selected_exactPartsAt_card_eq q m p d hd hb r M B ω k j
      (hJ k hk).1 (hJ j hj).1 W).le
  · exact Finset.le_sup (f := fun k => (exactPartsAt q b m p d r k W).card) hj

/-- Every occupied stage region has repair parameter at least two. -/
theorem stagePopulationAt_n_ge_two {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    2 ≤ (stagePopulationAt q p d b m r).n := by
  classical
  dsimp only [stagePopulationAt] at hn ⊢
  letI : Fintype
      ((t : Fin s) ×
        (Fin (∑ u, (((b * m * p.baseN t : ℕ) : ℚ) *
          (d.A t).prob r * (d.alpha t r).prob u).floor.toNat) × Fin 2)) :=
    Fintype.ofFinite _
  have hpos : 0 < Fintype.card
      ((t : Fin s) ×
        (Fin (∑ u, (((b * m * p.baseN t : ℕ) : ℚ) *
          (d.A t).prob r * (d.alpha t r).prob u).floor.toNat) × Fin 2)) :=
    Nat.pos_of_ne_zero hn
  obtain ⟨a⟩ := (Fintype.card_pos_iff.mp hpos : Nonempty
      ((t : Fin s) ×
        (Fin (∑ u, (((b * m * p.baseN t : ℕ) : ℚ) *
          (d.A t).prob r * (d.alpha t r).prob u).floor.toNat) × Fin 2)))
  let f : Fin 2 →
      ((t : Fin s) ×
        (Fin (∑ u, (((b * m * p.baseN t : ℕ) : ℚ) *
          (d.A t).prob r * (d.alpha t r).prob u).floor.toNat) × Fin 2)) :=
    fun h => ⟨a.1, (a.2.1, h)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg (fun z => z.2.2) hxy
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

set_option maxHeartbeats 1000000 in
-- This repeats the dependent stage-family envelope of the maximum transport above.
/-- The good-label hole budget can be stated against the common stored maximum. -/
theorem selected_holesAt25_capacity_sup {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) (ε : ℚ)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b ε m r M B ω j)
    (j : (stagePopulationAt q p d b m r).Label) (hj : j ∈ J) (W : Side) :
    4 * (stagePopulationAt q p d b m r).n *
        (holesAt25 q b m M ε p d r B ω j W).card ≤
      J.sup (fun k => (exactPartsAt q b m p d r k W).card) := by
  rw [selected_exactPartsAt_sup_eq q m p d hd hb ε r M B ω J hJ j hj W]
  exact (hJ j hj).2 W

set_option maxHeartbeats 1000000 in
-- This repeats the dependent stage-family envelope of the maximum transport above.
/-- The reserve appearing in `stageRepairedCount` is the reserve of any selected label. -/
theorem selected_repairReserve_sup_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) (ε : ℚ)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b ε m r M B ω j)
    (j : (stagePopulationAt q p d b m r).Label) (hj : j ∈ J) :
    repairReserve (stagePopulationAt q p d b m r).n
        (fun W => J.sup (fun k => (exactPartsAt q b m p d r k W).card)) =
      repairReserve (stagePopulationAt q p d b m r).n
        (fun W => (exactPartsAt q b m p d r j W).card) := by
  congr 1
  funext W
  exact selected_exactPartsAt_sup_eq q m p d hd hb ε r M B ω J hJ j hj W

/-- Independent regional copy labels assemble into the product number of full tensor copies. -/
theorem copiesZ_regionProductZ_restricts (copies : Fin 6 → ℕ) (T : Fin 6 → ITensor) :
    Restricts (copiesZ (∏ r, copies r) (regionProductZ T)).tensor
      (regionProductZ (fun r => copiesZ (copies r) (T r))).tensor := by
  classical
  let e : Fin (∏ r, copies r) ≃ ((r : Fin 6) → Fin (copies r)) :=
    Fintype.equivOfCardEq (by simp)
  refine ADVXXZ.restricts_of_sub
    (fun p r => (e p.1 r, p.2 r))
    (fun p r => (e p.1 r, p.2 r))
    (fun p r => (e p.1 r, p.2 r)) ?_
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
  simp only [copiesZ, regionProductZ, famDS]
  by_cases h : a = b ∧ b = c
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg (by simpa using h)]
    symm
    have hex : ∃ r, ¬ (e a r = e b r ∧ e b r = e c r) := by
      by_contra hn
      push_neg at hn
      apply h
      exact ⟨e.injective (funext fun r => (hn r).1),
        e.injective (funext fun r => (hn r).2)⟩
    obtain ⟨r, hr⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    rw [if_neg]
    rintro ⟨hab, hbc, -⟩
    exact hr ⟨hab, hbc⟩

end
end OmegaBound.ADVXXZGeneral
end
