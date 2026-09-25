import OmegaBound.ADVXXZGeneralAmend25Ordered

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem pairedChunk_eq_parent25 {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W)
    (t : Fin s) (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    StageCandidateRaw.pairedChunk
        (StageCandidateRaw.stageWord q b m p d r W a) t i =
      Parent25.paired a t i := by
  funext c
  by_cases hc : c.val < w
  · simp [StageCandidateRaw.pairedChunk, Parent25.paired,
      StageCandidateRaw.stageWord, hc]
  · simp [StageCandidateRaw.pairedChunk, Parent25.paired,
      StageCandidateRaw.stageWord, hc]

private theorem inputPartKeep_iff_parent25 {w s : ℕ} (q b m : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (a : (stagePopulationAt q p d b m r).Part W) :
    StageCandidateRaw.inputPartKeep q b m ε p d r W a ↔
      Parent25.inputPartKeep p d b m ε r W a := by
  simp only [StageCandidateRaw.inputPartKeep, Parent25.inputPartKeep,
    Parent25.parentCount, Parent25.alphaCount,
    StageCandidateRaw.stageParentCount, StageCandidateRaw.stageAlphaCount,
    pairedChunk_eq_parent25]
  cases W <;> rfl

private theorem coarseContains_iff_parent25 {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W) :
    stageCandidateCoarseContains q p d b m r W j a ↔
      Parent25.containsSide p d b m r W j a := by
  rfl

private theorem compatible_iff_parent25 {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part
      (d.perm r (if which = 0 then .Y else .Z))) :
    stageCandidateCompatible q p d b m r which j a ↔
      Parent25.compatible p d b m r which j a := by
  by_cases h : which = 0 <;>
    simp [stageCandidateCompatible, Parent25.compatible,
      stageCandidateCellCount, Parent25.cellCount, Parent25.boundary,
      Parent25.childCount, Parent25.side, h]

private theorem incidence_implies_coarseContains {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W)
    (hinc : (stagePopulationAt q p d b m r).incidence W j a) :
    stageCandidateCoarseContains q p d b m r W j a := by
  simpa only [stageCandidateCoarseContains] using hinc.1

set_option maxHeartbeats 1000000 in
-- The dependent stage-position/cardinality elaboration exceeds the default heartbeat budget.
private theorem incidence_exact_cell {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W)
    (hinc : (stagePopulationAt q p d b m r).incidence W j a)
    (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    stageCandidateCellCount q p d b m r W j a t (fun v => v = u.val) σ =
      ((m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ).floor.toNat := by
  have hcount := hinc.2 t u σ
  rw [stageCandidateCellCount]
  calc
    _ = (Finset.univ.filter fun ih :
          Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
          j.val ⟨t, ih⟩ = u ∧ a ⟨t, ih⟩ = σ).card := by
      symm
      refine Finset.card_bij
        (fun ih _ => (⟨t, ih⟩ : StageCandidateRaw.StagePos b m p d r)) ?_ ?_ ?_
      · intro ih hih
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hih ⊢
        exact ⟨congrArg Subtype.val hih.1, hih.2⟩
      · intro ih₁ _ ih₂ _ heq
        cases heq
        rfl
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rcases z with ⟨t₀, ih⟩
        dsimp only at hz
        rcases hz with ⟨ht, hju, ha⟩
        subst t₀
        refine ⟨ih, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Subtype.ext hju, ha⟩
    _ = _ := by simpa only [Nat.cast_mul] using hcount

set_option maxHeartbeats 1000000 in
-- The dependent parent-indexed double-sum elaboration exceeds the default heartbeat budget.
private theorem stageCandidateCellCount_grade {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W)
    (t : Fin s) (k : Fin (2*w+1)) (σ : Chunk w) :
    stageCandidateCellCount q p d b m r W j a t
        (fun u => coord W u = k.val) σ =
      ∑ u : ChildShape p t, if coord W u.val = k.val then
        stageCandidateCellCount q p d b m r W j a t (fun v => v = u.val) σ else 0 := by
  classical
  simp only [stageCandidateCellCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ z, ∑ u : ChildShape p t,
        if coord W u.val = k.val ∧ z.1 = t ∧
            (j.val z).val = u.val ∧ a z = σ then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro z _hz
      by_cases ht : z.1 = t
      · subst t
        by_cases hc : coord W (j.val z).val = k.val
        · by_cases ha : a z = σ
          · have hfilter :
                (Finset.univ.filter fun u : ChildShape p z.1 =>
                  coord W u.val = k.val ∧ (j.val z).val = u.val ∧ a z = σ) =
                    {j.val z} := by
              ext u
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton]
              constructor
              · intro hu
                exact Subtype.ext hu.2.1.symm
              · intro hu
                subst u
                exact ⟨hc, rfl, ha⟩
            simp only [eq_self, true_and]
            rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
              hfilter, Finset.card_singleton]
            rw [if_pos ⟨hc, ha⟩]
          · simp [ha]
        · have hfilter :
              (Finset.univ.filter fun u : ChildShape p z.1 =>
                coord W u.val = k.val ∧ (j.val z).val = u.val ∧ a z = σ) = ∅ := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false]
            intro hu
            apply hc
            rw [hu.2.1]
            exact hu.1
          simp only [eq_self, true_and]
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
            hfilter, Finset.card_empty]
          rw [if_neg (fun h => hc h.1)]
      · simp [ht]
    _ = ∑ u : ChildShape p t, ∑ z,
        if coord W u.val = k.val ∧ z.1 = t ∧
            (j.val z).val = u.val ∧ a z = σ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro u _hu
      by_cases hc : coord W u.val = k.val
      · rw [if_pos hc]
        refine Finset.sum_congr rfl ?_
        intro z _hz
        by_cases ht : z.1 = t <;>
          by_cases hj : (j.val z).val = u.val <;>
            by_cases ha : a z = σ <;> simp [hc, ht, hj, ha]
      · simp [hc]

private theorem incidence_implies_compatible {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part
      (d.perm r (if which = 0 then .Y else .Z)))
    (hinc : (stagePopulationAt q p d b m r).incidence
      (d.perm r (if which = 0 then .Y else .Z)) j a) :
    stageCandidateCompatible q p d b m r which j a := by
  have hside :
      (if which = 0 then d.perm r .Y else d.perm r .Z) =
        d.perm r (if which = 0 then .Y else .Z) := by
    by_cases hw : which = 0 <;> simp [hw]
  unfold stageCandidateCompatible
  dsimp only
  rw [hside]
  constructor
  · intro t u _hboundary σ
    exact incidence_exact_cell q b m p d r _ j a hinc t u σ
  · intro t k σ
    rw [stageCandidateCellCount_grade]
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases hc : coord (d.perm r (if which = 0 then .Y else .Z)) u.val = k.val
    · simp only [hc, if_pos]
      exact incidence_exact_cell q b m p d r _ j a hinc t u σ
    · simp only [hc]
      simp

theorem constituent_ordered_deletions {w s b : ℕ} (q m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (ε : ℚ) (r : Fin 6) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M) :
  ∀ W : Side, ∀ x : (regionalInputZ q p d (b*m) ε).leg W,
    candidateWord q p d b ε m r B ω W x ↔
      stageKeepAt25 q b m M ε p d r B ω .zUseful W x := by
  classical
  intro W x
  simp only [candidateWord, stageKeepAt25, stagePartKeepAt25]
  constructor
  · rintro ⟨hinput, j, pre, hjS, hprex, hyUnique, hzUnique⟩
    have hpart : pre.1.val = stagePartAt q b m ε p d r W x := by
      have hp := pre.2.property
      rw [hprex] at hp
      exact hp.symm
    have hinc : (stagePopulationAt q p d b m r).incidence W j
        (stagePartAt q b m ε p d r W x) := hpart ▸ pre.1.property
    have hcontains : Parent25.containsSide p d b m r W j
        (stagePartAt q b m ε p d r W x) :=
      (coarseContains_iff_parent25 q b m p d r W j _).mp
        (incidence_implies_coarseContains q b m p d r W j _ hinc)
    have hjMatching : j ∈
        (selected
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
          (fun k => Parent25.containsSide p d b m r W k
            (stagePartAt q b m ε p d r W x)) :=
      Finset.mem_filter.mpr ⟨hjS, hcontains⟩
    refine ⟨(inputPartKeep_iff_parent25 q b m ε p d r W _).mp hinput,
      ⟨j, hjMatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _hW
      exact ⟨j, hjMatching, hinc⟩
    · intro hW
      subst W
      refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩⟩
      exact (compatible_iff_parent25 q b m p d r 0 j _).mp
        (incidence_implies_compatible q b m p d r 0 j _ hinc)
    · intro hW
      subst W
      apply Finset.card_eq_one.mpr
      refine ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
      · refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
        exact (compatible_iff_parent25 q b m p d r 0 j _).mp
          (incidence_implies_compatible q b m p d r 0 j _ hinc)
      · intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkm := Finset.mem_filter.mp hk'.1
        exact hyUnique rfl k hkm.1
          ((coarseContains_iff_parent25 q b m p d r _ k _).mpr hkm.2)
          ((compatible_iff_parent25 q b m p d r 0 k _).mpr hk'.2)
    · intro hW
      subst W
      refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩, hinc⟩
      exact (compatible_iff_parent25 q b m p d r 0 j _).mp
        (incidence_implies_compatible q b m p d r 0 j _ hinc)
    · intro hW
      subst W
      refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩⟩
      exact (compatible_iff_parent25 q b m p d r 1 j _).mp
        (incidence_implies_compatible q b m p d r 1 j _ hinc)
    · intro hW
      subst W
      apply Finset.card_eq_one.mpr
      refine ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
      · refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
        exact (compatible_iff_parent25 q b m p d r 1 j _).mp
          (incidence_implies_compatible q b m p d r 1 j _ hinc)
      · intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkm := Finset.mem_filter.mp hk'.1
        exact hzUnique rfl k hkm.1
          ((coarseContains_iff_parent25 q b m p d r _ k _).mpr hkm.2)
          ((compatible_iff_parent25 q b m p d r 1 k _).mpr hk'.2)
    · intro hW
      subst W
      refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩, hinc⟩
      exact (compatible_iff_parent25 q b m p d r 1 j _).mp
        (incidence_implies_compatible q b m p d r 1 j _ hinc)
  · rintro ⟨hinput, _hhash, hX, _hYC, hYU, hYF, _hZC, hZU, hZF⟩
    have hchosen : ∃ j ∈
        (selected
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
          (fun k => Parent25.containsSide p d b m r W k
            (stagePartAt q b m ε p d r W x)),
        (stagePopulationAt q p d b m r).incidence W j
          (stagePartAt q b m ε p d r W x) := by
      rcases (hd.roles.1 r).2 W with ⟨V, hV⟩
      cases V with
      | X => exact hX hV.symm
      | Y =>
          rcases hYF hV.symm with ⟨j, hj, hinc⟩
          exact ⟨j, (Finset.mem_filter.mp hj).1, hinc⟩
      | Z =>
          rcases hZF hV.symm with ⟨j, hj, hinc⟩
          exact ⟨j, (Finset.mem_filter.mp hj).1, hinc⟩
    rcases hchosen with ⟨j, hjMatching, hinc⟩
    have hjS := (Finset.mem_filter.mp hjMatching).1
    let pre : StageExactPreimageAt q p d b ε m r j W :=
      ⟨⟨stagePartAt q b m ε p d r W x, hinc⟩, ⟨x, rfl⟩⟩
    refine ⟨(inputPartKeep_iff_parent25 q b m ε p d r W _).mpr hinput,
      j, pre, hjS, rfl, ?_, ?_⟩
    · intro hW
      subst W
      intro k hkS hkContains hkCompatible
      have hkC : k ∈
          ((selected
            (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
            (fun l => Parent25.containsSide p d b m r (d.perm r .Y) l
              (stagePartAt q b m ε p d r (d.perm r .Y) x))).filter
            (fun l => Parent25.compatible p d b m r 0 l
              (stagePartAt q b m ε p d r (d.perm r .Y) x)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hkS,
          (coarseContains_iff_parent25 q b m p d r (d.perm r .Y) k _).mp hkContains⟩,
          (compatible_iff_parent25 q b m p d r 0 k _).mp hkCompatible⟩
      have hjC : j ∈
          ((selected
            (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
            (fun l => Parent25.containsSide p d b m r (d.perm r .Y) l
              (stagePartAt q b m ε p d r (d.perm r .Y) x))).filter
            (fun l => Parent25.compatible p d b m r 0 l
              (stagePartAt q b m ε p d r (d.perm r .Y) x)) := by
        refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
        exact (compatible_iff_parent25 q b m p d r 0 j _).mp
          (incidence_implies_compatible q b m p d r 0 j _ hinc)
      rcases Finset.card_eq_one.mp (hYU rfl) with ⟨z, hz⟩
      rw [hz] at hkC hjC
      simp only [Finset.mem_singleton] at hkC hjC
      exact hkC.trans hjC.symm
    · intro hW
      subst W
      intro k hkS hkContains hkCompatible
      have hkC : k ∈
          ((selected
            (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
            (fun l => Parent25.containsSide p d b m r (d.perm r .Z) l
              (stagePartAt q b m ε p d r (d.perm r .Z) x))).filter
            (fun l => Parent25.compatible p d b m r 1 l
              (stagePartAt q b m ε p d r (d.perm r .Z) x)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hkS,
          (coarseContains_iff_parent25 q b m p d r (d.perm r .Z) k _).mp hkContains⟩,
          (compatible_iff_parent25 q b m p d r 1 k _).mp hkCompatible⟩
      have hjC : j ∈
          ((selected
            (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω).filter
            (fun l => Parent25.containsSide p d b m r (d.perm r .Z) l
              (stagePartAt q b m ε p d r (d.perm r .Z) x))).filter
            (fun l => Parent25.compatible p d b m r 1 l
              (stagePartAt q b m ε p d r (d.perm r .Z) x)) := by
        refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
        exact (compatible_iff_parent25 q b m p d r 1 j _).mp
          (incidence_implies_compatible q b m p d r 1 j _ hinc)
      rcases Finset.card_eq_one.mp (hZU rfl) with ⟨z, hz⟩
      rw [hz] at hkC hjC
      simp only [Finset.mem_singleton] at hkC hjC
      exact hkC.trans hjC.symm

end OmegaBound.ADVXXZGeneral
end
