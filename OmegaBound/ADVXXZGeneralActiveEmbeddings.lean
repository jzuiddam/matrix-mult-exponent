import OmegaBound.ADVXXZGeneralOrderedDeletions

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable section

private theorem selected_unique_coarseX (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (j k : P.Label)
    (hj : j ∈ selected P M B ω) (hk : k ∈ selected P M B ω)
    (hcoarse : P.coarse k .X = P.coarse j .X) : k = j := by
  classical
  simp only [selected, Finset.mem_filter] at hj hk
  exact hj.2.2 k hk.1 hcoarse

private theorem scaledIntegralCount_eq (b base m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * (base : ℚ) * a = (k : ℚ)) :
    (((b * m : ℕ) : ℚ) * (base : ℚ) * a).floor.toNat = k * m := by
  have hq : (((b * m : ℕ) : ℚ) * (base : ℚ) * a) = ((k * m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k * m : ℕ) : ℚ).floor) = (k * m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k * m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k * m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

private theorem stageParentCount_eq_regionalCount {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (hb : StepIntegralAt p d b) (t : Fin s) (r : Fin 6) :
    StageCandidateRaw.stageParentCount b m p d r t =
      (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat := by
  classical
  let kA : ℕ := Classical.choose ((hb.2 t r).1)
  let kα : ChildShape p t → ℕ := fun u => Classical.choose (((hb.2 t r).2 u).1)
  have hkA : (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r = (kA : ℚ) :=
    Classical.choose_spec ((hb.2 t r).1)
  have hkα : ∀ u, (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u = (kα u : ℚ) :=
    fun u => Classical.choose_spec (((hb.2 t r).2 u).1)
  have hk_sum : ∑ u, kα u = kA := by
    exact_mod_cast (show ∑ u, (kα u : ℚ) = (kA : ℚ) by
      rw [← hkA]
      calc
        ∑ u, (kα u : ℚ) = ∑ u, (b : ℚ) * (p.baseN t : ℚ) *
            (d.A t).prob r * (d.alpha t r).prob u := by
          exact Finset.sum_congr rfl fun u _ => (hkα u).symm
        _ = (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r *
            ∑ u, (d.alpha t r).prob u := by rw [Finset.mul_sum]
        _ = (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r := by
          rw [(d.alpha t r).sum_prob, mul_one])
  rw [StageCandidateRaw.stageParentCount]
  calc
    ∑ u, StageCandidateRaw.stageAlphaCount b m p d r t u =
        ∑ u, kα u * m := by
      refine Finset.sum_congr rfl fun u _ => ?_
      unfold StageCandidateRaw.stageAlphaCount
      simpa only [Nat.cast_mul, mul_assoc] using
        (scaledIntegralCount_eq b (p.baseN t) m (kα u)
          ((d.A t).prob r * (d.alpha t r).prob u) (by
            simpa only [mul_assoc] using hkα u))
    _ = (∑ u, kα u) * m := by rw [Finset.sum_mul]
    _ = kA * m := by rw [hk_sum]
    _ = (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat := by
      symm
      exact scaledIntegralCount_eq b (p.baseN t) m kA ((d.A t).prob r) hkA

private def joinedCoord {w : ℕ} (h : Fin 2) (c : Fin w) : Fin (w + w) :=
  ⟨h.val * w + c.val, by
    have hh : h.val = 0 ∨ h.val = 1 := by omega
    rcases hh with hh | hh <;> simp [hh] <;> omega⟩

private noncomputable def regionalLegValue {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (W : Side)
    (x : (regionalInputZ q p d (b*m) ε).leg W)
    (slot : Fin (Fintype.card (Fin s × Fin 6)))
    (i : Fin ((((b*m : ℕ) : ℚ) *
      (p.baseN ((Fintype.equivFin (Fin s × Fin 6)).symm slot).1 : ℚ) *
      (d.A ((Fintype.equivFin (Fin s × Fin 6)).symm slot).1).prob
        ((Fintype.equivFin (Fin s × Fin 6)).symm slot).2).floor.toNat))
    (c : Fin (w+w)) : CW90.Idx7 q := by
  cases W <;>
    exact x slot i c

private noncomputable def packPhysicalWords {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : StepIntegralAt p d b)
    (ε : ℚ) (W : Side) (x : (r : Fin 6) → StagePhysicalWord q p d b m r) :
    (regionalInputZ q p d (b*m) ε).leg W := by
  classical
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  let value := fun (slot : Fin (Fintype.card (Fin s × Fin 6)))
      (i : Fin ((((b*m : ℕ) : ℚ) * (p.baseN (e slot).1 : ℚ) *
        (d.A (e slot).1).prob (e slot).2).floor.toNat))
      (c : Fin (w+w)) =>
    let tr := e slot
    let hi := stageParentCount_eq_regionalCount p d b m hb tr.1 tr.2
    let i' : Fin (StageCandidateRaw.stageParentCount b m p d tr.2 tr.1) :=
      Fin.cast hi.symm i
    if hc : c.val < w then
      x tr.2 ⟨tr.1, (i', ⟨0, by omega⟩)⟩ ⟨c.val, hc⟩
    else
      x tr.2 ⟨tr.1, (i', ⟨1, by omega⟩)⟩ ⟨c.val - w, by omega⟩
  cases W <;>
    simpa only [regionalInputZ, ITensor.leg, supportedIfaceZ, ifaceZ] using value

private theorem physical_apply_of_pair_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (x : (r : Fin 6) → StagePhysicalWord q p d b m r)
    {tr tr' : Fin s × Fin 6} (htr : tr' = tr)
    (i' : Fin (StageCandidateRaw.stageParentCount b m p d tr'.2 tr'.1))
    (i : Fin (StageCandidateRaw.stageParentCount b m p d tr.2 tr.1))
    (hi : i'.val = i.val) (h : Fin 2) (c : Fin w) :
    x tr'.2 ⟨tr'.1, (i', h)⟩ c = x tr.2 ⟨tr.1, (i, h)⟩ c := by
  subst tr'
  have hii : i' = i := Fin.ext hi
  subst i'
  rfl

set_option maxHeartbeats 1000000 in
private theorem packPhysicalWords_apply {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : StepIntegralAt p d b)
    (ε : ℚ) (W : Side) (x : (r : Fin 6) → StagePhysicalWord q p d b m r)
    (r : Fin 6) (pos : StageCandidateRaw.StagePos b m p d r) (c : Fin w) :
    regionalLegValue q m p d ε W (packPhysicalWords q m p d hb ε W x)
        (Fintype.equivFin (Fin s × Fin 6) (pos.1, r))
        (Fin.cast (by
          simpa only [Equiv.symm_apply_apply] using
            (stageParentCount_eq_regionalCount p d b m hb pos.1 r)) pos.2.1)
        (joinedCoord pos.2.2 c) = x r pos c := by
  classical
  cases W <;> rcases pos with ⟨t, i, h⟩ <;> rcases i with ⟨i, hi⟩
  all_goals
    have hh : h = 0 ∨ h = 1 := by fin_cases h <;> simp
    rcases hh with rfl | rfl <;>
      simp [regionalLegValue, packPhysicalWords, joinedCoord,
        Equiv.symm_apply_apply]
  all_goals
    apply physical_apply_of_pair_eq q m p d x
      (Equiv.symm_apply_apply (Fintype.equivFin (Fin s × Fin 6)) (t, r))
    rfl

private theorem packPhysicalWords_injective {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : StepIntegralAt p d b)
    (ε : ℚ) (W : Side) :
    Function.Injective (packPhysicalWords q m p d hb ε W) := by
  intro x y hxy
  funext r pos c
  have h := congrArg
    (fun z => regionalLegValue q m p d ε W z
      (Fintype.equivFin (Fin s × Fin 6) (pos.1, r))
      (Fin.cast (by
        simpa only [Equiv.symm_apply_apply] using
          (stageParentCount_eq_regionalCount p d b m hb pos.1 r)) pos.2.1)
      (joinedCoord pos.2.2 c)) hxy
  simpa only [packPhysicalWords_apply] using h

private noncomputable def stageSelected {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (r : Fin 6) : Finset (stagePopulationAt q p d b m r).Label :=
  selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
    (M r) (B r) (ω r)

private noncomputable def stageRegionFamily {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (r : Fin 6) : ITensor := by
  classical
  exact if (stagePopulationAt q p d b m r).n = 0 then unitFamilyZ else
    dependentSumZ fun j : {j // j ∈ stageSelected q p d b m M B ω r} =>
      stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val

private def productLegValue (T : Fin 6 → ITensor) (W : Side)
    (x : (regionProductZ T).leg W) (r : Fin 6) : (T r).leg W := by
  cases W <;> exact x r

private noncomputable def emptyStageWord {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6)
    (_hn : (stagePopulationAt q p d b m r).n = 0) :
    StagePhysicalWord q p d b m r :=
  fun _ _ => Sum.inl none

private noncomputable def sourcePairAt {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    (j : {j // j ∈ stageSelected q p d b m M B ω r}) ×
      (stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val).leg W := by
  classical
  cases W with
  | X => simpa [regionProductZ, ITensor.leg, stageRegionFamily, hn] using x r
  | Y => simpa [regionProductZ, ITensor.leg, stageRegionFamily, hn] using x r
  | Z => simpa [regionProductZ, ITensor.leg, stageRegionFamily, hn] using x r

private noncomputable def sourceWordAt {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) : StagePhysicalWord q p d b m r := by
  classical
  by_cases hn : (stagePopulationAt q p d b m r).n = 0
  · exact emptyStageWord q p d b m r hn
  · cases W <;> exact (sourcePairAt q p d b ε m M B ω _ x r hn).2.val

private noncomputable def sourceLabelAt {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    {j // j ∈ stageSelected q p d b m M B ω r} := by
  classical
  exact (sourcePairAt q p d b ε m M B ω W x r hn).1

set_option maxHeartbeats 1000000 in
private theorem source_properties {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    let j := sourceLabelAt q p d b ε m M B ω W x r hn
    j.val ∈ stageSelected q p d b m M B ω r ∧
      (stagePopulationAt q p d b m r).incidence W j.val
        (stagePhysicalPart q p d b m r W
          (sourceWordAt q p d b ε m M B ω W x r)) ∧
      stagePhysicalPart q p d b m r W
          (sourceWordAt q p d b ε m M B ω W x r) ∉
        holesAt25 q b m (M r) ε p d r (B r) (ω r) j.val W := by
  classical
  cases W <;>
    simpa [sourceLabelAt, sourceWordAt, hn] using
      (sourcePairAt q p d b ε m M B ω _ x r hn).2.property

private theorem incidence_coarse {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W)
    (hinc : (stagePopulationAt q p d b m r).incidence W j a) :
    stageCandidateCoarseContains q p d b m r W j a := by
  simpa only [stageCandidateCoarseContains] using hinc.1

set_option maxHeartbeats 1000000 in
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
private theorem cellCount_grade {w s : ℕ} (q b m : ℕ)
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

private theorem incidence_compatible {w s : ℕ} (q b m : ℕ)
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
    rw [cellCount_grade]
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases hc : coord (d.perm r (if which = 0 then .Y else .Z)) u.val = k.val
    · simp only [hc, if_pos]
      exact incidence_exact_cell q b m p d r _ j a hinc t u σ
    · simp only [hc]
      simp

private theorem source_part_keep {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    stagePartKeepAt25 q b m (M r) ε p d r (B r) (ω r) .zUseful W
      (stagePhysicalPart q p d b m r W
        (sourceWordAt q p d b ε m M B ω W x r)) := by
  classical
  have hp := source_properties q p d b ε m M B ω W x r hn
  by_contra hkeep
  apply hp.2.2
  simp only [holesAt25, Finset.mem_filter]
  exact ⟨by simpa [exactPartsAt] using hp.2.1, hkeep⟩

private theorem labels_eq_roleX {w s : ℕ} (q b m M : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .X))
    (hincj : (stagePopulationAt q p d b m r).incidence (d.perm r .X) j a)
    (hinck : (stagePopulationAt q p d b m r).incidence (d.perm r .X) k a) :
    k = j := by
  apply selected_unique_coarseX
    (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω j k hj hk
  funext i
  apply Fin.ext
  simp only [rolePopulation]
  dsimp only [stagePopulationAt]
  generalize d.perm r .X = V at *
  cases V <;> simpa only [coord] using (hinck.1 _).symm.trans (hincj.1 _)

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

private theorem labels_eq_roleY {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .Y))
    (hincj : (stagePopulationAt q p d b m r).incidence (d.perm r .Y) j a)
    (hinck : (stagePopulationAt q p d b m r).incidence (d.perm r .Y) k a)
    (hkeep : stagePartKeepAt25 q b m M ε p d r B ω .zUseful
      (d.perm r .Y) a) : k = j := by
  classical
  unfold stagePartKeepAt25 at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_hinput, _hhash, _hX, _hYC, hYU, _hYF, _hZC, _hZU, _hZF⟩
  let S := selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω
  let matching := S.filter fun l => Parent25.containsSide p d b m r (d.perm r .Y) l a
  let C := matching.filter fun l => Parent25.compatible p d b m r 0 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hYU rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hj, incidence_coarse q b m p d r _ j a hincj⟩, ?_⟩
    exact (compatible_iff_parent25 q b m p d r 0 j a).mp
      (incidence_compatible q b m p d r 0 j a hincj)
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hk, incidence_coarse q b m p d r _ k a hinck⟩, ?_⟩
    exact (compatible_iff_parent25 q b m p d r 0 k a).mp
      (incidence_compatible q b m p d r 0 k a hinck)
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

private theorem labels_eq_roleZ {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .Z))
    (hincj : (stagePopulationAt q p d b m r).incidence (d.perm r .Z) j a)
    (hinck : (stagePopulationAt q p d b m r).incidence (d.perm r .Z) k a)
    (hkeep : stagePartKeepAt25 q b m M ε p d r B ω .zUseful
      (d.perm r .Z) a) : k = j := by
  classical
  unfold stagePartKeepAt25 at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_hinput, _hhash, _hX, _hYC, _hYU, _hYF, _hZC, hZU, _hZF⟩
  let S := selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω
  let matching := S.filter fun l => Parent25.containsSide p d b m r (d.perm r .Z) l a
  let C := matching.filter fun l => Parent25.compatible p d b m r 1 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hZU rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hj, incidence_coarse q b m p d r _ j a hincj⟩, ?_⟩
    exact (compatible_iff_parent25 q b m p d r 1 j a).mp
      (incidence_compatible q b m p d r 1 j a hincj)
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hk, incidence_coarse q b m p d r _ k a hinck⟩, ?_⟩
    exact (compatible_iff_parent25 q b m p d r 1 k a).mp
      (incidence_compatible q b m p d r 1 k a hinck)
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabel_eq_of_word_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hword : sourceWordAt q p d b ε m M B ω W x r =
      sourceWordAt q p d b ε m M B ω W y r) :
    sourceLabelAt q p d b ε m M B ω W x r hn =
      sourceLabelAt q p d b ε m M B ω W y r hn := by
  rcases (hd.roles.1 r).2 W with ⟨R, rfl⟩
  cases R with
  | X =>
      let j := sourceLabelAt q p d b ε m M B ω (d.perm r .X) x r hn
      let k := sourceLabelAt q p d b ε m M B ω (d.perm r .X) y r hn
      have hj := source_properties q p d b ε m M B ω (d.perm r .X) x r hn
      have hk := source_properties q p d b ε m M B ω (d.perm r .X) y r hn
      have hpart := congrArg (stagePhysicalPart q p d b m r (d.perm r .X)) hword
      have hkinc := hk.2.1
      rw [← hpart] at hkinc
      apply Subtype.ext
      exact (labels_eq_roleX q b m (M r) p d r (B r) (ω r)
        j.val k.val (by simpa [stageSelected, j] using hj.1)
        (by simpa [stageSelected, k] using hk.1) _
        (by simpa [j] using hj.2.1) (by simpa [k] using hkinc)).symm
  | Y =>
      let j := sourceLabelAt q p d b ε m M B ω (d.perm r .Y) x r hn
      let k := sourceLabelAt q p d b ε m M B ω (d.perm r .Y) y r hn
      have hj := source_properties q p d b ε m M B ω (d.perm r .Y) x r hn
      have hk := source_properties q p d b ε m M B ω (d.perm r .Y) y r hn
      have hpart := congrArg (stagePhysicalPart q p d b m r (d.perm r .Y)) hword
      have hkinc := hk.2.1
      rw [← hpart] at hkinc
      apply Subtype.ext
      exact (labels_eq_roleY q b m (M r) ε p d r (B r) (ω r)
        j.val k.val (by simpa [stageSelected, j] using hj.1)
        (by simpa [stageSelected, k] using hk.1) _
        (by simpa [j] using hj.2.1) (by simpa [k] using hkinc)
        (source_part_keep q p d b ε m M B ω (d.perm r .Y) x r hn)).symm
  | Z =>
      let j := sourceLabelAt q p d b ε m M B ω (d.perm r .Z) x r hn
      let k := sourceLabelAt q p d b ε m M B ω (d.perm r .Z) y r hn
      have hj := source_properties q p d b ε m M B ω (d.perm r .Z) x r hn
      have hk := source_properties q p d b ε m M B ω (d.perm r .Z) y r hn
      have hpart := congrArg (stagePhysicalPart q p d b m r (d.perm r .Z)) hword
      have hkinc := hk.2.1
      rw [← hpart] at hkinc
      apply Subtype.ext
      exact (labels_eq_roleZ q b m (M r) ε p d r (B r) (ω r)
        j.val k.val (by simpa [stageSelected, j] using hj.1)
        (by simpa [stageSelected, k] using hk.1) _
        (by simpa [j] using hj.2.1) (by simpa [k] using hkinc)
        (source_part_keep q p d b ε m M B ω (d.perm r .Z) x r hn)).symm

private theorem sourcePair_component_injective {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hpair : sourcePairAt q p d b ε m M B ω W x r hn =
      sourcePairAt q p d b ε m M B ω W y r hn) :
    productLegValue (stageRegionFamily q p d b ε m M B ω) W x r =
      productLegValue (stageRegionFamily q p d b ε m M B ω) W y r := by
  cases W <;>
    simpa [sourcePairAt, productLegValue, stageRegionFamily, hn] using hpair

private theorem sigmaSubtype_ext {I A : Type*} {p : I → A → Prop}
    {x y : (i : I) × {a : A // p i a}}
    (hfst : x.1 = y.1) (hval : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, a, ha⟩
  rcases y with ⟨j, b, hb⟩
  dsimp only at hfst hval
  subst j
  subst b
  rfl

set_option maxHeartbeats 1000000 in
private theorem sourcePair_eq_of_word_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hword : sourceWordAt q p d b ε m M B ω W x r =
      sourceWordAt q p d b ε m M B ω W y r) :
    sourcePairAt q p d b ε m M B ω W x r hn =
      sourcePairAt q p d b ε m M B ω W y r hn := by
  have hlabel := sourceLabel_eq_of_word_eq q m p d hd ε M B ω W x y r hn hword
  have hfst : (sourcePairAt q p d b ε m M B ω W x r hn).1 =
      (sourcePairAt q p d b ε m M B ω W y r hn).1 := by
    simpa [sourceLabelAt] using hlabel
  cases W <;>
    apply sigmaSubtype_ext hfst <;>
      simpa [sourceWordAt, hn] using hword

private theorem zero_component_eq {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n = 0) :
    productLegValue (stageRegionFamily q p d b ε m M B ω) W x r =
      productLegValue (stageRegionFamily q p d b ε m M B ω) W y r := by
  cases W with
  | X =>
      let hsub : Subsingleton (stageRegionFamily q p d b ε m M B ω r).X := by
        rw [stageRegionFamily, if_pos hn]
        exact ⟨fun a b => by cases a; cases b; rfl⟩
      exact hsub.elim _ _
  | Y =>
      let hsub : Subsingleton (stageRegionFamily q p d b ε m M B ω r).Y := by
        rw [stageRegionFamily, if_pos hn]
        exact ⟨fun a b => by cases a; cases b; rfl⟩
      exact hsub.elim _ _
  | Z =>
      let hsub : Subsingleton (stageRegionFamily q p d b ε m M B ω r).Z := by
        rw [stageRegionFamily, if_pos hn]
        exact ⟨fun a b => by cases a; cases b; rfl⟩
      exact hsub.elim _ _

private theorem sourceWords_injective {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) : Function.Injective
      (fun x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W =>
        fun r => sourceWordAt q p d b ε m M B ω W x r) := by
  intro x y hxy
  cases W <;> apply funext <;> intro r
  all_goals
    by_cases hn : (stagePopulationAt q p d b m r).n = 0
    · exact zero_component_eq q p d b ε m M B ω _ x y r hn
    · apply sourcePair_component_injective q p d b ε m M B ω _ x y r hn
      apply sourcePair_eq_of_word_eq q m p d hd ε M B ω _ x y r hn
      exact congrFun hxy r

private noncomputable def activeMap {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) :
    (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W →
      (regionalInputZ q p d (b*m) ε).leg W :=
  fun x => packPhysicalWords q m p d hb ε W
    (fun r => sourceWordAt q p d b ε m M B ω W x r)

private theorem activeMap_injective {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) : Function.Injective (activeMap q m p d hb ε M B ω W) := by
  exact (packPhysicalWords_injective q m p d hb ε W).comp
    (sourceWords_injective q m p d hd ε M B ω W)

private def localHashZero {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨0, by omega⟩

private def localHashOne {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨1, by omega⟩

private def localHashWeight {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  ω ⟨i.val + 2, by omega⟩

private def localHashX (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero ω + ∑ i, (P.coarse j .X i).val * localHashWeight ω i

private def localHashY (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero ω + localHashOne ω +
    ∑ i, (P.coarse j .Y i).val * localHashWeight ω i

private noncomputable def localHashZ (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero ω + Ring.inverse 2 *
    (localHashOne ω +
      ∑ i, (P.grade - (P.coarse j .Z i).val) * localHashWeight ω i)

private noncomputable def localSurvives (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun j =>
    localHashX P M ω j = localHashY P M ω j ∧
      localHashY P M ω j = localHashZ P M ω j ∧
      localHashX P M ω j ∈ B

private noncomputable def localSelected (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  exact (localSurvives P M B ω).filter fun j =>
    j ∈ P.target ∧ ∀ k ∈ localSurvives P M B ω,
      P.coarse k .X = P.coarse j .X → k = j

private theorem selected_eq_local (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) :
    selected P M B ω = localSelected P M B ω := by
  with_unfolding_all rfl

private theorem selected_hash_data (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (j : P.Label)
    (hj : j ∈ selected P M B ω) :
    localHashX P M ω j = localHashY P M ω j ∧
      localHashY P M ω j = localHashZ P M ω j ∧
      localHashX P M ω j ∈ B := by
  classical
  rw [selected_eq_local] at hj
  unfold localSelected at hj
  have hs := (Finset.mem_filter.mp hj).1
  simpa [localSurvives] using hs

private theorem complement_coord {w s : ℕ} (p : ConstituentInput w s)
    (t : Fin s) (u : ChildShape p t) (W : Side) :
    coord W (complement p t u).val =
      StageCandidateRaw.sideGrade p W t - coord W u.val := by
  cases W <;> rfl

private def mixedChildShape {w s : ℕ} {p : ConstituentInput w s}
    {b m : ℕ} {d : ConstituentSpec p} {r : Fin 6}
    (jX jY jZ : (stagePopulationAt 0 p d b m r).Label)
    (pos : StageCandidateRaw.StagePos b m p d r)
    (hsum : coord .X (jX.val pos).val + coord .Y (jY.val pos).val +
      coord .Z (jZ.val pos).val = 2*w) : ChildShape p pos.1 :=
  ⟨⟨((jX.val pos).val.1.1, (jY.val pos).val.1.2.1,
      (jZ.val pos).val.1.2.2), hsum⟩,
    (jX.val pos).property.1, (jY.val pos).property.2.1,
      (jZ.val pos).property.2.2⟩

set_option maxHeartbeats 1000000 in
private noncomputable def mixedStageLabel {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (jX jY jZ : (stagePopulationAt q p d b m r).Label)
    (hsum : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord .X (jX.val pos).val + coord .Y (jY.val pos).val +
        coord .Z (jZ.val pos).val = 2*w) :
    (stagePopulationAt q p d b m r).Label := by
  classical
  dsimp [stagePopulationAt] at jX jY jZ ⊢
  let J := fun pos : StageCandidateRaw.StagePos b m p d r =>
    mixedChildShape jX jY jZ pos (hsum pos)
  refine ⟨J, ?_, ?_⟩
  · intro t h W a
    cases W with
    | X => simpa [J, mixedChildShape, coord] using jX.property.1 t h .X a
    | Y => simpa [J, mixedChildShape, coord] using jY.property.1 t h .Y a
    | Z => simpa [J, mixedChildShape, coord] using jZ.property.1 t h .Z a
  · intro t i
    have hx := congrArg (fun u => coord .X u.val) (jX.property.2 t i)
    have hy := congrArg (fun u => coord .Y u.val) (jY.property.2 t i)
    have hz := congrArg (fun u => coord .Z u.val) (jZ.property.2 t i)
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simpa [J, mixedChildShape, complement_coord] using hx
    · apply Prod.ext
      · apply Fin.ext
        simpa [J, mixedChildShape, complement_coord] using hy
      · apply Fin.ext
        simpa [J, mixedChildShape, complement_coord] using hz

private theorem inverse_two_mul (M : ℕ) (hprime : Nat.Prime M) (hodd : 2 < M) :
    Ring.inverse (2 : ZMod M) * 2 = 1 := by
  apply Ring.inverse_mul_cancel
  have hnot : ¬ M ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) hodd
  have hcop : Nat.Coprime 2 M := by
    rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd]
    exact hnot
  exact (ZMod.unitOfCoprime 2 hcop).isUnit

private theorem local_hash_ap (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label)
    (htight : ∀ i, (P.coarse j .X i).val + (P.coarse j .Y i).val +
      (P.coarse j .Z i).val = P.grade)
    (hprime : Nat.Prime M) (hodd : 2 < M) :
    localHashX P M ω j + localHashY P M ω j =
      2 * localHashZ P M ω j := by
  have hcomp :
      (∑ i, (P.grade - (P.coarse j .Z i).val) * localHashWeight ω i) =
        (∑ i, (P.coarse j .X i).val * localHashWeight ω i) +
          ∑ i, (P.coarse j .Y i).val * localHashWeight ω i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hs := htight i
    have hz : (P.coarse j .Z i).val ≤ P.grade := by omega
    have hn : P.grade - (P.coarse j .Z i).val =
        (P.coarse j .X i).val + (P.coarse j .Y i).val := by omega
    rw [← Nat.cast_sub hz, hn, Nat.cast_add]
    ring
  have hinv := inverse_two_mul M hprime hodd
  unfold localHashX localHashY localHashZ
  rw [hcomp]
  calc
    localHashZero ω + ∑ i, (P.coarse j .X i).val * localHashWeight ω i +
        (localHashZero ω + localHashOne ω +
          ∑ i, (P.coarse j .Y i).val * localHashWeight ω i) =
      2 * localHashZero ω +
        (localHashOne ω +
          ((∑ i, (P.coarse j .X i).val * localHashWeight ω i) +
            ∑ i, (P.coarse j .Y i).val * localHashWeight ω i)) := by ring
    _ = 2 * (localHashZero ω + Ring.inverse 2 *
        (localHashOne ω +
          ((∑ i, (P.coarse j .X i).val * localHashWeight ω i) +
            ∑ i, (P.coarse j .Y i).val * localHashWeight ω i))) := by
      rw [mul_add, ← mul_assoc, show (2 : ZMod M) * Ring.inverse 2 = 1 by
        rw [mul_comm, hinv], one_mul]

private theorem side_univ : (Finset.univ : Finset Side) = {.X, .Y, .Z} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Unfolding the dependent stage-position carrier in all six role cases is elaboration-heavy.
private theorem stage_role_tight {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (i : Fin (stagePopulationAt q p d b m r).n) :
    ((rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j .X i).val +
      ((rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j .Y i).val +
      ((rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j .Z i).val =
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).grade := by
  letI : Fintype (StageCandidateRaw.StagePos b m p d r) := Fintype.ofFinite _
  dsimp [rolePopulation, stagePopulationAt] at j i ⊢
  let u := (j.val ((Fintype.equivFin
    (StageCandidateRaw.StagePos b m p d r)).symm i)).val
  let e : Side ≃ Side := Equiv.ofBijective (d.perm r) (hd.roles.1 r)
  have he := Equiv.sum_comp e (fun W => coord W u)
  have hplain : (∑ W, coord W u) = 2 * w := by
    rw [side_univ]
    simpa [coord, add_assoc] using
      (j.val ((Fintype.equivFin (StageCandidateRaw.StagePos b m p d r)).symm i)).val.property
  have hh := he.trans hplain
  rw [side_univ] at hh
  dsimp only [e, Equiv.ofBijective_apply] at hh
  dsimp [u, StageCandidateRaw.StagePos, StageCandidateRaw.stageParentCount,
    StageCandidateRaw.stageAlphaCount] at hh
  have hXY : d.perm r .X ≠ d.perm r .Y :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hXZ : d.perm r .X ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hYZ : d.perm r .Y ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  cases hX : d.perm r .X <;>
    cases hY : d.perm r .Y <;>
      cases hZ : d.perm r .Z <;>
        simp_all [u, coord, add_assoc] <;> omega

private def physicalLabel {w s : ℕ} {q b m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {r : Fin 6}
    (jX jY jZ : (stagePopulationAt q p d b m r).Label) (W : Side) :
    (stagePopulationAt q p d b m r).Label :=
  match W with
  | .X => jX
  | .Y => jY
  | .Z => jZ

set_option maxHeartbeats 1000000 in
-- Both sides unfold the stage population's internal finite position equivalence.
private theorem mixedStageLabel_coarse {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (jX jY jZ : (stagePopulationAt q p d b m r).Label)
    (hsum : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord .X (jX.val pos).val + coord .Y (jY.val pos).val +
        coord .Z (jZ.val pos).val = 2*w) (W : Side) :
    (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse
        (mixedStageLabel q b m p d r jX jY jZ hsum) W =
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse
        (physicalLabel jX jY jZ (d.perm r W)) W := by
  funext i
  apply Fin.ext
  dsimp [rolePopulation, stagePopulationAt]
  cases hW : d.perm r W <;> rfl

private theorem mixedStageLabel_coord {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (jX jY jZ : (stagePopulationAt q p d b m r).Label)
    (hsum : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord .X (jX.val pos).val + coord .Y (jY.val pos).val +
        coord .Z (jZ.val pos).val = 2*w)
    (W : Side) (pos : StageCandidateRaw.StagePos b m p d r) :
    coord W ((mixedStageLabel q b m p d r jX jY jZ hsum).val pos).val =
      coord W ((physicalLabel jX jY jZ W).val pos).val := by
  cases W <;> rfl

private theorem localHashX_eq_of_coarse (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .X = P.coarse k .X) :
    localHashX P M ω j = localHashX P M ω k := by
  unfold localHashX
  rw [h]

private theorem localHashY_eq_of_coarse (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .Y = P.coarse k .Y) :
    localHashY P M ω j = localHashY P M ω k := by
  unfold localHashY
  rw [h]

private theorem localHashZ_eq_of_coarse (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .Z = P.coarse k .Z) :
    localHashZ P M ω j = localHashZ P M ω k := by
  unfold localHashZ
  rw [h]

private theorem selected_unique_local (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (j k : P.Label)
    (hj : j ∈ selected P M B ω) (hk : k ∈ localSurvives P M B ω)
    (hcoarse : P.coarse k .X = P.coarse j .X) : k = j := by
  classical
  rw [selected_eq_local] at hj
  exact (Finset.mem_filter.mp (show j ∈ localSelected P M B ω from hj)).2.2
    k hk hcoarse

set_option maxHeartbeats 2000000 in
-- This is the paper's mixed-label/AP-free alignment in role coordinates.
private theorem physical_labels_align {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B) (r : Fin 6)
    (jX jY jZ : (stagePopulationAt q p d b m r).Label)
    (hsel : ∀ W, physicalLabel jX jY jZ W ∈ stageSelected q p d b m M B ω r)
    (hsum : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord .X (jX.val pos).val + coord .Y (jY.val pos).val +
        coord .Z (jZ.val pos).val = 2 * w) :
    ∀ (W : Side) (pos : StageCandidateRaw.StagePos b m p d r),
      coord (d.perm r W)
          ((physicalLabel jX jY jZ (d.perm r .X)).val pos).val =
        coord (d.perm r W)
          ((physicalLabel jX jY jZ (d.perm r W)).val pos).val := by
  classical
  let P := rolePopulation (stagePopulationAt q p d b m r) (d.perm r)
  let jL := fun W => physicalLabel jX jY jZ (d.perm r W)
  let jmix := mixedStageLabel q b m p d r jX jY jZ hsum
  have hcX : P.coarse jmix .X = P.coarse (jL .X) .X := by
    simpa [P, jL, jmix] using
      mixedStageLabel_coarse q b m p d r jX jY jZ hsum .X
  have hcY : P.coarse jmix .Y = P.coarse (jL .Y) .Y := by
    simpa [P, jL, jmix] using
      mixedStageLabel_coarse q b m p d r jX jY jZ hsum .Y
  have hcZ : P.coarse jmix .Z = P.coarse (jL .Z) .Z := by
    simpa [P, jL, jmix] using
      mixedStageLabel_coarse q b m p d r jX jY jZ hsum .Z
  have hhX := localHashX_eq_of_coarse P (M r) (ω r) jmix (jL .X) hcX
  have hhY := localHashY_eq_of_coarse P (M r) (ω r) jmix (jL .Y) hcY
  have hhZ := localHashZ_eq_of_coarse P (M r) (ω r) jmix (jL .Z) hcZ
  have hdX := selected_hash_data P (M r) (B r) (ω r) (jL .X) (by
    simpa [P, jL, stageSelected] using hsel (d.perm r .X))
  have hdY := selected_hash_data P (M r) (B r) (ω r) (jL .Y) (by
    simpa [P, jL, stageSelected] using hsel (d.perm r .Y))
  have hdZ := selected_hash_data P (M r) (B r) (ω r) (jL .Z) (by
    simpa [P, jL, stageSelected] using hsel (d.perm r .Z))
  have hmixAP := local_hash_ap P (M r) (ω r) jmix
    (fun i => by simpa [P, jmix] using stage_role_tight q m p d hd r jmix i)
    (hvalid r).1 (hvalid r).2.1
  rw [hhX, hhY, hhZ] at hmixAP
  have hZmem : localHashZ P (M r) (ω r) (jL .Z) ∈ B r := by
    rw [← hdZ.2.1, ← hdZ.1]
    exact hdZ.2.2
  have hYmem : localHashY P (M r) (ω r) (jL .Y) ∈ B r := by
    rw [← hdY.1]
    exact hdY.2.2
  have hAP := (hvalid r).2.2.2
    (localHashX P (M r) (ω r) (jL .X)) hdX.2.2
    (localHashZ P (M r) (ω r) (jL .Z)) hZmem
    (localHashY P (M r) (ω r) (jL .Y)) hYmem hmixAP
  have hsurv : jmix ∈ localSurvives P (M r) (B r) (ω r) := by
    simp only [localSurvives, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [hhX, hhY]
      exact hAP.1.trans hAP.2.symm
    constructor
    · rw [hhY, hhZ]
      exact hAP.2
    · rw [hhX]
      exact hdX.2.2
  have hjLX : jL .X ∈ selected P (M r) (B r) (ω r) := by
    simpa [P, jL, stageSelected] using hsel (d.perm r .X)
  have hmixed : jmix = jL .X :=
    selected_unique_local P (M r) (B r) (ω r) (jL .X) jmix hjLX hsurv hcX
  intro W pos
  have hc := mixedStageLabel_coord q b m p d r jX jY jZ hsum (d.perm r W) pos
  change coord (d.perm r W) (jmix.val pos).val =
    coord (d.perm r W) ((jL W).val pos).val at hc
  rw [hmixed] at hc
  simpa [jL, jmix] using hc

set_option maxHeartbeats 2000000 in
-- A nonzero regional-input coefficient makes each underlying CW coordinate nonzero.
private theorem regionalInput_cw_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (ε : ℚ)
    (x : (regionalInputZ q p d (b*m) ε).X)
    (y : (regionalInputZ q p d (b*m) ε).Y)
    (z : (regionalInputZ q p d (b*m) ε).Z)
    (hxyz : (regionalInputZ q p d (b*m) ε).tensor x y z ≠ 0)
    (r : Fin 6) (pos : StageCandidateRaw.StagePos b m p d r) (c : Fin (w+w)) :
    cwZ q
      (regionalLegValue q m p d ε .X x
        (Fintype.equivFin (Fin s × Fin 6) (pos.1, r))
        (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
          stageParentCount_eq_regionalCount p d b m hb pos.1 r) pos.2.1) c)
      (regionalLegValue q m p d ε .Y y
        (Fintype.equivFin (Fin s × Fin 6) (pos.1, r))
        (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
          stageParentCount_eq_regionalCount p d b m hb pos.1 r) pos.2.1) c)
      (regionalLegValue q m p d ε .Z z
        (Fintype.equivFin (Fin s × Fin 6) (pos.1, r))
        (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
          stageParentCount_eq_regionalCount p d b m hb pos.1 r) pos.2.1) c) ≠ 0 := by
  classical
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  let slot := Fintype.equivFin (Fin s × Fin 6) (pos.1, r)
  let n := fun a : Fin (Fintype.card (Fin s × Fin 6)) =>
    (((b*m : ℕ) : ℚ) * (p.baseN (e a).1 : ℚ) *
      (d.A (e a).1).prob (e a).2).floor.toNat
  let ii : Fin (n slot) := Fin.cast (by
    simpa [n, slot, e, Equiv.symm_apply_apply] using
      stageParentCount_eq_regionalCount p d b m hb pos.1 r) pos.2.1
  have hn : n slot ≠ 0 := by
    intro hzero
    have := ii.isLt
    omega
  unfold regionalInputZ at hxyz
  unfold supportedIfaceZ at hxyz
  dsimp only [ITensor.tensor] at hxyz
  rw [ADVXXZ.zoP_apply] at hxyz
  split at hxyz
  next hs =>
    unfold ifaceZ at hxyz
    rw [Finset.prod_ne_zero_iff] at hxyz
    have ht := hxyz slot (Finset.mem_univ slot)
    unfold ifaceTermZ at ht
    rw [if_neg hn] at ht
    split at ht
    next ha =>
      unfold tensorPower at ht
      rw [Finset.prod_ne_zero_iff] at ht
      have hc := ht ii (Finset.mem_univ ii)
      unfold conZ at hc
      rw [ADVXXZ.zoP_apply] at hc
      split at hc
      next hl =>
        unfold tensorPower at hc
        rw [Finset.prod_ne_zero_iff] at hc
        have hcw := hc c (Finset.mem_univ c)
        simpa [regionalLegValue, n, slot, e, ii, Equiv.symm_apply_apply] using hcw
      next hl => exact (hc rfl).elim
    next ha => exact (ht rfl).elim
  next hs => exact (hxyz rfl).elim

private theorem lvl7_add_of_cwZ_ne {q : ℕ} (a b c : CW90.Idx7 q)
    (h : cwZ q a b c ≠ 0) :
    (CW90.lvl7 a).val + (CW90.lvl7 b).val + (CW90.lvl7 c).val = 2 := by
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
    rcases c with (_ | c) | c <;> simp_all [cwZ, CW90.lvl7]

set_option maxHeartbeats 2000000 in
-- Source support turns a nonzero packed entry into a compatible physical label triple.
private theorem source_label_sum {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (hxyz : (regionalInputZ q p d (b*m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (pos : StageCandidateRaw.StagePos b m p d r) :
    coord .X ((sourceLabelAt q p d b ε m M B ω .X x r hn).val.val pos).val +
      coord .Y ((sourceLabelAt q p d b ε m M B ω .Y y r hn).val.val pos).val +
      coord .Z ((sourceLabelAt q p d b ε m M B ω .Z z r hn).val.val pos).val =
      2*w := by
  classical
  have hpX := source_properties q p d b ε m M B ω .X x r hn
  have hpY := source_properties q p d b ε m M B ω .Y y r hn
  have hpZ := source_properties q p d b ε m M B ω .Z z r hn
  rw [← hpX.2.1.1 pos, ← hpY.2.1.1 pos, ← hpZ.2.1.1 pos]
  simp only [stagePhysicalPart, chunkLvl, chunkOf]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    ∑ c : Fin w,
        ((CW90.lvl7 (sourceWordAt q p d b ε m M B ω .X x r pos c)).val +
          (CW90.lvl7 (sourceWordAt q p d b ε m M B ω .Y y r pos c)).val +
          (CW90.lvl7 (sourceWordAt q p d b ε m M B ω .Z z r pos c)).val) =
        ∑ _c : Fin w, 2 := by
      apply Finset.sum_congr rfl
      intro c _hc
      apply lvl7_add_of_cwZ_ne
      have hcw := regionalInput_cw_ne q m p d hb ε
        (activeMap q m p d hb ε M B ω .X x)
        (activeMap q m p d hb ε M B ω .Y y)
        (activeMap q m p d hb ε M B ω .Z z) hxyz r pos
        (joinedCoord pos.2.2 c)
      dsimp only [activeMap] at hcw
      rw [packPhysicalWords_apply q m p d hb ε .X
          (fun r => sourceWordAt q p d b ε m M B ω .X x r) r pos c,
        packPhysicalWords_apply q m p d hb ε .Y
          (fun r => sourceWordAt q p d b ε m M B ω .Y y r) r pos c,
        packPhysicalWords_apply q m p d hb ε .Z
          (fun r => sourceWordAt q p d b ε m M B ω .Z z r) r pos c] at hcw
      exact hcw
    _ = 2*w := by simp [Nat.mul_comm]

end
end OmegaBound.ADVXXZGeneral
end
