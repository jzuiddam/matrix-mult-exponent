import OmegaBound.ADVXXZGeneralCExact36GridPartition

set_option autoImplicit false

section
universe u v
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
namespace CExact36EmbeddingAux
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
    (hb : ConstituentIntegral36 d b m) (t : Fin s) (r : Fin 6) :
    StageCandidateRaw.stageParentCount b m p d r t =
      (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat := by
  classical
  let kA : ℕ := Classical.choose (hb.regionIntegral t r)
  let kα : ChildShape p t → ℕ := fun u => Classical.choose (hb.alphaIntegral t r u)
  have hkA : (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r = (kA : ℚ) :=
    Classical.choose_spec (hb.regionIntegral t r)
  have hkα : ∀ u, (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u = (kα u : ℚ) :=
    fun u => Classical.choose_spec (hb.alphaIntegral t r u)
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
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
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
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
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
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
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
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side) :
    (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W →
      (regionalInputZ q p d (b*m) ε).leg W :=
  fun x => packPhysicalWords q m p d hb ε W
    (fun r => sourceWordAt q p d b ε m M B ω W x r)

private theorem activeMap_injective {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
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
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
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
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
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

private def sideWord {A : Type} (x y z : A) : Side → A
  | .X => x
  | .Y => y
  | .Z => z

private theorem sideWord_apply {A B : Type} (x y z : A → B) (W : Side) (a : A) :
    sideWord x y z W a = sideWord (x a) (y a) (z a) W := by
  cases W <;> rfl

private theorem lvl7_eq_zero_of_chunkLvl_eq_zero {q w : ℕ}
    (a : Fin w → CW90.Idx7 q) (h : chunkLvl (chunkOf a) = 0) (c : Fin w) :
    (CW90.lvl7 (a c)).val = 0 := by
  have hle : (chunkOf a c).val ≤ chunkLvl (chunkOf a) := by
    unfold chunkLvl
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun p => (chunkOf a p).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simpa only [chunkOf] using (show (chunkOf a c).val = 0 by omega)

private theorem cwZ_ne_permutations {q : ℕ} (x y z : CW90.Idx7 q)
    (h : cwZ q x y z ≠ 0) :
    cwZ q y x z ≠ 0 ∧ cwZ q x z y ≠ 0 ∧ cwZ q y z x ≠ 0 ∧
      cwZ q z x y ≠ 0 ∧ cwZ q z y x ≠ 0 := by
  rcases x with (_ | x₀) | x₀ <;>
    rcases y with (_ | y₀) | y₀ <;>
      rcases z with (_ | z₀) | z₀ <;> simp_all [cwZ]

set_option maxHeartbeats 1000000 in
private theorem chunk_reflect_last_of_cwZ_ne {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf z) = 0) :
    chunkOf y = reflect (chunkOf x) := by
  funext c
  apply Fin.ext
  have hz := lvl7_eq_zero_of_chunkLvl_eq_zero z hzero c
  have hw := hcw c
  rcases hx : x c with (_ | x₀) | x₀ <;>
    rcases hy : y c with (_ | y₀) | y₀ <;>
      rcases hz' : z c with (_ | z₀) | z₀ <;>
        simp_all [cwZ, chunkOf, reflect, CW90.lvl7]

private theorem chunk_reflect_of_cwZ_ne {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf (sideWord x y z C)) = 0) :
    chunkOf (sideWord x y z B) = reflect (chunkOf (sideWord x y z A)) := by
  cases A <;> cases B <;> cases C <;> simp_all [sideWord]
  · exact chunk_reflect_last_of_cwZ_ne x y z hcw hzero
  · exact chunk_reflect_last_of_cwZ_ne x z y
      (fun c => (cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne y x z
      (fun c => (cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).1) hzero
  · exact chunk_reflect_last_of_cwZ_ne y z x
      (fun c => (cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne z x y
      (fun c => (cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne z y x
      (fun c => (cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.2) hzero

private theorem reflect_reflect {w : ℕ} (σ : Chunk w) : reflect (reflect σ) = σ := by
  funext c
  apply Fin.ext
  simp only [reflect]
  have hc := (σ c).isLt
  omega

set_option maxHeartbeats 1000000 in
private theorem incidence_exact_cell_final {w s : ℕ} (q b m : ℕ)
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

private theorem cellCount_exact_reflect {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (A B : Side) (j : (stagePopulationAt q p d b m r).Label)
    (aA : (stagePopulationAt q p d b m r).Part A)
    (aB : (stagePopulationAt q p d b m r).Part B)
    (t : Fin s) (u : ChildShape p t) (σ : Chunk w)
    (hreflect : ∀ ih : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2,
      j.val ⟨t, ih⟩ = u → (aB ⟨t, ih⟩ = σ ↔ aA ⟨t, ih⟩ = reflect σ)) :
    stageCandidateCellCount q p d b m r B j aB t (fun v => v = u.val) σ =
      stageCandidateCellCount q p d b m r A j aA t
        (fun v => v = u.val) (reflect σ) := by
  unfold stageCandidateCellCount
  apply congrArg Finset.card
  ext pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases pos with ⟨t₀, ih⟩
  dsimp only
  by_cases ht : t₀ = t
  · subst t₀
    constructor
    · rintro ⟨_, hju, ha⟩
      exact ⟨rfl, hju, (hreflect ih (Subtype.ext hju)).mp ha⟩
    · rintro ⟨_, hju, ha⟩
      exact ⟨rfl, hju, (hreflect ih (Subtype.ext hju)).mpr ha⟩
  · simp [ht]

private theorem cellCount_grade_congr {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (j k : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part W)
    (halign : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord W (j.val pos).val = coord W (k.val pos).val)
    (t : Fin s) (grade : Fin (2*w+1)) (σ : Chunk w) :
    stageCandidateCellCount q p d b m r W j a t
        (fun u => coord W u = grade.val) σ =
      stageCandidateCellCount q p d b m r W k a t
        (fun u => coord W u = grade.val) σ := by
  unfold stageCandidateCellCount
  apply congrArg Finset.card
  ext pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [halign pos]

set_option maxHeartbeats 1000000 in
private theorem boundary_cell_count_from_words {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (x y z : StagePhysicalWord q p d b m r) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hincA : (stagePopulationAt q p d b m r).incidence A j
      (stagePhysicalPart q p d b m r A (sideWord x y z A)))
    (hcoarseC : stageCandidateCoarseContains q p d b m r C j
      (stagePhysicalPart q p d b m r C (sideWord x y z C)))
    (hcw : ∀ pos c, cwZ q (x pos c) (y pos c) (z pos c) ≠ 0)
    (t : Fin s) (u : ChildShape p t) (hboundary : coord C u.val = 0)
    (σ : Chunk w) :
    stageCandidateCellCount q p d b m r B j
        (stagePhysicalPart q p d b m r B (sideWord x y z B)) t
        (fun v => v = u.val) σ =
      ((m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild B t r u).prob σ).floor.toNat := by
  rw [cellCount_exact_reflect q b m p d r A B j
    (stagePhysicalPart q p d b m r A (sideWord x y z A))
    (stagePhysicalPart q p d b m r B (sideWord x y z B)) t u σ]
  · rw [incidence_exact_cell_final q b m p d r A j _ hincA t u (reflect σ)]
    have hbeta := hd.child_boundary t r u C A B hAB hAC hBC hboundary (reflect σ)
    rw [reflect_reflect] at hbeta
    rw [hbeta]
  · intro ih hju
    let pos : StageCandidateRaw.StagePos b m p d r := ⟨t, ih⟩
    have hzero : chunkLvl (chunkOf (sideWord x y z C pos)) = 0 := by
      calc
        chunkLvl (chunkOf (sideWord x y z C pos)) =
            coord C (j.val pos).val := by
          simpa only [stagePhysicalPart] using hcoarseC pos
        _ = coord C u.val := by rw [hju]
        _ = 0 := hboundary
    have hzero' : chunkLvl (chunkOf (sideWord (x pos) (y pos) (z pos) C)) = 0 := by
      rw [← sideWord_apply] 
      exact hzero
    have hreflect := chunk_reflect_of_cwZ_ne
      (x pos) (y pos) (z pos) A B C hAB hAC hBC (hcw pos) hzero'
    have hreflect' : chunkOf (sideWord x y z B pos) =
        reflect (chunkOf (sideWord x y z A pos)) := by
      rw [sideWord_apply, sideWord_apply]
      exact hreflect
    simpa only [stagePhysicalPart] using (show
      chunkOf (sideWord x y z B pos) = σ ↔
        chunkOf (sideWord x y z A pos) = reflect σ by
      rw [hreflect']
      constructor
      · intro h
        have := congrArg reflect h
        simpa only [reflect_reflect] using this
      · intro h
        rw [h, reflect_reflect])

private theorem compatible_of_boundary_and_alignment {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j k : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part
      (d.perm r (if which = 0 then .Y else .Z)))
    (hboundary : ∀ t (u : ChildShape p t),
      (if which = 0 then coord (d.perm r .Z) u.val = 0
        else coord (d.perm r .X) u.val = 0 ∨ coord (d.perm r .Y) u.val = 0) →
      ∀ σ, stageCandidateCellCount q p d b m r
        (d.perm r (if which = 0 then .Y else .Z)) j a t
          (fun v => v = u.val) σ =
        ((m : ℚ) * d.outBase ⟨t,r,u⟩ *
          (d.betaChild (d.perm r (if which = 0 then .Y else .Z)) t r u).prob σ).floor.toNat)
    (halign : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord (d.perm r (if which = 0 then .Y else .Z)) (j.val pos).val =
        coord (d.perm r (if which = 0 then .Y else .Z)) (k.val pos).val)
    (hinc : (stagePopulationAt q p d b m r).incidence
      (d.perm r (if which = 0 then .Y else .Z)) k a) :
    stageCandidateCompatible q p d b m r which j a := by
  have hk := incidence_compatible q b m p d r which k a hinc
  unfold stageCandidateCompatible at hk ⊢
  dsimp only at hk ⊢
  have hside :
      (if which = 0 then d.perm r .Y else d.perm r .Z) =
        d.perm r (if which = 0 then .Y else .Z) := by
    by_cases hw : which = 0 <;> simp [hw]
  rw [hside] at hk ⊢
  constructor
  · exact hboundary
  · intro t grade σ
    rw [cellCount_grade_congr q b m p d r _ j k a halign t grade σ]
    exact hk.2 t grade σ

private theorem roleY_label_eq_of_candidate {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .Y))
    (hjcoarse : stageCandidateCoarseContains q p d b m r (d.perm r .Y) j a)
    (hjcompat : stageCandidateCompatible q p d b m r 0 j a)
    (hkinc : (stagePopulationAt q p d b m r).incidence (d.perm r .Y) k a)
    (hkeep : stagePartKeepAt25 q b m M ε p d r B ω .zUseful
      (d.perm r .Y) a) : k = j := by
  classical
  unfold stagePartKeepAt25 at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_, _, _, _, hunique, _, _, _, _⟩
  let S := selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω
  let matching := S.filter fun l => Parent25.containsSide p d b m r (d.perm r .Y) l a
  let C := matching.filter fun l => Parent25.compatible p d b m r 0 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hunique rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hj, by simpa [stageCandidateCoarseContains, Parent25.containsSide] using hjcoarse⟩,
      (compatible_iff_parent25 q b m p d r 0 j a).mp hjcompat⟩
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hk, ?_⟩, ?_⟩
    · simpa [stageCandidateCoarseContains, Parent25.containsSide] using
        incidence_coarse q b m p d r _ k a hkinc
    · exact (compatible_iff_parent25 q b m p d r 0 k a).mp
        (incidence_compatible q b m p d r 0 k a hkinc)
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

private theorem roleZ_label_eq_of_candidate {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω)
    (a : (stagePopulationAt q p d b m r).Part (d.perm r .Z))
    (hjcoarse : stageCandidateCoarseContains q p d b m r (d.perm r .Z) j a)
    (hjcompat : stageCandidateCompatible q p d b m r 1 j a)
    (hkinc : (stagePopulationAt q p d b m r).incidence (d.perm r .Z) k a)
    (hkeep : stagePartKeepAt25 q b m M ε p d r B ω .zUseful
      (d.perm r .Z) a) : k = j := by
  classical
  unfold stagePartKeepAt25 at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_, _, _, _, _, _, _, hunique, _⟩
  let S := selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω
  let matching := S.filter fun l => Parent25.containsSide p d b m r (d.perm r .Z) l a
  let C := matching.filter fun l => Parent25.compatible p d b m r 1 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hunique rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hj, by simpa [stageCandidateCoarseContains, Parent25.containsSide] using hjcoarse⟩,
      (compatible_iff_parent25 q b m p d r 1 j a).mp hjcompat⟩
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    refine ⟨⟨hk, ?_⟩, ?_⟩
    · simpa [stageCandidateCoarseContains, Parent25.containsSide] using
        incidence_coarse q b m p d r _ k a hkinc
    · exact (compatible_iff_parent25 q b m p d r 1 k a).mp
        (incidence_compatible q b m p d r 1 k a hkinc)
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

set_option maxHeartbeats 3000000 in
-- The ordered Y-then-Z boundary step.
theorem source_role_labels_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (htarget : (regionalInputZ q p d (b*m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    let lX := sourceLabelAt q p d b ε m M B ω .X x r hn
    let lY := sourceLabelAt q p d b ε m M B ω .Y y r hn
    let lZ := sourceLabelAt q p d b ε m M B ω .Z z r hn
    let label := fun W => physicalLabel lX.val lY.val lZ.val W
    label (d.perm r .Y) = label (d.perm r .X) ∧
      label (d.perm r .Z) = label (d.perm r .X) := by
  classical
  let lX := sourceLabelAt q p d b ε m M B ω .X x r hn
  let lY := sourceLabelAt q p d b ε m M B ω .Y y r hn
  let lZ := sourceLabelAt q p d b ε m M B ω .Z z r hn
  let label := fun W => physicalLabel lX.val lY.val lZ.val W
  let wX := sourceWordAt q p d b ε m M B ω .X x r
  let wY := sourceWordAt q p d b ε m M B ω .Y y r
  let wZ := sourceWordAt q p d b ε m M B ω .Z z r
  have hpX := source_properties q p d b ε m M B ω .X x r hn
  have hpY := source_properties q p d b ε m M B ω .Y y r hn
  have hpZ := source_properties q p d b ε m M B ω .Z z r hn
  have hselected : ∀ W, label W ∈
      selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
        (M r) (B r) (ω r) := by
    intro W
    cases W with
    | X =>
        change lX.val ∈ selected
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
            (M r) (B r) (ω r)
        exact hpX.1
    | Y =>
        change lY.val ∈ selected
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
            (M r) (B r) (ω r)
        exact hpY.1
    | Z =>
        change lZ.val ∈ selected
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
            (M r) (B r) (ω r)
        exact hpZ.1
  have hinc : ∀ W, (stagePopulationAt q p d b m r).incidence W (label W)
      (stagePhysicalPart q p d b m r W (sideWord wX wY wZ W)) := by
    intro W
    cases W with
    | X => simpa [label, lX, wX, sideWord, physicalLabel] using hpX.2.1
    | Y => simpa [label, lY, wY, sideWord, physicalLabel] using hpY.2.1
    | Z => simpa [label, lZ, wZ, sideWord, physicalLabel] using hpZ.2.1
  have hkeep : ∀ W, stagePartKeepAt25 q b m (M r) ε p d r (B r) (ω r)
      .zUseful W (stagePhysicalPart q p d b m r W (sideWord wX wY wZ W)) := by
    intro W
    cases W with
    | X => simpa [wX, sideWord] using
        source_part_keep q p d b ε m M B ω .X x r hn
    | Y => simpa [wY, sideWord] using
        source_part_keep q p d b ε m M B ω .Y y r hn
    | Z => simpa [wZ, sideWord] using
        source_part_keep q p d b ε m M B ω .Z z r hn
  have hsum : ∀ pos : StageCandidateRaw.StagePos b m p d r,
      coord .X (lX.val.val pos).val + coord .Y (lY.val.val pos).val +
        coord .Z (lZ.val.val pos).val = 2*w := by
    intro pos
    simpa [lX, lY, lZ] using
      source_label_sum q m p d hb ε M B ω x y z htarget r hn pos
  have halign := physical_labels_align q m p d hd M B ω hvalid r
    lX.val lY.val lZ.val (by simpa [label] using hselected) hsum
  have hcoarse : ∀ R, stageCandidateCoarseContains q p d b m r (d.perm r R)
      (label (d.perm r .X))
      (stagePhysicalPart q p d b m r (d.perm r R)
        (sideWord wX wY wZ (d.perm r R))) := by
    intro R pos
    calc
      chunkLvl (stagePhysicalPart q p d b m r (d.perm r R)
          (sideWord wX wY wZ (d.perm r R)) pos) =
          coord (d.perm r R) ((label (d.perm r R)).val pos).val :=
        (hinc (d.perm r R)).1 pos
      _ = coord (d.perm r R) ((label (d.perm r .X)).val pos).val :=
        (halign R pos).symm
  have hcw : ∀ pos : StageCandidateRaw.StagePos b m p d r, ∀ c : Fin w,
      cwZ q (wX pos c) (wY pos c) (wZ pos c) ≠ 0 := by
    intro pos c
    have hc := regionalInput_cw_ne q m p d hb ε
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) htarget r pos
      (joinedCoord pos.2.2 c)
    rw [show activeMap q m p d hb ε M B ω .X x =
          packPhysicalWords q m p d hb ε .X
            (fun r => sourceWordAt q p d b ε m M B ω .X x r) by rfl,
      show activeMap q m p d hb ε M B ω .Y y =
          packPhysicalWords q m p d hb ε .Y
            (fun r => sourceWordAt q p d b ε m M B ω .Y y r) by rfl,
      show activeMap q m p d hb ε M B ω .Z z =
          packPhysicalWords q m p d hb ε .Z
            (fun r => sourceWordAt q p d b ε m M B ω .Z z r) by rfl] at hc
    rw [packPhysicalWords_apply q m p d hb ε .X
        (fun r => sourceWordAt q p d b ε m M B ω .X x r) r pos c,
      packPhysicalWords_apply q m p d hb ε .Y
        (fun r => sourceWordAt q p d b ε m M B ω .Y y r) r pos c,
      packPhysicalWords_apply q m p d hb ε .Z
        (fun r => sourceWordAt q p d b ε m M B ω .Z z r) r pos c] at hc
    simpa [wX, wY, wZ] using hc
  have hXY : d.perm r .X ≠ d.perm r .Y :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hXZ : d.perm r .X ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hYZ : d.perm r .Y ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hcompatY : stageCandidateCompatible q p d b m r 0
      (label (d.perm r .X))
      (stagePhysicalPart q p d b m r (d.perm r .Y)
        (sideWord wX wY wZ (d.perm r .Y))) := by
    apply compatible_of_boundary_and_alignment q b m p d r 0
      (label (d.perm r .X)) (label (d.perm r .Y))
    · intro t u hboundary σ
      simpa using boundary_cell_count_from_words q b m p d hd r
        (label (d.perm r .X)) wX wY wZ
        (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
        hXY hXZ hYZ (hinc (d.perm r .X)) (hcoarse .Z) hcw
        t u hboundary σ
    · intro pos
      exact halign .Y pos
    · exact hinc (d.perm r .Y)
  have hY : label (d.perm r .Y) = label (d.perm r .X) :=
    roleY_label_eq_of_candidate q b m (M r) ε p d r (B r) (ω r)
      (label (d.perm r .X)) (label (d.perm r .Y))
      (hselected (d.perm r .X)) (hselected (d.perm r .Y)) _
      (hcoarse .Y) hcompatY (hinc (d.perm r .Y)) (hkeep (d.perm r .Y))
  have hincY0 := hinc (d.perm r .Y)
  rw [hY] at hincY0
  have hcompatZ : stageCandidateCompatible q p d b m r 1
      (label (d.perm r .X))
      (stagePhysicalPart q p d b m r (d.perm r .Z)
        (sideWord wX wY wZ (d.perm r .Z))) := by
    apply compatible_of_boundary_and_alignment q b m p d r 1
      (label (d.perm r .X)) (label (d.perm r .Z))
    · intro t u hboundary σ
      rcases hboundary with hX0 | hY0
      · simpa using boundary_cell_count_from_words q b m p d hd r
          (label (d.perm r .X)) wX wY wZ
          (d.perm r .Y) (d.perm r .Z) (d.perm r .X)
          hYZ hXY.symm hXZ.symm hincY0 (hcoarse .X) hcw t u hX0 σ
      · simpa using boundary_cell_count_from_words q b m p d hd r
          (label (d.perm r .X)) wX wY wZ
          (d.perm r .X) (d.perm r .Z) (d.perm r .Y)
          hXZ hXY hYZ.symm (hinc (d.perm r .X)) (hcoarse .Y) hcw t u hY0 σ
    · intro pos
      exact halign .Z pos
    · exact hinc (d.perm r .Z)
  have hZ : label (d.perm r .Z) = label (d.perm r .X) :=
    roleZ_label_eq_of_candidate q b m (M r) ε p d r (B r) (ω r)
      (label (d.perm r .X)) (label (d.perm r .Z))
      (hselected (d.perm r .X)) (hselected (d.perm r .Z)) _
      (hcoarse .Z) hcompatZ (hinc (d.perm r .Z)) (hkeep (d.perm r .Z))
  exact ⟨hY, hZ⟩

private theorem prod_eq_zero_or_one {ι : Type} [Fintype ι]
    (f : ι → ℤ) (h : ∀ i, f i = 0 ∨ f i = 1) :
    (∏ i, f i) = 0 ∨ (∏ i, f i) = 1 := by
  classical
  by_cases hz : ∃ i, f i = 0
  · rcases hz with ⟨i, hi⟩
    exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  · right
    calc
      ∏ i, f i = ∏ _i : ι, (1 : ℤ) := by
        apply Finset.prod_congr rfl
        intro i _hi
        rcases h i with hi | hi
        · exact (hz ⟨i, hi⟩).elim
        · exact hi
      _ = 1 := by simp

private theorem cwZ_eq_zero_or_one (q : ℕ) (x y z : CW90.Idx7 q) :
    cwZ q x y z = 0 ∨ cwZ q x y z = 1 := by
  classical
  rcases x with (_ | x₀) | x₀ <;>
    rcases y with (_ | y₀) | y₀ <;>
      rcases z with (_ | z₀) | z₀ <;> simp [cwZ]
  all_goals exact Or.comm.mp (Classical.em _)

private theorem tensorPower_cwZ_eq_zero_or_one (q n : ℕ)
    (x y z : Fin n → CW90.Idx7 q) :
    tensorPower (cwZ q) n x y z = 0 ∨ tensorPower (cwZ q) n x y z = 1 := by
  exact prod_eq_zero_or_one _ (fun i => cwZ_eq_zero_or_one q (x i) (y i) (z i))

private theorem conZ_eq_zero_or_one (q w i j k : ℕ)
    (x y z : Fin w → CW90.Idx7 q) :
    conZ q w i j k x y z = 0 ∨ conZ q w i j k x y z = 1 := by
  unfold conZ
  rw [ADVXXZ.zoP_apply]
  split
  · exact tensorPower_cwZ_eq_zero_or_one q w x y z
  · exact Or.inl rfl

private theorem ifaceTermZ_eq_zero_or_one (q w i j k n : ℕ)
    (bX bY bZ : SplitDist w) (ε : ℚ)
    (x y z : Fin n → Fin w → CW90.Idx7 q) :
    ifaceTermZ q w i j k n bX bY bZ ε x y z = 0 ∨
      ifaceTermZ q w i j k n bX bY bZ ε x y z = 1 := by
  unfold ifaceTermZ
  split
  · exact Or.inr rfl
  · split
    · exact prod_eq_zero_or_one _
        (fun a => conZ_eq_zero_or_one q w i j k (x a) (y a) (z a))
    · exact Or.inl rfl

theorem regionalInputZ_eq_zero_or_one {w s : ℕ} (q n : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ)
    (x : (regionalInputZ q p d n ε).X)
    (y : (regionalInputZ q p d n ε).Y)
    (z : (regionalInputZ q p d n ε).Z) :
    (regionalInputZ q p d n ε).tensor x y z = 0 ∨
      (regionalInputZ q p d n ε).tensor x y z = 1 := by
  classical
  simp only [regionalInputZ, supportedIfaceZ, ITensor.tensor]
  rw [ADVXXZ.zoP_apply]
  split
  · unfold ifaceZ
    dsimp only [ITensor.tensor]
    apply prod_eq_zero_or_one
    intro slot
    let e := (Fintype.equivFin (Fin s × Fin 6)).symm
    exact ifaceTermZ_eq_zero_or_one q (w+w)
      (p.i (e slot).1) (p.j (e slot).1) (p.k (e slot).1)
      (((n : ℚ) * (p.baseN (e slot).1 : ℚ) *
        (d.A (e slot).1).prob (e slot).2).floor.toNat)
      (d.betaRegion .X (e slot).1 (e slot).2)
      (d.betaRegion .Y (e slot).1 (e slot).2)
      (d.betaRegion .Z (e slot).1 (e slot).2) ε
      (x slot) (y slot) (z slot)
  · exact Or.inl rfl

def CoeffZeroOne (T : ITensor) : Prop :=
  ∀ x y z, T.tensor x y z = 0 ∨ T.tensor x y z = 1

private theorem stageBrokenCopyZ25_coeffZeroOne {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) :
    CoeffZeroOne (stageBrokenCopyZ25 q p d b ε m r M B ω j) := by
  classical
  intro x y z
  unfold stageBrokenCopyZ25
  dsimp only [ITensor.tensor]
  exact prod_eq_zero_or_one _ (fun pos => conZ_eq_zero_or_one q w
    (coord .X (j.val pos).val) (coord .Y (j.val pos).val)
    (coord .Z (j.val pos).val) (x.val pos) (y.val pos) (z.val pos))

private theorem dependentSumZ_coeffZeroOne {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → ITensor) (h : ∀ i, CoeffZeroOne (T i)) :
    CoeffZeroOne (dependentSumZ T) := by
  intro x y z
  unfold dependentSumZ
  dsimp only [ITensor.tensor]
  split
  · split
    · exact h x.1 x.2 _ _
    · exact Or.inl rfl
  · exact Or.inl rfl

private theorem regionProductZ_coeffZeroOne (T : Fin 6 → ITensor)
    (h : ∀ r, CoeffZeroOne (T r)) : CoeffZeroOne (regionProductZ T) := by
  intro x y z
  unfold regionProductZ
  dsimp only [ITensor.tensor]
  exact prod_eq_zero_or_one _ (fun r => h r (x r) (y r) (z r))

theorem brokenFamilyTensorZ25_coeffZeroOne {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r)) :
    CoeffZeroOne (brokenFamilyTensorZ25 q p d b ε m M B ω) := by
  classical
  unfold brokenFamilyTensorZ25 goodBrokenFamilyZ25
  split
  · apply regionProductZ_coeffZeroOne
    intro r
    split
    · intro _ _ _
      exact Or.inr rfl
    · apply dependentSumZ_coeffZeroOne
      intro j
      exact stageBrokenCopyZ25_coeffZeroOne q p d b ε m r (M r) (B r) (ω r) j.val
  · intro x
    exact x.elim

set_option maxHeartbeats 1000000 in
-- Pointwise support of the packed target, factored out of the boundary proof above.
theorem packed_cw_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (htarget : (regionalInputZ q p d (b*m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0)
    (r : Fin 6) (pos : StageCandidateRaw.StagePos b m p d r) (c : Fin w) :
    cwZ q
      (sourceWordAt q p d b ε m M B ω .X x r pos c)
      (sourceWordAt q p d b ε m M B ω .Y y r pos c)
      (sourceWordAt q p d b ε m M B ω .Z z r pos c) ≠ 0 := by
  have hc := regionalInput_cw_ne q m p d hb ε
    (activeMap q m p d hb ε M B ω .X x)
    (activeMap q m p d hb ε M B ω .Y y)
    (activeMap q m p d hb ε M B ω .Z z) htarget r pos
    (joinedCoord pos.2.2 c)
  rw [show activeMap q m p d hb ε M B ω .X x =
        packPhysicalWords q m p d hb ε .X
          (fun r => sourceWordAt q p d b ε m M B ω .X x r) by rfl,
    show activeMap q m p d hb ε M B ω .Y y =
        packPhysicalWords q m p d hb ε .Y
          (fun r => sourceWordAt q p d b ε m M B ω .Y y r) by rfl,
    show activeMap q m p d hb ε M B ω .Z z =
        packPhysicalWords q m p d hb ε .Z
          (fun r => sourceWordAt q p d b ε m M B ω .Z z r) by rfl] at hc
  rw [packPhysicalWords_apply q m p d hb ε .X
      (fun r => sourceWordAt q p d b ε m M B ω .X x r) r pos c,
    packPhysicalWords_apply q m p d hb ε .Y
      (fun r => sourceWordAt q p d b ε m M B ω .Y y r) r pos c,
    packPhysicalWords_apply q m p d hb ε .Z
      (fun r => sourceWordAt q p d b ε m M B ω .Z z r) r pos c] at hc
  exact hc

theorem source_physical_labels_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (htarget : (regionalInputZ q p d (b*m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    let lX := sourceLabelAt q p d b ε m M B ω .X x r hn
    let lY := sourceLabelAt q p d b ε m M B ω .Y y r hn
    let lZ := sourceLabelAt q p d b ε m M B ω .Z z r hn
    lX = lY ∧ lX = lZ := by
  classical
  let lX := sourceLabelAt q p d b ε m M B ω .X x r hn
  let lY := sourceLabelAt q p d b ε m M B ω .Y y r hn
  let lZ := sourceLabelAt q p d b ε m M B ω .Z z r hn
  let label := fun W => physicalLabel lX.val lY.val lZ.val W
  have hrole := source_role_labels_eq q m p d hd hb ε M B ω hvalid x y z htarget r hn
  change label (d.perm r .Y) = label (d.perm r .X) ∧
    label (d.perm r .Z) = label (d.perm r .X) at hrole
  have hall : ∀ W, label W = label (d.perm r .X) := by
    intro W
    rcases (hd.roles.1 r).2 W with ⟨R, rfl⟩
    cases R with
    | X => rfl
    | Y => exact hrole.1
    | Z => exact hrole.2
  constructor
  · apply Subtype.ext
    change label .X = label .Y
    exact (hall .X).trans (hall .Y).symm
  · apply Subtype.ext
    change label .X = label .Z
    exact (hall .X).trans (hall .Z).symm


theorem sourceWordAt_X_eq {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    sourceWordAt q p d b ε m M B ω .X x r =
      fun pos c => (sourcePairAt q p d b ε m M B ω .X x r hn).2.val pos c := by
  simp [sourceWordAt, hn]

theorem sourceWordAt_Y_eq {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    sourceWordAt q p d b ε m M B ω .Y y r =
      fun pos c => (sourcePairAt q p d b ε m M B ω .Y y r hn).2.val pos c := by
  simp [sourceWordAt, hn]

theorem sourceWordAt_Z_eq {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    sourceWordAt q p d b ε m M B ω .Z z r =
      fun pos c => (sourcePairAt q p d b ε m M B ω .Z z r hn).2.val pos c := by
  simp [sourceWordAt, hn]

private theorem tensor_eq_tensor_transport {S T : ITensor} (h : S = T)
    (x : S.X) (y : S.Y) (z : S.Z) :
    S.tensor x y z = T.tensor
      (Eq.mp (congrArg (fun V : ITensor => V.X) h) x)
      (Eq.mp (congrArg (fun V : ITensor => V.Y) h) y)
      (Eq.mp (congrArg (fun V : ITensor => V.Z) h) z) := by
  cases h
  rfl


private theorem iteTensor_ne_of_false {P : Prop} [Decidable P] (T U : ITensor)
    (h : ¬ P) (x : (if P then T else U).X) (y : (if P then T else U).Y)
    (z : (if P then T else U).Z) (sx : U.X) (sy : U.Y) (sz : U.Z)
    (hx : Eq.mp (congrArg (fun V : ITensor => V.X) (if_neg h)) x = sx)
    (hy : Eq.mp (congrArg (fun V : ITensor => V.Y) (if_neg h)) y = sy)
    (hz : Eq.mp (congrArg (fun V : ITensor => V.Z) (if_neg h)) z = sz)
    (hs : U.tensor sx sy sz ≠ 0) :
    (if P then T else U).tensor x y z ≠ 0 := by
  rw [tensor_eq_tensor_transport (if_neg h), hx, hy, hz]
  exact hs

private theorem stageRegionFamily_tensor_eq_one_of_zero {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n = 0) :
    (stageRegionFamily q p d b ε m M B ω r).tensor
      (x r) (y r) (z r) = 1 := by
  let hT : stageRegionFamily q p d b ε m M B ω r = unitFamilyZ := by
    simp [stageRegionFamily, hn]
  rw [tensor_eq_tensor_transport hT]
  rfl

set_option maxHeartbeats 2000000 in
theorem source_ne_of_target_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (htarget : (regionalInputZ q p d (b * m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0) :
    (regionProductZ (stageRegionFamily q p d b ε m M B ω)).tensor
      x y z ≠ 0 := by
  classical
  unfold regionProductZ
  dsimp only [ITensor.tensor]
  rw [Finset.prod_ne_zero_iff]
  intro r _hr
  by_cases hn0 : (stagePopulationAt q p d b m r).n = 0
  · rw [stageRegionFamily_tensor_eq_one_of_zero q p d b ε m M B ω x y z r hn0]
    norm_num
  · let sx := sourcePairAt q p d b ε m M B ω .X x r hn0
    let sy := sourcePairAt q p d b ε m M B ω .Y y r hn0
    let sz := sourcePairAt q p d b ε m M B ω .Z z r hn0
    have hx : Eq.mp (congrArg (fun V : ITensor => V.X) (if_neg hn0)) (x r) = sx := by
      simp only [sx, sourcePairAt, id]
    have hy : Eq.mp (congrArg (fun V : ITensor => V.Y) (if_neg hn0)) (y r) = sy := by
      simp only [sy, sourcePairAt, id]
    have hz : Eq.mp (congrArg (fun V : ITensor => V.Z) (if_neg hn0)) (z r) = sz := by
      simp only [sz, sourcePairAt, id]
    have hlabels := source_physical_labels_eq q m p d hd hb ε M B ω hvalid
      x y z htarget r hn0
    have hlX : sourceLabelAt q p d b ε m M B ω .X x r hn0 = sx.1 := by
      change (sourcePairAt q p d b ε m M B ω .X x r hn0).1 = sx.1
      rfl
    have hlY : sourceLabelAt q p d b ε m M B ω .Y y r hn0 = sy.1 := by
      change (sourcePairAt q p d b ε m M B ω .Y y r hn0).1 = sy.1
      rfl
    have hlZ : sourceLabelAt q p d b ε m M B ω .Z z r hn0 = sz.1 := by
      change (sourcePairAt q p d b ε m M B ω .Z z r hn0).1 = sz.1
      rfl
    rw [hlX, hlY, hlZ] at hlabels
    rcases hsx : sx with ⟨jx, px⟩
    rcases hsy : sy with ⟨jy, py⟩
    rcases hsz : sz with ⟨jz, pz⟩
    have hxy : jx = jy := by
      simpa [sx, sy, hsx, hsy, sourceLabelAt] using hlabels.1
    have hxz : jx = jz := by
      simpa [sx, sz, hsx, hsz, sourceLabelAt] using hlabels.2
    subst jy
    subst jz
    unfold stageRegionFamily
    apply iteTensor_ne_of_false _ _ hn0 _ _ _ sx sy sz hx hy hz
    simp only [hsx, hsy, hsz]
    unfold dependentSumZ
    dsimp only [ITensor.tensor]
    rw [dif_pos rfl, dif_pos rfl]
    unfold stageBrokenCopyZ25
    dsimp only [ITensor.tensor]
    rw [Finset.prod_ne_zero_iff]
    intro pos _hpos
    unfold conZ
    rw [ADVXXZ.zoP_apply]
    rw [if_pos ⟨px.property.1.1 pos, py.property.1.1 pos, pz.property.1.1 pos⟩]
    unfold tensorPower
    rw [Finset.prod_ne_zero_iff]
    intro c _hc
    have hcw := packed_cw_ne q m p d hb ε M B ω x y z htarget r pos c
    simp only [sourceWordAt, hn0, dite_false] at hcw
    change cwZ q (sx.2.val pos c) (sy.2.val pos c) (sz.2.val pos c) ≠ 0 at hcw
    rw [hsx, hsy, hsz] at hcw
    exact hcw

set_option maxHeartbeats 1000000 in
private theorem stagePopulationAt_n_ne_zero_of_pos {w s : ℕ} (q b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (pos : StageCandidateRaw.StagePos b m p d r) :
    (stagePopulationAt q p d b m r).n ≠ 0 := by
  intro hn
  have hc : Fintype.card (StageCandidateRaw.StagePos b m p d r) = 0 := by
    simpa [stagePopulationAt, StageCandidateRaw.StagePos,
      StageCandidateRaw.stageParentCount, StageCandidateRaw.stageAlphaCount] using hn
  have hE : IsEmpty (StageCandidateRaw.StagePos b m p d r) :=
    Fintype.card_eq_zero_iff.mp hc
  exact hE.false pos

set_option maxHeartbeats 1000000 in
private theorem source_cw_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (hsource : (regionProductZ
      (stageRegionFamily q p d b ε m M B ω)).tensor x y z ≠ 0)
    (r : Fin 6) (pos : StageCandidateRaw.StagePos b m p d r) (c : Fin w) :
    cwZ q
      (sourceWordAt q p d b ε m M B ω .X x r pos c)
      (sourceWordAt q p d b ε m M B ω .Y y r pos c)
      (sourceWordAt q p d b ε m M B ω .Z z r pos c) ≠ 0 := by
  classical
  have hr : (stageRegionFamily q p d b ε m M B ω r).tensor
      (x r) (y r) (z r) ≠ 0 := by
    unfold regionProductZ at hsource
    dsimp only [ITensor.tensor] at hsource
    rw [Finset.prod_ne_zero_iff] at hsource
    exact hsource r (Finset.mem_univ r)
  have hn := stagePopulationAt_n_ne_zero_of_pos q b m p d r pos
  let sx := sourcePairAt q p d b ε m M B ω .X x r hn
  let sy := sourcePairAt q p d b ε m M B ω .Y y r hn
  let sz := sourcePairAt q p d b ε m M B ω .Z z r hn
  have hx : Eq.mp (congrArg (fun V : ITensor => V.X) (if_neg hn)) (x r) = sx := by
    simp only [sx, sourcePairAt, id]
  have hy : Eq.mp (congrArg (fun V : ITensor => V.Y) (if_neg hn)) (y r) = sy := by
    simp only [sy, sourcePairAt, id]
  have hz : Eq.mp (congrArg (fun V : ITensor => V.Z) (if_neg hn)) (z r) = sz := by
    simp only [sz, sourcePairAt, id]
  rcases sx with ⟨jx, px⟩
  rcases sy with ⟨jy, py⟩
  rcases sz with ⟨jz, pz⟩
  have hpairX : sourcePairAt q p d b ε m M B ω .X x r hn = ⟨jx, px⟩ := by
    simpa only [sourcePairAt] using hx
  have hpairY : sourcePairAt q p d b ε m M B ω .Y y r hn = ⟨jy, py⟩ := by
    simpa only [sourcePairAt] using hy
  have hpairZ : sourcePairAt q p d b ε m M B ω .Z z r hn = ⟨jz, pz⟩ := by
    simpa only [sourcePairAt] using hz
  unfold stageRegionFamily at hr
  rw [tensor_eq_tensor_transport (if_neg hn), hx, hy, hz] at hr
  unfold dependentSumZ at hr
  dsimp only [ITensor.tensor] at hr
  split at hr
  next hxy =>
    split at hr
    next hxz =>
      subst jy
      subst jz
      have hr' : (stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) jx.val).tensor
          px py pz ≠ 0 := by
        simpa only using hr
      unfold stageBrokenCopyZ25 at hr'
      dsimp only [ITensor.tensor] at hr'
      rw [Finset.prod_ne_zero_iff] at hr'
      have hp := hr' pos (Finset.mem_univ pos)
      unfold conZ at hp
      rw [ADVXXZ.zoP_apply] at hp
      split at hp
      next _ =>
        unfold tensorPower at hp
        rw [Finset.prod_ne_zero_iff] at hp
        have hcw := hp c (Finset.mem_univ c)
        rw [sourceWordAt_X_eq q p d b ε m M B ω x r hn,
          sourceWordAt_Y_eq q p d b ε m M B ω y r hn,
          sourceWordAt_Z_eq q p d b ε m M B ω z r hn]
        have hwX :
            (sourcePairAt q p d b ε m M B ω .X x r hn).2.val pos c =
              px.val pos c := by
          simpa only using congrArg (fun v => v.2.val pos c) hpairX
        have hwY :
            (sourcePairAt q p d b ε m M B ω .Y y r hn).2.val pos c =
              py.val pos c := by
          simpa only using congrArg (fun v => v.2.val pos c) hpairY
        have hwZ :
            (sourcePairAt q p d b ε m M B ω .Z z r hn).2.val pos c =
              pz.val pos c := by
          simpa only using congrArg (fun v => v.2.val pos c) hpairZ
        dsimp only
        rw [hwX, hwY, hwZ]
        exact hcw
      next hbad => exact (hp rfl).elim
    next _ => exact (hr rfl).elim
  next hne => exact (hr rfl).elim

set_option maxHeartbeats 1000000 in
private theorem packed_parent_chunk_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    chunkOf (fun c => regionalLegValue q m p d ε W
      (activeMap q m p d hb ε M B ω W x)
      (Fintype.equivFin (Fin s × Fin 6) (t, r))
      (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
        stageParentCount_eq_regionalCount p d b m hb t r) i) c) =
      Parent25.paired
        (stagePhysicalPart q p d b m r W
          (sourceWordAt q p d b ε m M B ω W x r)) t i := by
  classical
  funext c
  unfold Parent25.paired stagePhysicalPart chunkOf
  by_cases hc : c.val < w
  · simp only [hc, dite_true]
    let c' : Fin w := ⟨c.val, hc⟩
    have hcoord : c = joinedCoord (0 : Fin 2) c' := by
      apply Fin.ext
      change c.val = 0 * w + c.val
      omega
    have happ := packPhysicalWords_apply q m p d hb ε W
      (fun r => sourceWordAt q p d b ε m M B ω W x r)
      r ⟨t, (i, (0 : Fin 2))⟩ c'
    have hleft := congrArg (fun k : Fin (w + w) =>
      regionalLegValue q m p d ε W
        (activeMap q m p d hb ε M B ω W x)
        (Fintype.equivFin (Fin s × Fin 6) (t, r))
        (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
          stageParentCount_eq_regionalCount p d b m hb t r) i) k) hcoord
    exact congrArg CW90.lvl7 (hleft.trans (by
      simpa [activeMap] using happ))
  · simp only [hc, dite_false]
    let c' : Fin w := ⟨c.val - w, by omega⟩
    have hcoord : c = joinedCoord (1 : Fin 2) c' := by
      apply Fin.ext
      change c.val = 1 * w + (c.val - w)
      omega
    have happ := packPhysicalWords_apply q m p d hb ε W
      (fun r => sourceWordAt q p d b ε m M B ω W x r)
      r ⟨t, (i, (1 : Fin 2))⟩ c'
    have hleft := congrArg (fun k : Fin (w + w) =>
      regionalLegValue q m p d ε W
        (activeMap q m p d hb ε M B ω W x)
        (Fintype.equivFin (Fin s × Fin 6) (t, r))
        (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
          stageParentCount_eq_regionalCount p d b m hb t r) i) k) hcoord
    exact congrArg CW90.lvl7 (hleft.trans (by
      simpa [activeMap] using happ))

private theorem source_input_keep {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (r : Fin 6) (hn : (stagePopulationAt q p d b m r).n ≠ 0) :
    Parent25.inputPartKeep p d b m ε r W
      (stagePhysicalPart q p d b m r W
        (sourceWordAt q p d b ε m M B ω W x r)) := by
  have hk := source_part_keep q p d b ε m M B ω W x r hn
  unfold stagePartKeepAt25 at hk
  exact hk.1

private theorem approxConsistent_fin_cast {α : Type} [Fintype α] [DecidableEq α]
    {n n' : ℕ} (h : n = n') (ε : ℚ) (P : RatDist α) (f : Fin n → α)
    (hf : ApproxConsistent ε P f) :
    ApproxConsistent ε P (fun i : Fin n' => f (Fin.cast h.symm i)) := by
  subst n'
  simpa using hf

set_option maxHeartbeats 2000000 in
private theorem packed_input_properties {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (t : Fin s) (r : Fin 6) :
    let n := (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat
    let v : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
      regionalLegValue q m p d ε W
        (activeMap q m p d hb ε M B ω W x)
        (Fintype.equivFin (Fin s × Fin 6) (t, r))
        (Fin.cast (by unfold n; simp only [Equiv.symm_apply_apply]) i) c
    n = 0 ∨
      (ApproxConsistent ε (d.betaRegion W t r) (chunkSeq v) ∧
       (∀ i, (d.betaRegion W t r).num (chunkOf (v i)) ≠ 0) ∧
       ∀ i, levOf (v i) = match W with
         | .X => p.i t | .Y => p.j t | .Z => p.k t) := by
  classical
  let n := (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat
  let v : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
    regionalLegValue q m p d ε W
      (activeMap q m p d hb ε M B ω W x)
      (Fintype.equivFin (Fin s × Fin 6) (t, r))
      (Fin.cast (by unfold n; simp only [Equiv.symm_apply_apply]) i) c
  let hcount := stageParentCount_eq_regionalCount p d b m hb t r
  change n = 0 ∨ _
  by_cases hn : StageCandidateRaw.stageParentCount b m p d r t = 0
  · left
    unfold n
    rw [← hcount]
    exact hn
  · right
    let i0 : Fin (StageCandidateRaw.stageParentCount b m p d r t) :=
      ⟨0, Nat.pos_of_ne_zero hn⟩
    have hpop := stagePopulationAt_n_ne_zero_of_pos q b m p d r
      (⟨t, (i0, (0 : Fin 2))⟩ : StageCandidateRaw.StagePos b m p d r)
    have hkeep := source_input_keep q p d b ε m M B ω W x r hpop
    have ht := hkeep t
    have hparent : Parent25.parentCount p d b m r t ≠ 0 := by
      change StageCandidateRaw.stageParentCount b m p d r t ≠ 0
      exact hn
    have ht' := ht.resolve_left hparent
    let f := fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      Parent25.paired
        (stagePhysicalPart q p d b m r W
          (sourceWordAt q p d b ε m M B ω W x r)) t i
    have hchunk : ∀ i : Fin n, chunkOf (v i) = f (Fin.cast hcount.symm i) := by
      intro i
      have hc := packed_parent_chunk_eq q m p d hb ε M B ω W x r t
        (Fin.cast hcount.symm i)
      simpa [v, f] using hc
    have hseq : chunkSeq v = fun i : Fin n => f (Fin.cast hcount.symm i) := by
      funext i
      exact hchunk i
    constructor
    · rw [hseq]
      exact approxConsistent_fin_cast hcount ε (d.betaRegion W t r) f ht'.1
    constructor
    · intro i
      rw [hchunk i]
      exact ht'.2.1 (Fin.cast hcount.symm i)
    · intro i
      change chunkLvl (chunkOf (v i)) = _
      rw [hchunk i]
      cases W <;> simpa [f] using ht'.2.2 (Fin.cast hcount.symm i)

set_option maxHeartbeats 1000000 in
private theorem packed_cw_ne_of_source_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (hsource : (regionProductZ
      (stageRegionFamily q p d b ε m M B ω)).tensor x y z ≠ 0)
    (t : Fin s) (r : Fin 6)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t))
    (h : Fin 2) (c : Fin w) :
    let slot := Fintype.equivFin (Fin s × Fin 6) (t, r)
    let ii := Fin.cast (by unfold slot; simpa only [Equiv.symm_apply_apply] using
      stageParentCount_eq_regionalCount p d b m hb t r) i
    cwZ q
      (regionalLegValue q m p d ε .X
        (activeMap q m p d hb ε M B ω .X x) slot ii
        (joinedCoord h c))
      (regionalLegValue q m p d ε .Y
        (activeMap q m p d hb ε M B ω .Y y) slot ii
        (joinedCoord h c))
      (regionalLegValue q m p d ε .Z
        (activeMap q m p d hb ε M B ω .Z z) slot ii
        (joinedCoord h c)) ≠ 0 := by
  have hs := source_cw_ne q m p d ε M B ω x y z hsource r
    (⟨t, (i, h)⟩ : StageCandidateRaw.StagePos b m p d r) c
  dsimp only
  have hx : regionalLegValue q m p d ε .X
      (activeMap q m p d hb ε M B ω .X x)
      (Fintype.equivFin (Fin s × Fin 6) (t, r))
      (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
        stageParentCount_eq_regionalCount p d b m hb t r) i)
      (joinedCoord h c) =
        sourceWordAt q p d b ε m M B ω .X x r ⟨t, (i, h)⟩ c := by
    exact packPhysicalWords_apply q m p d hb ε .X
      (fun r => sourceWordAt q p d b ε m M B ω .X x r) r
      ⟨t, (i, h)⟩ c
  have hy : regionalLegValue q m p d ε .Y
      (activeMap q m p d hb ε M B ω .Y y)
      (Fintype.equivFin (Fin s × Fin 6) (t, r))
      (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
        stageParentCount_eq_regionalCount p d b m hb t r) i)
      (joinedCoord h c) =
        sourceWordAt q p d b ε m M B ω .Y y r ⟨t, (i, h)⟩ c := by
    exact packPhysicalWords_apply q m p d hb ε .Y
      (fun r => sourceWordAt q p d b ε m M B ω .Y y r) r
      ⟨t, (i, h)⟩ c
  have hz : regionalLegValue q m p d ε .Z
      (activeMap q m p d hb ε M B ω .Z z)
      (Fintype.equivFin (Fin s × Fin 6) (t, r))
      (Fin.cast (by simpa only [Equiv.symm_apply_apply] using
        stageParentCount_eq_regionalCount p d b m hb t r) i)
      (joinedCoord h c) =
        sourceWordAt q p d b ε m M B ω .Z z r ⟨t, (i, h)⟩ c := by
    exact packPhysicalWords_apply q m p d hb ε .Z
      (fun r => sourceWordAt q p d b ε m M B ω .Z z r) r
      ⟨t, (i, h)⟩ c
  rw [hx, hy, hz]
  exact hs

set_option maxHeartbeats 1000000 in
private theorem packed_support {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (W : Side)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).leg W)
    (slot : Fin (Fintype.card (Fin s × Fin 6)))
    (i : Fin ((((b * m : ℕ) : ℚ) *
      (p.baseN ((Fintype.equivFin (Fin s × Fin 6)).symm slot).1 : ℚ) *
      (d.A ((Fintype.equivFin (Fin s × Fin 6)).symm slot).1).prob
        ((Fintype.equivFin (Fin s × Fin 6)).symm slot).2).floor.toNat)) :
    (d.betaRegion W ((Fintype.equivFin (Fin s × Fin 6)).symm slot).1
      ((Fintype.equivFin (Fin s × Fin 6)).symm slot).2).num
      (chunkOf (fun c => regionalLegValue q m p d ε W
        (activeMap q m p d hb ε M B ω W x) slot i c)) ≠ 0 := by
  classical
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  rcases htr : e slot with ⟨t, r⟩
  have hslot := congrArg (Fintype.equivFin (Fin s × Fin 6)) htr
  simp only [e, Equiv.apply_symm_apply] at hslot
  subst slot
  have hp := packed_input_properties q m p d hb ε M B ω W x t r
  rcases hp with hzero | hp
  · have hz :
        (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat = 0 := hzero
    have hi :
        (((b * m : ℕ) : ℚ) *
          (p.baseN ((Fintype.equivFin (Fin s × Fin 6)).symm
            (Fintype.equivFin (Fin s × Fin 6) (t, r))).1 : ℚ) *
          (d.A ((Fintype.equivFin (Fin s × Fin 6)).symm
            (Fintype.equivFin (Fin s × Fin 6) (t, r))).1).prob
            ((Fintype.equivFin (Fin s × Fin 6)).symm
              (Fintype.equivFin (Fin s × Fin 6) (t, r))).2).floor.toNat = 0 := by
      simpa only [Equiv.symm_apply_apply] using hz
    have hpos : 0 <
        (((b * m : ℕ) : ℚ) *
          (p.baseN ((Fintype.equivFin (Fin s × Fin 6)).symm
            (Fintype.equivFin (Fin s × Fin 6) (t, r))).1 : ℚ) *
          (d.A ((Fintype.equivFin (Fin s × Fin 6)).symm
            (Fintype.equivFin (Fin s × Fin 6) (t, r))).1).prob
            ((Fintype.equivFin (Fin s × Fin 6)).symm
              (Fintype.equivFin (Fin s × Fin 6) (t, r))).2).floor.toNat :=
      Nat.zero_lt_of_lt i.isLt
    exact (Nat.ne_of_gt hpos hi).elim
  · let i' : Fin ((((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) *
        (d.A t).prob r).floor.toNat) :=
      Fin.cast (by simpa only [Equiv.symm_apply_apply]) i
    have hs := hp.2.1 i'
    dsimp only at hs
    have hidx : Fin.cast (by simpa only [Equiv.symm_apply_apply]) i' = i :=
      Fin.ext rfl
    rw [hidx] at hs
    simpa only [Prod.fst, Prod.snd, Equiv.symm_apply_apply,
      regionalLegValue] using hs

set_option maxHeartbeats 2000000 in
private theorem packed_iface_term_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (hsource : (regionProductZ
      (stageRegionFamily q p d b ε m M B ω)).tensor x y z ≠ 0)
    (t : Fin s) (r : Fin 6) :
    let n := (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat
    let slot := Fintype.equivFin (Fin s × Fin 6) (t, r)
    let vX : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
      regionalLegValue q m p d ε .X
        (activeMap q m p d hb ε M B ω .X x) slot
        (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
    let vY : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
      regionalLegValue q m p d ε .Y
        (activeMap q m p d hb ε M B ω .Y y) slot
        (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
    let vZ : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
      regionalLegValue q m p d ε .Z
        (activeMap q m p d hb ε M B ω .Z z) slot
        (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
    ifaceTermZ q (w + w) (p.i t) (p.j t) (p.k t) n
      (d.betaRegion .X t r) (d.betaRegion .Y t r) (d.betaRegion .Z t r) ε
      vX vY vZ ≠ 0 := by
  classical
  let n := (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat
  let slot := Fintype.equivFin (Fin s × Fin 6) (t, r)
  let vX : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
    regionalLegValue q m p d ε .X
      (activeMap q m p d hb ε M B ω .X x) slot
      (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
  let vY : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
    regionalLegValue q m p d ε .Y
      (activeMap q m p d hb ε M B ω .Y y) slot
      (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
  let vZ : Fin n → Fin (w + w) → CW90.Idx7 q := fun i c =>
    regionalLegValue q m p d ε .Z
      (activeMap q m p d hb ε M B ω .Z z) slot
      (Fin.cast (by unfold n slot; simp only [Equiv.symm_apply_apply]) i) c
  have hpX := packed_input_properties q m p d hb ε M B ω .X x t r
  have hpY := packed_input_properties q m p d hb ε M B ω .Y y t r
  have hpZ := packed_input_properties q m p d hb ε M B ω .Z z t r
  change ifaceTermZ q (w + w) (p.i t) (p.j t) (p.k t) n
    (d.betaRegion .X t r) (d.betaRegion .Y t r) (d.betaRegion .Z t r) ε
    vX vY vZ ≠ 0
  by_cases hn : n = 0
  · unfold ifaceTermZ
    rw [if_pos hn]
    norm_num
  · rcases hpX with hzero | hpX
    · exact (hn hzero).elim
    rcases hpY with hzero | hpY
    · exact (hn hzero).elim
    rcases hpZ with hzero | hpZ
    · exact (hn hzero).elim
    unfold ifaceTermZ
    rw [if_neg hn, if_pos ⟨hpX.1, hpY.1, hpZ.1⟩]
    unfold tensorPower
    rw [Finset.prod_ne_zero_iff]
    intro i _hi
    unfold conZ
    rw [ADVXXZ.zoP_apply]
    rw [if_pos ⟨hpX.2.2 i, hpY.2.2 i, hpZ.2.2 i⟩]
    unfold tensorPower
    rw [Finset.prod_ne_zero_iff]
    intro c _hc
    let hcount := stageParentCount_eq_regionalCount p d b m hb t r
    let i' : Fin (StageCandidateRaw.stageParentCount b m p d r t) :=
      Fin.cast hcount.symm i
    by_cases hc : c.val < w
    · let c' : Fin w := ⟨c.val, hc⟩
      have hcoord : c = joinedCoord (0 : Fin 2) c' := by
        apply Fin.ext
        change c.val = 0 * w + c.val
        omega
      rw [hcoord]
      have hs := packed_cw_ne_of_source_ne q m p d hb ε M B ω x y z hsource
        t r i' (0 : Fin 2) c'
      simpa [vX, vY, vZ, slot, i', hcount] using hs
    · let c' : Fin w := ⟨c.val - w, by omega⟩
      have hcoord : c = joinedCoord (1 : Fin 2) c' := by
        apply Fin.ext
        change c.val = 1 * w + (c.val - w)
        omega
      rw [hcoord]
      have hs := packed_cw_ne_of_source_ne q m p d hb ε M B ω x y z hsource
        t r i' (1 : Fin 2) c'
      simpa [vX, vY, vZ, slot, i', hcount] using hs

private theorem ifaceTermZ_fin_cast {q w i j k n n' : ℕ}
    (h : n = n') {bX bY bZ : SplitDist w} {ε : ℚ}
    {x : Fin n → Fin w → CW90.Idx7 q}
    {y : Fin n → Fin w → CW90.Idx7 q}
    {z : Fin n → Fin w → CW90.Idx7 q} :
    ifaceTermZ q w i j k n bX bY bZ ε x y z =
      ifaceTermZ q w i j k n' bX bY bZ ε
        (fun a => x (Fin.cast h.symm a))
        (fun a => y (Fin.cast h.symm a))
        (fun a => z (Fin.cast h.symm a)) := by
  subst n'
  rfl

set_option maxHeartbeats 2000000 in
theorem target_ne_of_source_ne {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z)
    (hsource : (regionProductZ
      (stageRegionFamily q p d b ε m M B ω)).tensor x y z ≠ 0) :
    (regionalInputZ q p d (b * m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) ≠ 0 := by
  classical
  let e := (Fintype.equivFin (Fin s × Fin 6)).symm
  unfold regionalInputZ supportedIfaceZ
  dsimp only [ITensor.tensor]
  rw [ADVXXZ.zoP_apply]
  rw [if_pos]
  · unfold ifaceZ
    rw [Finset.prod_ne_zero_iff]
    intro slot _hslot
    rcases htr : e slot with ⟨t, r⟩
    have hslot := congrArg (Fintype.equivFin (Fin s × Fin 6)) htr
    simp only [e, Equiv.apply_symm_apply] at hslot
    subst slot
    have ht := packed_iface_term_ne q m p d hb ε M B ω x y z hsource t r
    dsimp only at ht
    have hcan :
        (((b * m : ℕ) : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r).floor.toNat =
          (((b * m : ℕ) : ℚ) *
            (p.baseN ((Fintype.equivFin (Fin s × Fin 6)).symm
              (Fintype.equivFin (Fin s × Fin 6) (t, r))).1 : ℚ) *
            (d.A ((Fintype.equivFin (Fin s × Fin 6)).symm
              (Fintype.equivFin (Fin s × Fin 6) (t, r))).1).prob
              ((Fintype.equivFin (Fin s × Fin 6)).symm
                (Fintype.equivFin (Fin s × Fin 6) (t, r))).2).floor.toNat := by
      simp only [Equiv.symm_apply_apply]
    rw [ifaceTermZ_fin_cast (h := hcan)] at ht
    simpa [e, Equiv.symm_apply_apply, regionalLegValue] using ht
  · constructor
    · intro slot i
      have hs := packed_support q m p d hb ε M B ω .X x slot i
      simpa only [e, regionalLegValue] using hs
    constructor
    · intro slot i
      have hs := packed_support q m p d hb ε M B ω .Y y slot i
      simpa only [e, regionalLegValue] using hs
    · intro slot i
      have hs := packed_support q m p d hb ε M B ω .Z z slot i
      simpa only [e, regionalLegValue] using hs

private theorem brokenFamily_eq_embedding_region {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B) :
    brokenFamilyTensorZ25 q p d b ε m M B ω =
      regionProductZ (stageRegionFamily q p d b ε m M B ω) := by
  classical
  unfold brokenFamilyTensorZ25 goodBrokenFamilyZ25
  rw [if_pos hvalid]
  congr 1

private theorem brokenFamily_eq_empty_of_invalid {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ¬ ValidStageHashes p d b m M B) :
    brokenFamilyTensorZ25 q p d b ε m M B ω = emptyFamilyZ := by
  classical
  unfold brokenFamilyTensorZ25 goodBrokenFamilyZ25
  rw [if_neg hvalid]

set_option maxHeartbeats 2000000 in
theorem active_coefficient_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (hvalid : ValidStageHashes p d b m M B)
    (x : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).X)
    (y : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Y)
    (z : (regionProductZ (stageRegionFamily q p d b ε m M B ω)).Z) :
    (regionalInputZ q p d (b * m) ε).tensor
      (activeMap q m p d hb ε M B ω .X x)
      (activeMap q m p d hb ε M B ω .Y y)
      (activeMap q m p d hb ε M B ω .Z z) =
      (regionProductZ (stageRegionFamily q p d b ε m M B ω)).tensor x y z := by
  have ht01 := regionalInputZ_eq_zero_or_one q (b * m) p d ε
    (activeMap q m p d hb ε M B ω .X x)
    (activeMap q m p d hb ε M B ω .Y y)
    (activeMap q m p d hb ε M B ω .Z z)
  have hs01 : CoeffZeroOne
      (regionProductZ (stageRegionFamily q p d b ε m M B ω)) := by
    have hs := brokenFamilyTensorZ25_coeffZeroOne q p d b ε m M B ω
    rw [brokenFamily_eq_embedding_region q p d b ε m M B ω hvalid] at hs
    exact hs
  rcases ht01 with ht0 | ht1
  · have hs0 :
        (regionProductZ (stageRegionFamily q p d b ε m M B ω)).tensor
          x y z = 0 := by
      by_contra hsne
      exact target_ne_of_source_ne q m p d hb ε M B ω x y z hsne ht0
    rw [ht0, hs0]
  · have htne : (regionalInputZ q p d (b * m) ε).tensor
        (activeMap q m p d hb ε M B ω .X x)
        (activeMap q m p d hb ε M B ω .Y y)
        (activeMap q m p d hb ε M B ω .Z z) ≠ 0 := by
      rw [ht1]
      norm_num
    have hsne := source_ne_of_target_ne q m p d hd hb ε M B ω hvalid x y z htne
    rcases hs01 x y z with hs0 | hs1
    · exact (hsne hs0).elim
    · rw [ht1, hs1]

theorem active_embeddings {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r)) :
  let T := regionalInputZ q p d (b*m) ε
  let U := brokenFamilyTensorZ25 q p d b ε m M B ω
  ∃ (eX : U.X → T.X) (eY : U.Y → T.Y) (eZ : U.Z → T.Z),
    Function.Injective eX ∧ Function.Injective eY ∧ Function.Injective eZ ∧
    ∀ x y z, T.tensor (eX x) (eY y) (eZ z) = U.tensor x y z := by
  classical
  dsimp only
  by_cases hvalid : ValidStageHashes p d b m M B
  · rw [brokenFamily_eq_embedding_region q p d b ε m M B ω hvalid]
    exact ⟨activeMap q m p d hb ε M B ω .X,
      activeMap q m p d hb ε M B ω .Y,
      activeMap q m p d hb ε M B ω .Z,
      activeMap_injective q m p d hd hb ε M B ω .X,
      activeMap_injective q m p d hd hb ε M B ω .Y,
      activeMap_injective q m p d hd hb ε M B ω .Z,
      active_coefficient_eq q m p d hd hb ε M B ω hvalid⟩
  · rw [brokenFamily_eq_empty_of_invalid q p d b ε m M B ω hvalid]
    exact ⟨fun x => x.elim, fun y => y.elim, fun z => z.elim,
      fun x => x.elim, fun y => y.elim, fun z => z.elim, fun x => x.elim⟩

end
end CExact36EmbeddingAux

-- Generic version for the empirical-grid consumer; P/constituent.tex:340-345.
theorem active_embeddings_integral36 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (rochd : ConstituentAdmissibleAt d b) (rochb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r)) :
  let T := regionalInputZ q p d (b*m) ε
  let U := brokenFamilyTensorZ25 q p d b ε m M B ω
  ∃ (eX : U.X → T.X) (eY : U.Y → T.Y) (eZ : U.Z → T.Z),
    Function.Injective eX ∧ Function.Injective eY ∧ Function.Injective eZ ∧
    ∀ x y z, T.tensor (eX x) (eY y) (eZ z) = U.tensor x y z :=
  CExact36EmbeddingAux.active_embeddings q m p d rochd rochb ε M B ω

#print axioms OmegaBound.ADVXXZGeneral.active_embeddings_integral36
end OmegaBound.ADVXXZGeneral
end
