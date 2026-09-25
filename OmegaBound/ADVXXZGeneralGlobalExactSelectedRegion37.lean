import OmegaBound.ADVXXZGeneralGlobalExactEnvelope37
import OmegaBound.ADVXXZGeneralGlobalOrderedDeletions
import OmegaBound.ADVXXZGeneralAmend25GlobalBridge

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable section

private theorem global_incidence_implies_coarseContains28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (W : Side) (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W)
    (hinc : (globalPopulation g n ξ r).incidence W j a) :
    globalCoarseContains g n ξ r W j a := by
  simpa only [globalCoarseContains] using hinc.1

private theorem globalCellCount_exact28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (W : Side) (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W)
    (hinc : (globalPopulation g n ξ r).incidence W j a)
    (u : Shape w) (σ : Chunk w) :
    globalCellCount g n ξ r W j a (fun v => v = u) σ = ξ.count W r u σ := by
  rw [globalCellCount]
  rw [← hinc.2 u σ]
  congr 1
  ext i
  simp

private theorem globalCellCount_grade28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (W : Side) (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W)
    (k : Fin (2*w+1)) (σ : Chunk w) :
    globalCellCount g n ξ r W j a (fun u => coord W u = k.val) σ =
      ∑ u : Shape w, if coord W u = k.val then
        globalCellCount g n ξ r W j a (fun v => v = u) σ else 0 := by
  classical
  simp only [globalCellCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ i, ∑ u : Shape w,
        if coord W u = k.val ∧ j.val i = u ∧ a i = σ then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hc : coord W (j.val i) = k.val
      · by_cases ha : a i = σ
        · have hfilter :
              (Finset.univ.filter fun u : Shape w =>
                coord W u = k.val ∧ j.val i = u ∧ a i = σ) = {j.val i} := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro hu
              exact hu.2.1.symm
            · intro hu
              subst u
              exact ⟨hc, rfl, ha⟩
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
            hfilter, Finset.card_singleton]
          rw [if_pos ⟨hc, ha⟩]
        · simp [ha]
      · have hfilter :
            (Finset.univ.filter fun u : Shape w =>
              coord W u = k.val ∧ j.val i = u ∧ a i = σ) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          intro hu
          apply hc
          rw [hu.2.1]
          exact hu.1
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
          hfilter, Finset.card_empty]
        rw [if_neg (fun h => hc h.1)]
    _ = ∑ u : Shape w, ∑ i,
        if coord W u = k.val ∧ j.val i = u ∧ a i = σ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro u _hu
      by_cases hc : coord W u = k.val
      · rw [if_pos hc]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        by_cases hj : j.val i = u <;>
          by_cases ha : a i = σ <;> simp [hc, hj, ha]
      · simp [hc]

private theorem global_incidence_implies_compatible28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (which : Fin 2) (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part
      (g.perm r (if which = 0 then .Y else .Z)))
    (hinc : (globalPopulation g n ξ r).incidence
      (g.perm r (if which = 0 then .Y else .Z)) j a) :
    globalCompatible g n ξ r which j a := by
  have hside :
      (if which = 0 then g.perm r .Y else g.perm r .Z) =
        g.perm r (if which = 0 then .Y else .Z) := by
    by_cases hw : which = 0 <;> simp [hw]
  unfold globalCompatible
  dsimp only
  rw [hside]
  constructor
  · intro u _hboundary σ
    exact globalCellCount_exact28 q n g ξ r _ j a hinc u σ
  · intro k σ
    rw [globalCellCount_grade28 (q := q)]
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases hc : coord (g.perm r (if which = 0 then .Y else .Z)) u = k.val
    · simp only [hc, if_pos]
      exact globalCellCount_exact28 q n g ξ r _ j a hinc u σ
    · simp [hc]

private theorem global_candidate_iff_keep28 {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (ξ : ExactGrid g (b*m)) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r)) :
    ∀ W : Side, ∀ x : (topZ q w (b*m)).leg W,
      globalCandidateWord q g b m ξ M B ω W x ↔
        globalFinalKeep q g b m ξ M B ω W x := by
  classical
  intro W x
  simp only [globalCandidateWord, globalFinalKeep]
  constructor
  · intro hcand r
    rcases hcand r with hn | ⟨j, v, hjS, rfl, hinc, hyUnique, hzUnique⟩
    · exact Or.inl hn
    · right
      simp only [globalPartKeep]
      have hcontains := global_incidence_implies_coarseContains28 q (b*m) g ξ r W j _ hinc
      have hjMatching : j ∈
          (selected (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
            (M r) (B r) (ω r)).filter
            (fun k => globalCoarseContains g (b*m) ξ r W k
              (globalPhysicalPart q g (b*m) ξ r W
                (globalRegionWord q g (b*m) ξ r W x))) :=
        Finset.mem_filter.mpr ⟨hjS, hcontains⟩
      refine ⟨⟨j, hjMatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _hW
        exact ⟨j, hjMatching, hinc⟩
      · intro hW
        subst W
        refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩⟩
        exact global_incidence_implies_compatible28 q (b*m) g ξ r 0 j _ hinc
      · intro hW
        subst W
        apply Finset.card_eq_one.mpr
        refine ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
        · refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
          exact global_incidence_implies_compatible28 q (b*m) g ξ r 0 j _ hinc
        · intro k hk
          have hk' := Finset.mem_filter.mp hk
          have hkm := Finset.mem_filter.mp hk'.1
          exact hyUnique rfl k hkm.1 hkm.2 hk'.2
      · intro hW
        subst W
        refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩, hinc⟩
        exact global_incidence_implies_compatible28 q (b*m) g ξ r 0 j _ hinc
      · intro hW
        subst W
        refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩⟩
        exact global_incidence_implies_compatible28 q (b*m) g ξ r 1 j _ hinc
      · intro hW
        subst W
        apply Finset.card_eq_one.mpr
        refine ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
        · refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
          exact global_incidence_implies_compatible28 q (b*m) g ξ r 1 j _ hinc
        · intro k hk
          have hk' := Finset.mem_filter.mp hk
          have hkm := Finset.mem_filter.mp hk'.1
          exact hzUnique rfl k hkm.1 hkm.2 hk'.2
      · intro hW
        subst W
        refine ⟨j, Finset.mem_filter.mpr ⟨hjMatching, ?_⟩, hinc⟩
        exact global_incidence_implies_compatible28 q (b*m) g ξ r 1 j _ hinc
  · intro hkeep r
    rcases hkeep r with hn | hk
    · exact Or.inl hn
    · right
      simp only [globalPartKeep] at hk
      rcases hk with ⟨_hhash, hX, _hYC, hYU, hYF, _hZC, hZU, hZF⟩
      have hchosen : ∃ j ∈
          (selected (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
            (M r) (B r) (ω r)).filter
            (fun k => globalCoarseContains g (b*m) ξ r W k
              (globalPhysicalPart q g (b*m) ξ r W
                (globalRegionWord q g (b*m) ξ r W x))),
          (globalPopulation g (b*m) ξ r).incidence W j
            (globalPhysicalPart q g (b*m) ξ r W
              (globalRegionWord q g (b*m) ξ r W x)) := by
        rcases (hg.roles.1 r).2 W with ⟨V, hV⟩
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
      refine ⟨j, globalRegionWord q g (b*m) ξ r W x, hjS, rfl, hinc, ?_, ?_⟩
      · intro hW
        subst W
        intro k hkS hkContains hkCompatible
        have hkC : k ∈
            ((selected
              (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
                (M r) (B r) (ω r)).filter
              (fun l => globalCoarseContains g (b*m) ξ r (g.perm r .Y) l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Y)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Y) x)))).filter
              (fun l => globalCompatible g (b*m) ξ r 0 l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Y)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Y) x))) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hkS, hkContains⟩, hkCompatible⟩
        have hjC : j ∈
            ((selected
              (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
                (M r) (B r) (ω r)).filter
              (fun l => globalCoarseContains g (b*m) ξ r (g.perm r .Y) l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Y)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Y) x)))).filter
              (fun l => globalCompatible g (b*m) ξ r 0 l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Y)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Y) x))) := by
          refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
          exact global_incidence_implies_compatible28 q (b*m) g ξ r 0 j _ hinc
        rcases Finset.card_eq_one.mp (hYU rfl) with ⟨z, hz⟩
        rw [hz] at hkC hjC
        simp only [Finset.mem_singleton] at hkC hjC
        exact hkC.trans hjC.symm
      · intro hW
        subst W
        intro k hkS hkContains hkCompatible
        have hkC : k ∈
            ((selected
              (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
                (M r) (B r) (ω r)).filter
              (fun l => globalCoarseContains g (b*m) ξ r (g.perm r .Z) l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Z)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Z) x)))).filter
              (fun l => globalCompatible g (b*m) ξ r 1 l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Z)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Z) x))) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hkS, hkContains⟩, hkCompatible⟩
        have hjC : j ∈
            ((selected
              (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
                (M r) (B r) (ω r)).filter
              (fun l => globalCoarseContains g (b*m) ξ r (g.perm r .Z) l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Z)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Z) x)))).filter
              (fun l => globalCompatible g (b*m) ξ r 1 l
                (globalPhysicalPart q g (b*m) ξ r (g.perm r .Z)
                  (globalRegionWord q g (b*m) ξ r (g.perm r .Z) x))) := by
          refine Finset.mem_filter.mpr ⟨hjMatching, ?_⟩
          exact global_incidence_implies_compatible28 q (b*m) g ξ r 1 j _ hinc
        rcases Finset.card_eq_one.mp (hZU rfl) with ⟨z, hz⟩
        rw [hz] at hkC hjC
        simp only [Finset.mem_singleton] at hkC hjC
        exact hkC.trans hjC.symm

private theorem scaledGlobalCount_eq28 (b m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * a = (k : ℚ)) :
    (((b*m : ℕ) : ℚ) * a).floor.toNat = k*m := by
  have hq : (((b*m : ℕ) : ℚ) * a) = ((k*m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k*m : ℕ) : ℚ).floor) = (k*m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k*m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k*m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

private theorem globalPopulation_sum28 {w b m : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g (b*m)) (hb : GlobalIntegral g b) :
    ∑ r : Fin 6, (globalPopulation g (b*m) ξ r).n = b*m := by
  classical
  let k : Fin 6 → Shape w → ℕ := fun r u =>
    Classical.choose ((hb.2 r).2 u).1
  have hk : ∀ r u, (b : ℚ) * g.joint.prob (r, u) = (k r u : ℚ) :=
    fun r u => Classical.choose_spec ((hb.2 r).2 u).1
  have hcount : ∀ r u,
      (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = k r u * m :=
    fun r u => scaledGlobalCount_eq28 b m (k r u) (g.joint.prob (r, u)) (hk r u)
  have hksum : ∑ r : Fin 6, ∑ u : Shape w, k r u = b := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    calc
      ∑ r : Fin 6, ∑ u : Shape w, (k r u : ℚ) =
          ∑ r : Fin 6, ∑ u : Shape w, (b : ℚ) * g.joint.prob (r, u) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro u _hu
        exact (hk r u).symm
      _ = (b : ℚ) * ∑ ru : Fin 6 × Shape w, g.joint.prob ru := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum]
      _ = (b : ℚ) := by rw [g.joint.sum_prob, mul_one]
  change ∑ r : Fin 6, ∑ u : Shape w,
      (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = b*m
  simp_rw [hcount]
  simp_rw [← Finset.sum_mul]
  rw [hksum]

private noncomputable def globalBlockEquiv28 {w b m : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g (b*m)) (hb : GlobalIntegral g b) :
    ((r : Fin 6) × Fin (globalPopulation g (b*m) ξ r).n) ≃ Fin (b*m) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact globalPopulation_sum28 g ξ hb)

private noncomputable def globalRegionFamily28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (b m : ℕ) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (r : Fin 6) : ITensor := by
  classical
  exact if (globalPopulation g (b*m) ξ r).n = 0 then unitFamilyZ else
    dependentSumZ fun j : {j //
      j ∈ selected (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
        (M r) (B r) (ω r)} =>
      globalBrokenCopyZ q g (b*m) ξ r (M r) (B r) (ω r) j.val

private noncomputable def emptyGlobalWord28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n) (r : Fin 6)
    (_hn : (globalPopulation g n ξ r).n = 0) :
    GlobalPhysicalWord q g n ξ r :=
  fun _ _ => Sum.inl none

private noncomputable def globalSourcePairAt28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (b m : ℕ) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side)
    (x : (regionProductZ (globalRegionFamily28 q g b m ξ M B ω)).leg W)
    (r : Fin 6) (hn : (globalPopulation g (b*m) ξ r).n ≠ 0) :
    (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
      (M r) (B r) (ω r)}) ×
      (globalBrokenCopyZ q g (b*m) ξ r (M r) (B r) (ω r) j.val).leg W := by
  classical
  cases W with
  | X => simpa [regionProductZ, ITensor.leg, globalRegionFamily28, hn] using x r
  | Y => simpa [regionProductZ, ITensor.leg, globalRegionFamily28, hn] using x r
  | Z => simpa [regionProductZ, ITensor.leg, globalRegionFamily28, hn] using x r

private noncomputable def globalSourceWordAt28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (b m : ℕ) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side)
    (x : (regionProductZ (globalRegionFamily28 q g b m ξ M B ω)).leg W)
    (r : Fin 6) : GlobalPhysicalWord q g (b*m) ξ r := by
  classical
  by_cases hn : (globalPopulation g (b*m) ξ r).n = 0
  · exact emptyGlobalWord28 q g (b*m) ξ r hn
  · cases W <;> exact (globalSourcePairAt28 q g b m ξ M B ω _ x r hn).2.val

private noncomputable def globalSourceLabelAt28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (b m : ℕ) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side)
    (x : (regionProductZ (globalRegionFamily28 q g b m ξ M B ω)).leg W)
    (r : Fin 6) (hn : (globalPopulation g (b*m) ξ r).n ≠ 0) :
    {j // j ∈ selected
      (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
      (M r) (B r) (ω r)} := by
  classical
  exact (globalSourcePairAt28 q g b m ξ M B ω W x r hn).1

private theorem globalSourceProperties28 {w : ℕ} (q : ℕ)
    (g : GlobalSpec w) (b m : ℕ) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side)
    (x : (regionProductZ (globalRegionFamily28 q g b m ξ M B ω)).leg W)
    (r : Fin 6) (hn : (globalPopulation g (b*m) ξ r).n ≠ 0) :
    let j := globalSourceLabelAt28 q g b m ξ M B ω W x r hn
    j.val ∈ selected
        (rolePopulation (globalPopulation g (b*m) ξ r) (g.perm r))
        (M r) (B r) (ω r) ∧
      (globalPopulation g (b*m) ξ r).incidence W j.val
        (globalPhysicalPart q g (b*m) ξ r W
          (globalSourceWordAt28 q g b m ξ M B ω W x r)) ∧
      globalPartKeep g (b*m) ξ r (M r) (B r) (ω r) .zUseful W
        (globalPhysicalPart q g (b*m) ξ r W
          (globalSourceWordAt28 q g b m ξ M B ω W x r)) := by
  classical
  cases W <;>
    simpa [globalSourceLabelAt28, globalSourceWordAt28, hn] using
      (globalSourcePairAt28 q g b m ξ M B ω _ x r hn).2.property

private noncomputable def globalSourceMap28 {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hb : GlobalIntegral g b) (ξ : ExactGrid g (b*m))
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g (b*m) ξ r) (M r))
    (W : Side) :
    (regionProductZ (globalRegionFamily28 q g b m ξ M B ω)).leg W →
      (topZ q w (b*m)).leg W := by
  intro x
  cases W with
  | X =>
      exact fun i c =>
        let ri := (globalBlockEquiv28 g ξ hb).symm i
        globalSourceWordAt28 q g b m ξ M B ω .X x ri.1 ri.2 c
  | Y =>
      exact fun i c =>
        let ri := (globalBlockEquiv28 g ξ hb).symm i
        globalSourceWordAt28 q g b m ξ M B ω .Y x ri.1 ri.2 c
  | Z =>
      exact fun i c =>
        let ri := (globalBlockEquiv28 g ξ hb).symm i
        globalSourceWordAt28 q g b m ξ M B ω .Z x ri.1 ri.2 c

private def localHashZero28 {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨0, by omega⟩

private def localHashOne28 {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) : ZMod M :=
  ω ⟨1, by omega⟩

private def localHashWeight28 {P : RawPopulation} {M : ℕ}
    (ω : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  ω ⟨i.val + 2, by omega⟩

private def localHashX28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero28 ω + ∑ i, (P.coarse j .X i).val * localHashWeight28 ω i

private def localHashY28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero28 ω + localHashOne28 ω +
    ∑ i, (P.coarse j .Y i).val * localHashWeight28 ω i

private noncomputable def localHashZ28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label) : ZMod M :=
  localHashZero28 ω + Ring.inverse 2 *
    (localHashOne28 ω +
      ∑ i, (P.grade - (P.coarse j .Z i).val) * localHashWeight28 ω i)

private noncomputable def localSurvives28 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun j =>
    localHashX28 P M ω j = localHashY28 P M ω j ∧
      localHashY28 P M ω j = localHashZ28 P M ω j ∧
      localHashX28 P M ω j ∈ B

private noncomputable def localSelected28 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) : Finset P.Label := by
  classical
  exact (localSurvives28 P M B ω).filter fun j =>
    j ∈ P.target ∧ ∀ k ∈ localSurvives28 P M B ω,
      P.coarse k .X = P.coarse j .X → k = j

private theorem selected_eq_local28 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) :
    selected P M B ω = localSelected28 P M B ω := by
  with_unfolding_all rfl

private theorem selected_hash_data28 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (j : P.Label)
    (hj : j ∈ selected P M B ω) :
    localHashX28 P M ω j = localHashY28 P M ω j ∧
      localHashY28 P M ω j = localHashZ28 P M ω j ∧
      localHashX28 P M ω j ∈ B := by
  classical
  rw [selected_eq_local28] at hj
  unfold localSelected28 at hj
  have hs := (Finset.mem_filter.mp hj).1
  simpa [localSurvives28] using hs

private theorem inverse_two_mul28 (M : ℕ) (hprime : Nat.Prime M) (hodd : 2 < M) :
    Ring.inverse (2 : ZMod M) * 2 = 1 := by
  apply Ring.inverse_mul_cancel
  have hnot : ¬ M ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) hodd
  have hcop : Nat.Coprime 2 M := by
    rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd]
    exact hnot
  exact (ZMod.unitOfCoprime 2 hcop).isUnit

private theorem local_hash_ap28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j : P.Label)
    (htight : ∀ i, (P.coarse j .X i).val + (P.coarse j .Y i).val +
      (P.coarse j .Z i).val = P.grade)
    (hprime : Nat.Prime M) (hodd : 2 < M) :
    localHashX28 P M ω j + localHashY28 P M ω j =
      2 * localHashZ28 P M ω j := by
  have hcomp :
      (∑ i, (P.grade - (P.coarse j .Z i).val) * localHashWeight28 ω i) =
        (∑ i, (P.coarse j .X i).val * localHashWeight28 ω i) +
          ∑ i, (P.coarse j .Y i).val * localHashWeight28 ω i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hs := htight i
    have hz : (P.coarse j .Z i).val ≤ P.grade := by omega
    have hn : P.grade - (P.coarse j .Z i).val =
        (P.coarse j .X i).val + (P.coarse j .Y i).val := by omega
    rw [← Nat.cast_sub hz, hn, Nat.cast_add]
    ring
  have hinv := inverse_two_mul28 M hprime hodd
  unfold localHashX28 localHashY28 localHashZ28
  rw [hcomp]
  calc
    localHashZero28 ω + ∑ i, (P.coarse j .X i).val * localHashWeight28 ω i +
        (localHashZero28 ω + localHashOne28 ω +
          ∑ i, (P.coarse j .Y i).val * localHashWeight28 ω i) =
      2 * localHashZero28 ω +
        (localHashOne28 ω +
          ((∑ i, (P.coarse j .X i).val * localHashWeight28 ω i) +
            ∑ i, (P.coarse j .Y i).val * localHashWeight28 ω i)) := by ring
    _ = 2 * (localHashZero28 ω + Ring.inverse 2 *
        (localHashOne28 ω +
          ((∑ i, (P.coarse j .X i).val * localHashWeight28 ω i) +
            ∑ i, (P.coarse j .Y i).val * localHashWeight28 ω i))) := by
      rw [mul_add, ← mul_assoc, show (2 : ZMod M) * Ring.inverse 2 = 1 by
        rw [mul_comm, hinv], one_mul]

private theorem localHashX_eq_of_coarse28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .X = P.coarse k .X) :
    localHashX28 P M ω j = localHashX28 P M ω k := by
  unfold localHashX28
  rw [h]

private theorem localHashY_eq_of_coarse28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .Y = P.coarse k .Y) :
    localHashY28 P M ω j = localHashY28 P M ω k := by
  unfold localHashY28
  rw [h]

private theorem localHashZ_eq_of_coarse28 (P : RawPopulation) (M : ℕ)
    (ω : HashOutcome P M) (j k : P.Label)
    (h : P.coarse j .Z = P.coarse k .Z) :
    localHashZ28 P M ω j = localHashZ28 P M ω k := by
  unfold localHashZ28
  rw [h]

private theorem selected_unique_local28 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (ω : HashOutcome P M) (j k : P.Label)
    (hj : j ∈ selected P M B ω) (hk : k ∈ localSurvives28 P M B ω)
    (hcoarse : P.coarse k .X = P.coarse j .X) : k = j := by
  classical
  rw [selected_eq_local28] at hj
  exact (Finset.mem_filter.mp (show j ∈ localSelected28 P M B ω from hj)).2.2
    k hk hcoarse

private def physicalLabel28 {w : ℕ} {g : GlobalSpec w} {n : ℕ}
    {ξ : ExactGrid g n} {r : Fin 6}
    (jX jY jZ : (globalPopulation g n ξ r).Label) (W : Side) :
    (globalPopulation g n ξ r).Label :=
  match W with
  | .X => jX
  | .Y => jY
  | .Z => jZ

private def mixedGlobalShape28 {w : ℕ} {g : GlobalSpec w} {n : ℕ}
    {ξ : ExactGrid g n} {r : Fin 6}
    (jX jY jZ : (globalPopulation g n ξ r).Label)
    (i : Fin (globalPopulation g n ξ r).n)
    (hsum : coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w) :
    Shape w :=
  ⟨((jX.val i).val.1, (jY.val i).val.2.1, (jZ.val i).val.2.2), hsum⟩

set_option maxHeartbeats 1000000 in
private noncomputable def mixedGlobalLabel28 {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6)
    (jX jY jZ : (globalPopulation g n ξ r).Label)
    (hsum : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w) :
    (globalPopulation g n ξ r).Label := by
  classical
  dsimp [globalPopulation] at jX jY jZ ⊢
  let J := fun i => mixedGlobalShape28 jX jY jZ i (hsum i)
  refine ⟨J, ?_⟩
  intro W a
  cases W with
  | X => simpa [J, mixedGlobalShape28, coord] using jX.property .X a
  | Y => simpa [J, mixedGlobalShape28, coord] using jY.property .Y a
  | Z => simpa [J, mixedGlobalShape28, coord] using jZ.property .Z a

private theorem mixedGlobalLabel_coarse28 {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6)
    (jX jY jZ : (globalPopulation g n ξ r).Label)
    (hsum : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w)
    (W : Side) :
    (rolePopulation (globalPopulation g n ξ r) (g.perm r)).coarse
        (mixedGlobalLabel28 g n ξ r jX jY jZ hsum) W =
      (rolePopulation (globalPopulation g n ξ r) (g.perm r)).coarse
        (physicalLabel28 jX jY jZ (g.perm r W)) W := by
  funext i
  apply Fin.ext
  dsimp [rolePopulation, globalPopulation]
  cases hW : g.perm r W <;> rfl

private theorem mixedGlobalLabel_coord28 {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6)
    (jX jY jZ : (globalPopulation g n ξ r).Label)
    (hsum : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w)
    (W : Side) (i : Fin (globalPopulation g n ξ r).n) :
    coord W ((mixedGlobalLabel28 g n ξ r jX jY jZ hsum).val i) =
      coord W ((physicalLabel28 jX jY jZ W).val i) := by
  cases W <;> rfl

private theorem side_univ28 : (Finset.univ : Finset Side) = {.X, .Y, .Z} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private theorem global_role_tight28 {w : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (n : ℕ) (ξ : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n ξ r).Label) (i : Fin (globalPopulation g n ξ r).n) :
    ((rolePopulation (globalPopulation g n ξ r) (g.perm r)).coarse j .X i).val +
      ((rolePopulation (globalPopulation g n ξ r) (g.perm r)).coarse j .Y i).val +
      ((rolePopulation (globalPopulation g n ξ r) (g.perm r)).coarse j .Z i).val =
      (rolePopulation (globalPopulation g n ξ r) (g.perm r)).grade := by
  dsimp [rolePopulation, globalPopulation] at j i ⊢
  let u := j.val i
  let e : Side ≃ Side := Equiv.ofBijective (g.perm r) (hg.roles.1 r)
  have he := Equiv.sum_comp e (fun W => coord W u)
  have hplain : (∑ W, coord W u) = 2*w := by
    rw [side_univ28]
    simpa [coord, add_assoc] using u.property
  have hh := he.trans hplain
  rw [side_univ28] at hh
  dsimp only [e, Equiv.ofBijective_apply] at hh
  dsimp [u] at hh
  have hXY : g.perm r .X ≠ g.perm r .Y :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hXZ : g.perm r .X ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hYZ : g.perm r .Y ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  cases hX : g.perm r .X <;>
    cases hY : g.perm r .Y <;>
      cases hZ : g.perm r .Z <;>
        simp_all [u, coord, add_assoc] <;> omega

set_option maxHeartbeats 2000000 in
private theorem global_physical_labels_align28 {w : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (n : ℕ) (ξ : ExactGrid g n)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (globalPopulation g n ξ r) (M r))
    (hvalid : ValidGlobalHashes g n ξ M B) (r : Fin 6)
    (jX jY jZ : (globalPopulation g n ξ r).Label)
    (hsel : ∀ W, physicalLabel28 jX jY jZ W ∈ selected
      (rolePopulation (globalPopulation g n ξ r) (g.perm r)) (M r) (B r) (ω r))
    (hsum : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w) :
    ∀ (W : Side) (i : Fin (globalPopulation g n ξ r).n),
      coord (g.perm r W) ((physicalLabel28 jX jY jZ (g.perm r .X)).val i) =
        coord (g.perm r W) ((physicalLabel28 jX jY jZ (g.perm r W)).val i) := by
  classical
  let P := rolePopulation (globalPopulation g n ξ r) (g.perm r)
  let jL := fun W => physicalLabel28 jX jY jZ (g.perm r W)
  let jmix := mixedGlobalLabel28 g n ξ r jX jY jZ hsum
  have hcX : P.coarse jmix .X = P.coarse (jL .X) .X := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n ξ r jX jY jZ hsum .X
  have hcY : P.coarse jmix .Y = P.coarse (jL .Y) .Y := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n ξ r jX jY jZ hsum .Y
  have hcZ : P.coarse jmix .Z = P.coarse (jL .Z) .Z := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n ξ r jX jY jZ hsum .Z
  have hhX := localHashX_eq_of_coarse28 P (M r) (ω r) jmix (jL .X) hcX
  have hhY := localHashY_eq_of_coarse28 P (M r) (ω r) jmix (jL .Y) hcY
  have hhZ := localHashZ_eq_of_coarse28 P (M r) (ω r) jmix (jL .Z) hcZ
  have hdX := selected_hash_data28 P (M r) (B r) (ω r) (jL .X) (by
    simpa [P, jL] using hsel (g.perm r .X))
  have hdY := selected_hash_data28 P (M r) (B r) (ω r) (jL .Y) (by
    simpa [P, jL] using hsel (g.perm r .Y))
  have hdZ := selected_hash_data28 P (M r) (B r) (ω r) (jL .Z) (by
    simpa [P, jL] using hsel (g.perm r .Z))
  have hmixAP := local_hash_ap28 P (M r) (ω r) jmix
    (fun i => by simpa [P, jmix] using global_role_tight28 g hg n ξ r jmix i)
    (hvalid r).1 (hvalid r).2.1
  rw [hhX, hhY, hhZ] at hmixAP
  have hZmem : localHashZ28 P (M r) (ω r) (jL .Z) ∈ B r := by
    rw [← hdZ.2.1, ← hdZ.1]
    exact hdZ.2.2
  have hYmem : localHashY28 P (M r) (ω r) (jL .Y) ∈ B r := by
    rw [← hdY.1]
    exact hdY.2.2
  have hAP := (hvalid r).2.2.2
    (localHashX28 P (M r) (ω r) (jL .X)) hdX.2.2
    (localHashZ28 P (M r) (ω r) (jL .Z)) hZmem
    (localHashY28 P (M r) (ω r) (jL .Y)) hYmem hmixAP
  have hsurv : jmix ∈ localSurvives28 P (M r) (B r) (ω r) := by
    simp only [localSurvives28, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [hhX, hhY]
      exact hAP.1.trans hAP.2.symm
    constructor
    · rw [hhY, hhZ]
      exact hAP.2
    · rw [hhX]
      exact hdX.2.2
  have hjLX : jL .X ∈ selected P (M r) (B r) (ω r) := by
    simpa [P, jL] using hsel (g.perm r .X)
  have hmixed : jmix = jL .X :=
    selected_unique_local28 P (M r) (B r) (ω r) (jL .X) jmix hjLX hsurv hcX
  intro W i
  have hc := mixedGlobalLabel_coord28 g n ξ r jX jY jZ hsum (g.perm r W) i
  change coord (g.perm r W) (jmix.val i) =
    coord (g.perm r W) ((jL W).val i) at hc
  rw [hmixed] at hc
  simpa [jL, jmix] using hc

private def sideWord28 {A : Type} (x y z : A) : Side → A
  | .X => x
  | .Y => y
  | .Z => z

private theorem sideWord_apply28 {A B : Type} (x y z : A → B) (W : Side) (a : A) :
    sideWord28 x y z W a = sideWord28 (x a) (y a) (z a) W := by
  cases W <;> rfl

private theorem lvl7_eq_zero_of_chunkLvl_eq_zero28 {q w : ℕ}
    (a : Fin w → CW90.Idx7 q) (h : chunkLvl (chunkOf a) = 0) (c : Fin w) :
    (CW90.lvl7 (a c)).val = 0 := by
  have hle : (chunkOf a c).val ≤ chunkLvl (chunkOf a) := by
    unfold chunkLvl
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun p => (chunkOf a p).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simpa only [chunkOf] using (show (chunkOf a c).val = 0 by omega)

private theorem cwZ_ne_permutations28 {q : ℕ} (x y z : CW90.Idx7 q)
    (h : cwZ q x y z ≠ 0) :
    cwZ q y x z ≠ 0 ∧ cwZ q x z y ≠ 0 ∧ cwZ q y z x ≠ 0 ∧
      cwZ q z x y ≠ 0 ∧ cwZ q z y x ≠ 0 := by
  rcases x with (_ | x₀) | x₀ <;>
    rcases y with (_ | y₀) | y₀ <;>
      rcases z with (_ | z₀) | z₀ <;> simp_all [cwZ]

set_option maxHeartbeats 1000000 in
private theorem chunk_reflect_last_of_cwZ_ne28 {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf z) = 0) :
    chunkOf y = reflect (chunkOf x) := by
  funext c
  apply Fin.ext
  have hz := lvl7_eq_zero_of_chunkLvl_eq_zero28 z hzero c
  have hw := hcw c
  rcases hx : x c with (_ | x₀) | x₀ <;>
    rcases hy : y c with (_ | y₀) | y₀ <;>
      rcases hz' : z c with (_ | z₀) | z₀ <;>
        simp_all [cwZ, chunkOf, reflect, CW90.lvl7]

private theorem chunk_reflect_of_cwZ_ne28 {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf (sideWord28 x y z C)) = 0) :
    chunkOf (sideWord28 x y z B) = reflect (chunkOf (sideWord28 x y z A)) := by
  cases A <;> cases B <;> cases C <;> simp_all [sideWord28]
  · exact chunk_reflect_last_of_cwZ_ne28 x y z hcw hzero
  · exact chunk_reflect_last_of_cwZ_ne28 x z y
      (fun c => (cwZ_ne_permutations28 (x c) (y c) (z c) (hcw c)).2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne28 y x z
      (fun c => (cwZ_ne_permutations28 (x c) (y c) (z c) (hcw c)).1) hzero
  · exact chunk_reflect_last_of_cwZ_ne28 y z x
      (fun c => (cwZ_ne_permutations28 (x c) (y c) (z c) (hcw c)).2.2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne28 z x y
      (fun c => (cwZ_ne_permutations28 (x c) (y c) (z c) (hcw c)).2.2.2.1) hzero
  · exact chunk_reflect_last_of_cwZ_ne28 z y x
      (fun c => (cwZ_ne_permutations28 (x c) (y c) (z c) (hcw c)).2.2.2.2) hzero

private theorem reflect_reflect28 {w : ℕ} (σ : Chunk w) : reflect (reflect σ) = σ := by
  funext c
  apply Fin.ext
  simp only [reflect]
  have hc := (σ c).isLt
  omega

private theorem globalCellCount_exact_reflect28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (A B : Side) (j : (globalPopulation g n ξ r).Label)
    (aA : (globalPopulation g n ξ r).Part A)
    (aB : (globalPopulation g n ξ r).Part B)
    (u : Shape w) (σ : Chunk w)
    (hreflect : ∀ i : Fin (globalPopulation g n ξ r).n,
      j.val i = u → (aB i = σ ↔ aA i = reflect σ)) :
    globalCellCount g n ξ r B j aB (fun v => v = u) σ =
      globalCellCount g n ξ r A j aA (fun v => v = u) (reflect σ) := by
  unfold globalCellCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hju, ha⟩
    exact ⟨hju, (hreflect i hju).mp ha⟩
  · rintro ⟨hju, ha⟩
    exact ⟨hju, (hreflect i hju).mpr ha⟩

private theorem globalCellCount_grade_congr28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (W : Side) (j k : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W)
    (halign : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord W (j.val i) = coord W (k.val i))
    (grade : Fin (2*w+1)) (σ : Chunk w) :
    globalCellCount g n ξ r W j a (fun u => coord W u = grade.val) σ =
      globalCellCount g n ξ r W k a (fun u => coord W u = grade.val) σ := by
  unfold globalCellCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [halign i]

set_option maxHeartbeats 1000000 in
private theorem global_boundary_cell_count_from_words28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (hξ : GridBoundaryCompatible ξ) (r : Fin 6)
    (j : (globalPopulation g n ξ r).Label)
    (x y z : GlobalPhysicalWord q g n ξ r) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hincA : (globalPopulation g n ξ r).incidence A j
      (globalPhysicalPart q g n ξ r A (sideWord28 x y z A)))
    (hcoarseC : globalCoarseContains g n ξ r C j
      (globalPhysicalPart q g n ξ r C (sideWord28 x y z C)))
    (hcw : ∀ i c, cwZ q (x i c) (y i c) (z i c) ≠ 0)
    (u : Shape w) (hboundary : coord C u = 0) (σ : Chunk w) :
    globalCellCount g n ξ r B j
        (globalPhysicalPart q g n ξ r B (sideWord28 x y z B))
        (fun v => v = u) σ = ξ.count B r u σ := by
  rw [globalCellCount_exact_reflect28 q n g ξ r A B j
    (globalPhysicalPart q g n ξ r A (sideWord28 x y z A))
    (globalPhysicalPart q g n ξ r B (sideWord28 x y z B)) u σ]
  · rw [globalCellCount_exact28 q n g ξ r A j _ hincA u (reflect σ)]
    exact (hξ r u C B A hAB.symm hBC hAC hboundary σ).symm
  · intro i hju
    have hzero : chunkLvl (chunkOf (sideWord28 x y z C i)) = 0 := by
      calc
        chunkLvl (chunkOf (sideWord28 x y z C i)) = coord C (j.val i) := by
          simpa only [globalPhysicalPart] using hcoarseC i
        _ = coord C u := by rw [hju]
        _ = 0 := hboundary
    have hzero' : chunkLvl (chunkOf (sideWord28 (x i) (y i) (z i) C)) = 0 := by
      rw [← sideWord_apply28]
      exact hzero
    have hreflect := chunk_reflect_of_cwZ_ne28
      (x i) (y i) (z i) A B C hAB hAC hBC (hcw i) hzero'
    have hreflect' : chunkOf (sideWord28 x y z B i) =
        reflect (chunkOf (sideWord28 x y z A i)) := by
      rw [sideWord_apply28, sideWord_apply28]
      exact hreflect
    simpa only [globalPhysicalPart] using (show
      chunkOf (sideWord28 x y z B i) = σ ↔
        chunkOf (sideWord28 x y z A i) = reflect σ by
      rw [hreflect']
      constructor
      · intro h
        have := congrArg reflect h
        simpa only [reflect_reflect28] using this
      · intro h
        rw [h, reflect_reflect28])

private theorem global_compatible_of_boundary_and_alignment28 {w : ℕ} (q n : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (which : Fin 2) (j k : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part
      (g.perm r (if which = 0 then .Y else .Z)))
    (hboundary : ∀ u : Shape w,
      (if which = 0 then coord (g.perm r .Z) u = 0
        else coord (g.perm r .X) u = 0 ∨ coord (g.perm r .Y) u = 0) →
      ∀ σ, globalCellCount g n ξ r
        (g.perm r (if which = 0 then .Y else .Z)) j a (fun v => v = u) σ =
        ξ.count (g.perm r (if which = 0 then .Y else .Z)) r u σ)
    (halign : ∀ i : Fin (globalPopulation g n ξ r).n,
      coord (g.perm r (if which = 0 then .Y else .Z)) (j.val i) =
        coord (g.perm r (if which = 0 then .Y else .Z)) (k.val i))
    (hinc : (globalPopulation g n ξ r).incidence
      (g.perm r (if which = 0 then .Y else .Z)) k a) :
    globalCompatible g n ξ r which j a := by
  have hk := global_incidence_implies_compatible28 q n g ξ r which k a hinc
  unfold globalCompatible at hk ⊢
  dsimp only at hk ⊢
  have hside :
      (if which = 0 then g.perm r .Y else g.perm r .Z) =
        g.perm r (if which = 0 then .Y else .Z) := by
    by_cases hw : which = 0 <;> simp [hw]
  rw [hside] at hk ⊢
  constructor
  · exact hboundary
  · intro grade σ
    rw [globalCellCount_grade_congr28 q n g ξ r _ j k a halign grade σ]
    exact hk.2 grade σ

private theorem global_roleY_label_eq28 {w : ℕ} (q n M : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (globalPopulation g n ξ r) M)
    (j k : (globalPopulation g n ξ r).Label)
    (hj : j ∈ selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω)
    (a : (globalPopulation g n ξ r).Part (g.perm r .Y))
    (hjcoarse : globalCoarseContains g n ξ r (g.perm r .Y) j a)
    (hjcompat : globalCompatible g n ξ r 0 j a)
    (hkinc : (globalPopulation g n ξ r).incidence (g.perm r .Y) k a)
    (hkeep : globalPartKeep g n ξ r M B ω .zUseful (g.perm r .Y) a) : k = j := by
  classical
  unfold globalPartKeep at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_, _, _, hunique, _, _, _, _⟩
  let S := selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω
  let matching := S.filter fun l => globalCoarseContains g n ξ r (g.perm r .Y) l a
  let C := matching.filter fun l => globalCompatible g n ξ r 0 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hunique rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hj, hjcoarse⟩, hjcompat⟩
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hk, global_incidence_implies_coarseContains28 q n g ξ r _ k a hkinc⟩,
      global_incidence_implies_compatible28 q n g ξ r 0 k a hkinc⟩
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

private theorem global_roleZ_label_eq28 {w : ℕ} (q n M : ℕ)
    (g : GlobalSpec w) (ξ : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (globalPopulation g n ξ r) M)
    (j k : (globalPopulation g n ξ r).Label)
    (hj : j ∈ selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω)
    (hk : k ∈ selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω)
    (a : (globalPopulation g n ξ r).Part (g.perm r .Z))
    (hjcoarse : globalCoarseContains g n ξ r (g.perm r .Z) j a)
    (hjcompat : globalCompatible g n ξ r 1 j a)
    (hkinc : (globalPopulation g n ξ r).incidence (g.perm r .Z) k a)
    (hkeep : globalPartKeep g n ξ r M B ω .zUseful (g.perm r .Z) a) : k = j := by
  classical
  unfold globalPartKeep at hkeep
  dsimp only at hkeep
  rcases hkeep with ⟨_, _, _, _, _, _, hunique, _⟩
  let S := selected (rolePopulation (globalPopulation g n ξ r) (g.perm r)) M B ω
  let matching := S.filter fun l => globalCoarseContains g n ξ r (g.perm r .Z) l a
  let C := matching.filter fun l => globalCompatible g n ξ r 1 l a
  have hcard : C.card = 1 := by simpa [S, matching, C] using hunique rfl
  have hjC : j ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hj, hjcoarse⟩, hjcompat⟩
  have hkC : k ∈ C := by
    simp only [C, matching, Finset.mem_filter]
    exact ⟨⟨hk, global_incidence_implies_coarseContains28 q n g ξ r _ k a hkinc⟩,
      global_incidence_implies_compatible28 q n g ξ r 1 k a hkinc⟩
  exact (Finset.card_le_one.mp (by omega) j hjC k hkC).symm

private theorem lvl7_add_of_cwZ_ne28 {q : ℕ} (a b c : CW90.Idx7 q)
    (h : cwZ q a b c ≠ 0) :
    (CW90.lvl7 a).val + (CW90.lvl7 b).val + (CW90.lvl7 c).val = 2 := by
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
    rcases c with (_ | c) | c <;> simp_all [cwZ, CW90.lvl7]


private theorem regional_physical_labels_align37 {w n M : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (hprime : Nat.Prime M) (hodd : 2 < M) (hAP : HashAPFree B)
    (jX jY jZ : (globalPopulation g n xi r).Label)
    (hsel : ∀ W, physicalLabel28 jX jY jZ W ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega)
    (hsum : ∀ i : Fin (globalPopulation g n xi r).n,
      coord .X (jX.val i) + coord .Y (jY.val i) + coord .Z (jZ.val i) = 2*w) :
    ∀ (W : Side) (i : Fin (globalPopulation g n xi r).n),
      coord (g.perm r W) ((physicalLabel28 jX jY jZ (g.perm r .X)).val i) =
        coord (g.perm r W) ((physicalLabel28 jX jY jZ (g.perm r W)).val i) := by
  classical
  let P := rolePopulation (globalPopulation g n xi r) (g.perm r)
  let jL := fun W => physicalLabel28 jX jY jZ (g.perm r W)
  let jmix := mixedGlobalLabel28 g n xi r jX jY jZ hsum
  have hcX : P.coarse jmix .X = P.coarse (jL .X) .X := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n xi r jX jY jZ hsum .X
  have hcY : P.coarse jmix .Y = P.coarse (jL .Y) .Y := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n xi r jX jY jZ hsum .Y
  have hcZ : P.coarse jmix .Z = P.coarse (jL .Z) .Z := by
    simpa [P, jL, jmix] using mixedGlobalLabel_coarse28 g n xi r jX jY jZ hsum .Z
  have hhX := localHashX_eq_of_coarse28 P M omega jmix (jL .X) hcX
  have hhY := localHashY_eq_of_coarse28 P M omega jmix (jL .Y) hcY
  have hhZ := localHashZ_eq_of_coarse28 P M omega jmix (jL .Z) hcZ
  have hdX := selected_hash_data28 P M B omega (jL .X) (by
    simpa [P, jL] using hsel (g.perm r .X))
  have hdY := selected_hash_data28 P M B omega (jL .Y) (by
    simpa [P, jL] using hsel (g.perm r .Y))
  have hdZ := selected_hash_data28 P M B omega (jL .Z) (by
    simpa [P, jL] using hsel (g.perm r .Z))
  have hmixAP := local_hash_ap28 P M omega jmix
    (fun i => by simpa [P, jmix] using global_role_tight28 g hg n xi r jmix i)
    hprime hodd
  rw [hhX, hhY, hhZ] at hmixAP
  have hZmem : localHashZ28 P M omega (jL .Z) ∈ B := by
    rw [← hdZ.2.1, ← hdZ.1]
    exact hdZ.2.2
  have hYmem : localHashY28 P M omega (jL .Y) ∈ B := by
    rw [← hdY.1]
    exact hdY.2.2
  have hfree := hAP
    (localHashX28 P M omega (jL .X)) hdX.2.2
    (localHashZ28 P M omega (jL .Z)) hZmem
    (localHashY28 P M omega (jL .Y)) hYmem hmixAP
  have hsurv : jmix ∈ localSurvives28 P M B omega := by
    simp only [localSurvives28, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [hhX, hhY]
      exact hfree.1.trans hfree.2.symm
    constructor
    · rw [hhY, hhZ]
      exact hfree.2
    · rw [hhX]
      exact hdX.2.2
  have hjLX : jL .X ∈ selected P M B omega := by
    simpa [P, jL] using hsel (g.perm r .X)
  have hmixed : jmix = jL .X :=
    selected_unique_local28 P M B omega (jL .X) jmix hjLX hsurv hcX
  intro W i
  have hc := mixedGlobalLabel_coord28 g n xi r jX jY jZ hsum (g.perm r W) i
  change coord (g.perm r W) (jmix.val i) =
    coord (g.perm r W) ((jL W).val i) at hc
  rw [hmixed] at hc
  simpa [jL, jmix] using hc

set_option maxHeartbeats 3000000 in
private theorem regional_source_role_labels_eq37 {w n M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (xi : ExactGrid g n) (hxi : GridBoundaryCompatible xi) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (hprime : Nat.Prime M) (hodd : 2 < M) (hAP : HashAPFree B)
    (px : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).X)
    (py : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).Y)
    (pz : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).Z)
    (htarget : (topZ q w (globalPopulation g n xi r).n).tensor
      px.2.val py.2.val pz.2.val ≠ 0) :
    let label := fun W => physicalLabel28 (ξ := xi) (r := r)
      px.1.val py.1.val pz.1.val W
    label (g.perm r .Y) = label (g.perm r .X) ∧
      label (g.perm r .Z) = label (g.perm r .X) := by
  classical
  let lX := px.1
  let lY := py.1
  let lZ := pz.1
  let label := fun W => physicalLabel28 (ξ := xi) (r := r) lX.val lY.val lZ.val W
  let wX := px.2.val
  let wY := py.2.val
  let wZ := pz.2.val
  have hpX := px.2.property
  have hpY := py.2.property
  have hpZ := pz.2.property
  have hselected : ∀ W, label W ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega := by
    intro W
    cases W with
    | X => exact lX.property
    | Y => exact lY.property
    | Z => exact lZ.property
  have hinc : ∀ W, (globalPopulation g n xi r).incidence W (label W)
      (globalPhysicalPart q g n xi r W (sideWord28 wX wY wZ W)) := by
    intro W
    cases W with
    | X => simpa [label, lX, wX, sideWord28, physicalLabel28] using hpX.1
    | Y => simpa [label, lY, wY, sideWord28, physicalLabel28] using hpY.1
    | Z => simpa [label, lZ, wZ, sideWord28, physicalLabel28] using hpZ.1
  have hkeep : ∀ W, globalPartKeep g n xi r M B omega
      .zUseful W (globalPhysicalPart q g n xi r W (sideWord28 wX wY wZ W)) := by
    intro W
    cases W with
    | X => simpa [wX, sideWord28] using hpX.2
    | Y => simpa [wY, sideWord28] using hpY.2
    | Z => simpa [wZ, sideWord28] using hpZ.2
  have hcw : ∀ i : Fin (globalPopulation g n xi r).n, ∀ c : Fin w,
      cwZ q (wX i c) (wY i c) (wZ i c) ≠ 0 := by
    unfold topZ at htarget
    dsimp only [ITensor.tensor] at htarget
    unfold tensorPower at htarget
    rw [Finset.prod_ne_zero_iff] at htarget
    intro i c
    have hi := htarget i (Finset.mem_univ i)
    rw [Finset.prod_ne_zero_iff] at hi
    exact hi c (Finset.mem_univ c)
  have hsum : ∀ i : Fin (globalPopulation g n xi r).n,
      coord .X (lX.val.val i) + coord .Y (lY.val.val i) +
        coord .Z (lZ.val.val i) = 2*w := by
    intro i
    rw [← hpX.1.1 i, ← hpY.1.1 i, ← hpZ.1.1 i]
    simp only [globalPhysicalPart, chunkLvl, chunkOf]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      ∑ c : Fin w,
          ((CW90.lvl7 (wX i c)).val + (CW90.lvl7 (wY i c)).val +
            (CW90.lvl7 (wZ i c)).val) =
          ∑ _c : Fin w, 2 := by
        apply Finset.sum_congr rfl
        intro c _hc
        exact lvl7_add_of_cwZ_ne28 _ _ _ (hcw i c)
      _ = 2*w := by simp [Nat.mul_comm]
  have halign := regional_physical_labels_align37 g hg xi r B omega
    hprime hodd hAP lX.val lY.val lZ.val (by simpa [label] using hselected) hsum
  have hcoarse : ∀ R, globalCoarseContains g n xi r (g.perm r R)
      (label (g.perm r .X))
      (globalPhysicalPart q g n xi r (g.perm r R)
        (sideWord28 wX wY wZ (g.perm r R))) := by
    intro R i
    calc
      chunkLvl (globalPhysicalPart q g n xi r (g.perm r R)
          (sideWord28 wX wY wZ (g.perm r R)) i) =
          coord (g.perm r R) ((label (g.perm r R)).val i) :=
        (hinc (g.perm r R)).1 i
      _ = coord (g.perm r R) ((label (g.perm r .X)).val i) :=
        (halign R i).symm
  have hXY : g.perm r .X ≠ g.perm r .Y :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hXZ : g.perm r .X ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hYZ : g.perm r .Y ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hcompatY : globalCompatible g n xi r 0
      (label (g.perm r .X))
      (globalPhysicalPart q g n xi r (g.perm r .Y)
        (sideWord28 wX wY wZ (g.perm r .Y))) := by
    apply global_compatible_of_boundary_and_alignment28 q n g xi r 0
      (label (g.perm r .X)) (label (g.perm r .Y))
    · intro u hboundary sigma
      simpa using global_boundary_cell_count_from_words28 q n g xi hxi r
        (label (g.perm r .X)) wX wY wZ
        (g.perm r .X) (g.perm r .Y) (g.perm r .Z)
        hXY hXZ hYZ (hinc (g.perm r .X)) (hcoarse .Z) hcw
        u hboundary sigma
    · intro i
      exact halign .Y i
    · exact hinc (g.perm r .Y)
  have hY : label (g.perm r .Y) = label (g.perm r .X) :=
    global_roleY_label_eq28 q n M g xi r B omega
      (label (g.perm r .X)) (label (g.perm r .Y))
      (hselected (g.perm r .X)) (hselected (g.perm r .Y)) _
      (hcoarse .Y) hcompatY (hinc (g.perm r .Y)) (hkeep (g.perm r .Y))
  have hincY0 := hinc (g.perm r .Y)
  rw [hY] at hincY0
  have hcompatZ : globalCompatible g n xi r 1
      (label (g.perm r .X))
      (globalPhysicalPart q g n xi r (g.perm r .Z)
        (sideWord28 wX wY wZ (g.perm r .Z))) := by
    apply global_compatible_of_boundary_and_alignment28 q n g xi r 1
      (label (g.perm r .X)) (label (g.perm r .Z))
    · intro u hboundary sigma
      rcases hboundary with hX0 | hY0
      · simpa using global_boundary_cell_count_from_words28 q n g xi hxi r
          (label (g.perm r .X)) wX wY wZ
          (g.perm r .Y) (g.perm r .Z) (g.perm r .X)
          hYZ hXY.symm hXZ.symm hincY0 (hcoarse .X) hcw u hX0 sigma
      · simpa using global_boundary_cell_count_from_words28 q n g xi hxi r
          (label (g.perm r .X)) wX wY wZ
          (g.perm r .X) (g.perm r .Z) (g.perm r .Y)
          hXZ hXY hYZ.symm (hinc (g.perm r .X)) (hcoarse .Y) hcw u hY0 sigma
    · intro i
      exact halign .Z i
    · exact hinc (g.perm r .Z)
  have hZ : label (g.perm r .Z) = label (g.perm r .X) :=
    global_roleZ_label_eq28 q n M g xi r B omega
      (label (g.perm r .X)) (label (g.perm r .Z))
      (hselected (g.perm r .X)) (hselected (g.perm r .Z)) _
      (hcoarse .Z) hcompatZ (hinc (g.perm r .Z)) (hkeep (g.perm r .Z))
  exact ⟨hY, hZ⟩

set_option maxHeartbeats 3000000 in
private theorem regional_source_physical_labels_eq37 {w n M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (xi : ExactGrid g n) (hxi : GridBoundaryCompatible xi) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (hprime : Nat.Prime M) (hodd : 2 < M) (hAP : HashAPFree B)
    (px : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).X)
    (py : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).Y)
    (pz : (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}) ×
        (globalBrokenCopyZ q g n xi r M B omega j.val).Z)
    (htarget : (topZ q w (globalPopulation g n xi r).n).tensor
      px.2.val py.2.val pz.2.val ≠ 0) :
    px.1 = py.1 ∧ px.1 = pz.1 := by
  classical
  let label := fun W => physicalLabel28 (ξ := xi) (r := r)
    px.1.val py.1.val pz.1.val W
  have hrole := regional_source_role_labels_eq37 q g hg xi hxi r B omega
    hprime hodd hAP px py pz htarget
  change label (g.perm r .Y) = label (g.perm r .X) ∧
    label (g.perm r .Z) = label (g.perm r .X) at hrole
  have hall : ∀ W, label W = label (g.perm r .X) := by
    intro W
    rcases (hg.roles.1 r).2 W with ⟨R, rfl⟩
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

private theorem regional_same_label_coeff37 {w n M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    [DecidableEq {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega}]
    (j : {j // j ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega})
    (x : (globalBrokenCopyZ q g n xi r M B omega j.val).X)
    (y : (globalBrokenCopyZ q g n xi r M B omega j.val).Y)
    (z : (globalBrokenCopyZ q g n xi r M B omega j.val).Z) :
    (dependentSumZ (fun k : {k // k ∈ selected
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega} =>
        globalBrokenCopyZ q g n xi r M B omega k.val)).tensor
      ⟨j, x⟩ ⟨j, y⟩ ⟨j, z⟩ =
    (topZ q w (globalPopulation g n xi r).n).tensor x.val y.val z.val := by
  classical
  unfold dependentSumZ
  dsimp only [ITensor.tensor]
  rw [dif_pos rfl, dif_pos rfl]
  unfold globalBrokenCopyZ topZ tensorPower
  dsimp only [ITensor.tensor]
  apply Finset.prod_congr rfl
  intro i _hi
  unfold conZ
  rw [ADVXXZ.zoP_apply, if_pos]
  · rfl
  · exact ⟨by simpa only [levOf, globalPhysicalPart] using x.property.1.1 i,
      by simpa only [levOf, globalPhysicalPart] using y.property.1.1 i,
      by simpa only [levOf, globalPhysicalPart] using z.property.1.1 i⟩

set_option maxHeartbeats 3000000 in
/-- Ordered deletion localized to one regional source. -/
theorem globalSelectedRegion_restrict_top37 {w b M : ℕ} [NeZero M]
    (q m : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (hb : GlobalIntegral g b) (xi : ExactGrid g (b*m))
    (hxi : GridBoundaryCompatible xi) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b*m) xi r) M)
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hgrade : (globalPopulation g (b*m) xi r).grade < M)
    (hAP : HashAPFree B) :
  Restricts (globalSelectedRegionFamily27 q g xi r B omega).tensor
    (topZ q w (globalPopulation g (b*m) xi r).n).tensor := by
  classical
  by_cases hn : (globalPopulation g (b*m) xi r).n = 0
  · rw [globalSelectedRegionFamily27, if_pos hn, hn]
    refine ADVXXZ.restricts_of_sub
      (fun _ i => Fin.elim0 i) (fun _ i => Fin.elim0 i) (fun _ i => Fin.elim0 i) ?_
    intro x y z
    simp [unitFamilyZ, topZ, tensorPower]
  · rw [globalSelectedRegionFamily27, if_neg hn]
    refine ADVXXZ.restricts_of_sub (fun x => x.2.val) (fun y => y.2.val)
      (fun z => z.2.val) ?_
    rintro px py pz
    by_cases htarget : (topZ q w (globalPopulation g (b*m) xi r).n).tensor
        px.2.val py.2.val pz.2.val ≠ 0
    · have hlabels := regional_source_physical_labels_eq37 q g hg xi hxi r B omega
        hprime hodd hAP px py pz htarget
      rcases px with ⟨lx, x⟩
      rcases py with ⟨ly, y⟩
      rcases pz with ⟨lz, z⟩
      dsimp only at hlabels ⊢
      rcases hlabels with ⟨hxy, hxz⟩
      subst ly
      subst lz
      exact regional_same_label_coeff37 q g xi r B omega lx x y z
    · have htarget0 : (topZ q w (globalPopulation g (b*m) xi r).n).tensor
          px.2.val py.2.val pz.2.val = 0 := not_ne_iff.mp htarget
      rcases px with ⟨lx, x⟩
      rcases py with ⟨ly, y⟩
      rcases pz with ⟨lz, z⟩
      by_cases hxy : lx = ly
      · subst ly
        by_cases hxz : lx = lz
        · subst lz
          rw [regional_same_label_coeff37 q g xi r B omega lx x y z, htarget0]
        · simp [dependentSumZ, hxz, htarget0]
      · simp [dependentSumZ, hxy, htarget0]

theorem globalSelectedRegion_restrict_top37_matches_display :
    GlobalExactEnvelope37.globalSelectedRegion_restrict_top37 :=
  @globalSelectedRegion_restrict_top37

end
end OmegaBound.ADVXXZGeneral
end
