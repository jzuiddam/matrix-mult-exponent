import OmegaBound.ADVXXZGeneralCExact42PositiveRegional
import OmegaBound.ADVXXZGeneralIterateInfraCopies

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

/-! The pooled producer deliberately repairs before dividing by a reserve.  These small
reindexing lemmas expose the two inverse direct-sum regroupings needed for that construction. -/

set_option maxHeartbeats 1000000 in
-- Three dependent direct-sum actions are normalized after splitting their outer labels.
private theorem dependentSumZ_restricts42
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S T : ι → ITensor) (h : ∀ i, Restricts (S i).tensor (T i).tensor) :
    Restricts (dependentSumZ S).tensor (dependentSumZ T).tensor := by
  classical
  choose A1 A2 A3 hA using h
  refine ⟨fun p q => if hq : q.1 = p.1 then A1 p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A2 p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A3 p.1 p.2 (hq ▸ q.2) else 0, ?_⟩
  funext p q r
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  obtain ⟨k, z⟩ := r
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have hv := congrFun (congrFun (congrFun (hA i) x) y) z
      simp only [dependentSumZ, Finset.mem_univ, and_self, if_true]
      rw [hv]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ,
        Finset.sum_sigma]
      simp
    · simp only [dependentSumZ, true_and, hik, if_false]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ,
        Finset.sum_sigma]
      have hki : k ≠ i := Ne.symm hik
      simp [hik, hki]
  · simp only [dependentSumZ, hij, if_false]
    simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ,
      Finset.sum_sigma]
    have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]
    intro hkj hki
    exact (hij (hki.symm.trans hkj)).elim

private theorem dependentSumZ_copies_restricts_copies42
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : ℕ) (T : ι → ITensor) :
    Restricts (dependentSumZ (fun i => copiesZ R (T i))).tensor
      (copiesZ R (dependentSumZ T)).tensor := by
  classical
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩)
    (fun y => ⟨y.2.1, ⟨y.1, y.2.2⟩⟩)
    (fun z => ⟨z.2.1, ⟨z.1, z.2.2⟩⟩) ?_
  rintro ⟨i, a, x⟩ ⟨j, b, y⟩ ⟨k, c, z⟩
  simp only [dependentSumZ, copiesZ, famDS, Finset.mem_univ, and_true]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hab : a = b
      · subst b
        by_cases hac : a = c
        · subst c
          simp
        · simp [hac]
      · simp [hab]
    · simp [hik]
  · simp [hij]

private theorem dependentSumZ_const_restricts_copies42 (R : ℕ) (T : ITensor) :
    Restricts (dependentSumZ fun _ : Fin R => T).tensor (copiesZ R T).tensor := by
  classical
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨x.1, x.2⟩) (fun y => ⟨y.1, y.2⟩) (fun z => ⟨z.1, z.2⟩) ?_
  rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  simp only [dependentSumZ, copiesZ, famDS, Finset.mem_univ, and_true]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp
    · simp [hik]
  · simp [hij]

private theorem regionProductZ_copies_restricts_copies42
    (copies : Fin 6 → ℕ) (T : Fin 6 → ITensor) :
    Restricts (regionProductZ (fun r => copiesZ (copies r) (T r))).tensor
      (copiesZ (∏ r, copies r) (regionProductZ T)).tensor := by
  classical
  let e : Fin (∏ r, copies r) ≃ ((r : Fin 6) → Fin (copies r)) :=
    Fintype.equivOfCardEq (by simp)
  refine ADVXXZ.restricts_of_sub
    (fun x => (e.symm (fun r => (x r).1), fun r => (x r).2))
    (fun y => (e.symm (fun r => (y r).1), fun r => (y r).2))
    (fun z => (e.symm (fun r => (z r).1), fun r => (z r).2)) ?_
  intro x y z
  simp only [regionProductZ, copiesZ, famDS, Finset.mem_univ, and_true]
  by_cases hxy : (fun r => (x r).1) = fun r => (y r).1
  · by_cases hyz : (fun r => (y r).1) = fun r => (z r).1
    · have hxy' : ∀ r, (x r).1 = (y r).1 := fun r => congrFun hxy r
      have hyz' : ∀ r, (y r).1 = (z r).1 := fun r => congrFun hyz r
      rw [if_pos ⟨congrArg e.symm hxy, congrArg e.symm hyz⟩]
      apply Finset.prod_congr rfl
      intro r _
      simp [hxy' r, hyz' r]
    · have hright : e.symm (fun r => (y r).1) ≠ e.symm (fun r => (z r).1) :=
        fun h => hyz (e.symm.injective h)
      rw [if_neg (fun h => hright h.2)]
      obtain ⟨r, hr⟩ : ∃ r, (y r).1 ≠ (z r).1 := by
        by_contra hall
        push_neg at hall
        exact hyz (funext hall)
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      simp [hr]
  · have hright : e.symm (fun r => (x r).1) ≠ e.symm (fun r => (y r).1) :=
      fun h => hxy (e.symm.injective h)
    rw [if_neg (fun h => hright h.1)]
    obtain ⟨r, hr⟩ : ∃ r, (x r).1 ≠ (y r).1 := by
      by_contra hall
      push_neg at hall
      exact hxy (funext hall)
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp [hr]

private theorem copiesExactLabel_restricts_sum42 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (j0 : (stagePopulationAt q p d b m r).Label)
    (hj0 : j0 ∈ (stagePopulationAt q p d b m r).target)
    (hJ : ∀ j, j ∈ J → j ∈ (stagePopulationAt q p d b m r).target) :
    Restricts (copiesZ J.card (stageExactITensor27 q m p d r j0)).tensor
      (dependentSumZ fun j : {j // j ∈ J} =>
        stageExactITensor27 q m p d r j.val).tensor := by
  classical
  let e : Fin J.card ≃ {j // j ∈ J} := Fintype.equivOfCardEq (by simp)
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨e x.1, labelExactLegEquiv27 q m p d r j0 (e x.1).val
      hj0 (hJ _ (e x.1).property) .X x.2⟩)
    (fun y => ⟨e y.1, labelExactLegEquiv27 q m p d r j0 (e y.1).val
      hj0 (hJ _ (e y.1).property) .Y y.2⟩)
    (fun z => ⟨e z.1, labelExactLegEquiv27 q m p d r j0 (e z.1).val
      hj0 (hJ _ (e z.1).property) .Z z.2⟩) ?_
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
  simp only [copiesZ, famDS, Finset.mem_univ, and_true, dependentSumZ]
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp only [and_self, if_true, stageExactITensor27]
      exact (labelExactTensor_equiv27 q m p d r j0 (e a).val hj0
        (hJ _ (e a).property) x y z).symm
    · have heac : e a ≠ e c := fun h => hac (e.injective h)
      simp [hac, heac]
  · have heab : e a ≠ e b := fun h => hab (e.injective h)
    simp [hab, heab]

private theorem goodLabel_target42 {w s b : ℕ} (q m M : ℕ) (epsilon : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : stageGood25 q p d b epsilon m r M B omega j) :
    j ∈ (stagePopulationAt q p d b m r).target := by
  simp only [stageGood25, selected, Finset.mem_filter] at hj
  exact hj.1.2.1

set_option maxHeartbeats 1000000 in
-- The selected-label repair theorem carries dependent exact-part types on all three legs.
private theorem selectedLabel_repair42 {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (epsilon : ℚ) (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b epsilon m r M B omega j)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (j : {j // j ∈ J}) :
    Restricts (stageExactITensor27 q m p d r j.val).tensor
      (copiesZ
        (repairReserve (stagePopulationAt q p d b m r).n
          (fun W => J.sup fun k => (exactPartsAt q b m p d r k W).card))
        (stageBrokenCopyZ25 q p d b epsilon m r M B omega j.val)).tensor := by
  have hjgood := hJ j.val j.property
  have heq := CExact36RepairAux.selected_repairReserve_sup_eq q m p d hd hb epsilon
    r M B omega
    J hJ j.val j.property
  have hrepair := CExact36RepairAux.repairExactGroup27 q m hq p d hd hb epsilon
    r M B omega
    j.val hjgood hn
    (fun _ => j.val) (fun _ => hjgood)
  rw [heq]
  exact Tensor3.Restricts.trans (by simpa only [stageExactITensor27] using hrepair)
    (dependentSumZ_const_restricts_copies42 _ _)

set_option maxHeartbeats 1000000 in
-- The occupied-region type unfolds six nested finite histogram families.
private theorem occupiedRegion_fresh_repair42 {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (epsilon : ℚ) (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b epsilon m r M B omega j)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hJpos : 0 < J.card) :
    ∃ j0 : (stagePopulationAt q p d b m r).Label,
      j0 ∈ (stagePopulationAt q p d b m r).target ∧
      Restricts (copiesZ J.card (stageExactITensor27 q m p d r j0)).tensor
        (copiesZ
          (repairReserve (stagePopulationAt q p d b m r).n
            (fun W => J.sup fun k => (exactPartsAt q b m p d r k W).card))
          (dependentSumZ fun j : {j // j ∈ J} =>
            stageBrokenCopyZ25 q p d b epsilon m r M B omega j.val)).tensor := by
  classical
  obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hJpos
  have hj0target := goodLabel_target42 q m M epsilon p d r B omega j0 (hJ j0 hj0)
  refine ⟨j0, hj0target, ?_⟩
  apply Tensor3.Restricts.trans
    (copiesExactLabel_restricts_sum42 q m p d r J j0 hj0target
      (fun j hj => goodLabel_target42 q m M epsilon p d r B omega j (hJ j hj)))
  apply Tensor3.Restricts.trans
    (dependentSumZ_restricts42 _ _
      (selectedLabel_repair42 q m hq p d hd hb epsilon r M B omega J hJ hn))
  exact dependentSumZ_copies_restricts_copies42 _ _

set_option maxHeartbeats 1000000 in
-- A zero-position population still has the unique empty histogram target used by the unit region.
private noncomputable def emptyStageTarget42 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (hn : (stagePopulationAt q p d b m r).n = 0) :
    {j : (stagePopulationAt q p d b m r).Label //
      j ∈ (stagePopulationAt q p d b m r).target} := by
  classical
  have hcard : Fintype.card (StageCandidateRaw.StagePos b m p d r) = 0 := by
    simpa [stagePopulationAt, StageCandidateRaw.StagePos,
      StageCandidateRaw.stageParentCount, StageCandidateRaw.stageAlphaCount] using hn
  have hparent : ∀ t, StageCandidateRaw.stageParentCount b m p d r t = 0 := by
    intro t
    by_contra hp
    have hp' : 0 < StageCandidateRaw.stageParentCount b m p d r t :=
      Nat.pos_of_ne_zero hp
    let z : StageCandidateRaw.StagePos b m p d r := ⟨t, (⟨0, hp'⟩, 0)⟩
    have hz : 0 < Fintype.card (StageCandidateRaw.StagePos b m p d r) :=
      Fintype.card_pos_iff.mpr ⟨z⟩
    omega
  have halpha : ∀ t u, StageCandidateRaw.stageAlphaCount b m p d r t u = 0 := by
    intro t u
    have hle : StageCandidateRaw.stageAlphaCount b m p d r t u ≤
        StageCandidateRaw.stageParentCount b m p d r t := by
      unfold StageCandidateRaw.stageParentCount
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    rw [hparent t] at hle
    omega
  have halphaRaw : ∀ t u, (((b * m * p.baseN t : ℕ) : ℚ) *
      (d.A t).prob r * (d.alpha t r).prob u).floor.toNat = 0 := by
    intro t u
    simpa only [StageCandidateRaw.stageAlphaCount] using halpha t u
  have hparentRaw : ∀ t, ∑ u : ChildShape p t,
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob u).floor.toNat = 0 := by
    intro t
    simpa only [StageCandidateRaw.stageParentCount,
      StageCandidateRaw.stageAlphaCount] using hparent t
  let J : (stagePopulationAt q p d b m r).Label := by
    dsimp only [stagePopulationAt]
    refine ⟨(fun z => False.elim (by
      have hp : 0 < ∑ u : ChildShape p z.1,
          (((b * m * p.baseN z.1 : ℕ) : ℚ) *
            (d.A z.1).prob r * (d.alpha z.1 r).prob u).floor.toNat :=
        Fin.pos_iff_nonempty.mpr ⟨z.2.1⟩
      rw [hparentRaw z.1] at hp
      omega)), ?_, ?_⟩
    · intro t h W a
      calc
        _ = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _
          have hp : 0 < ∑ x : ChildShape p t,
              (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
                (d.alpha t r).prob x).floor.toNat := Fin.pos_iff_nonempty.mpr ⟨i⟩
          rw [hparentRaw t] at hp
          omega
        _ = _ := by
          symm
          apply Finset.sum_eq_zero
          intro x _
          let c : Fin (2*w+1) := match W with
            | .X => (if h = 0 then x else complement p t x).val.1.1
            | .Y => (if h = 0 then x else complement p t x).val.1.2.1
            | .Z => (if h = 0 then x else complement p t x).val.1.2.2
          change (if c = a then
            (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
              (d.alpha t r).prob x).floor.toNat else 0) = 0
          by_cases hca : c = a
          · simp only [hca, if_true]
            exact halphaRaw t x
          · simp only [hca, if_false]
    · intro t i
      have hp : 0 < ∑ u : ChildShape p t,
          (((b * m * p.baseN t : ℕ) : ℚ) *
            (d.A t).prob r * (d.alpha t r).prob u).floor.toNat :=
        Fin.pos_iff_nonempty.mpr ⟨i⟩
      rw [hparentRaw t] at hp
      omega
  refine ⟨J, ?_⟩
  dsimp only [stagePopulationAt]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro t u
  calc
    _ = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _
      have hp : 0 < ∑ x : ChildShape p t,
          (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
            (d.alpha t r).prob x).floor.toNat := Fin.pos_iff_nonempty.mpr ⟨i⟩
      rw [hparentRaw t] at hp
      omega
    _ = _ := (halphaRaw t u).symm

set_option maxHeartbeats 1000000 in
-- With no positions, the exact regional tensor is the one-coefficient unit tensor.
private theorem emptyStageCopies_restricts_unit42 {w s b : ℕ}
    (q m : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (hn : (stagePopulationAt q p d b m r).n = 0) :
    Restricts
      (copiesZ 1 (stageExactITensor27 q m p d r
        (emptyStageTarget42 q m p d r hn).val)).tensor
      unitFamilyZ.tensor := by
  classical
  have hcard : Fintype.card (StageCandidateRaw.StagePos b m p d r) = 0 := by
    simpa [stagePopulationAt, StageCandidateRaw.StagePos,
      StageCandidateRaw.stageParentCount, StageCandidateRaw.stageAlphaCount] using hn
  letI : IsEmpty (StageCandidateRaw.StagePos b m p d r) :=
    Fintype.card_eq_zero_iff.mp hcard
  apply restricts_of_sub (fun _ => ()) (fun _ => ()) (fun _ => ())
  rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  have hij : i = j := Subsingleton.elim _ _
  have hik : i = k := Subsingleton.elim _ _
  subst j
  subst k
  fin_cases i
  simp [copiesZ, stageExactITensor27, stageExactTensorZ27, unitFamilyZ, famDS]

private theorem unitFamily_restricts_oneCopy42 :
    Restricts unitFamilyZ.tensor (copiesZ 1 unitFamilyZ).tensor := by
  refine ADVXXZ.restricts_of_sub (fun _ => (0, ())) (fun _ => (0, ()))
    (fun _ => (0, ())) ?_
  intro x y z
  cases x
  cases y
  cases z
  simp [unitFamilyZ, copiesZ, famDS]

set_option maxHeartbeats 2000000 in
-- Six dependent label families are repaired before any natural division is taken.
/-- Extra copies of the original plain input pay every actual regional reserve. -/
theorem constituent_fresh_repair42
    (q : ℕ) {w s b : ℕ} (hq : 0 < q) {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (epsilon : ℚ) (hepsilon : 0 ≤ epsilon)
    (m : ℕ) (h : ConstituentFullGrid27 d m epsilon)
    (P : ConstituentGridProduction29 q d hd epsilon m h.val)
    (hnonzero : ¬ ∀ x y z,
      (constituentGridTensorZ27 q d m h.val).tensor x y z = 0)
    (hselected : ∀ r : Fin 6,
      (stagePopulationAt q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b m r).n ≠ 0 →
        0 < (P.selected r).card) :
    Restricts
      (copiesZ (∏ r : Fin 6,
          if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
              (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1
          else (P.selected r).card)
        (constituentGridTensorZ27 q d m h.val)).tensor
      (copiesZ (constituentRepairPool33 q p d b m)
        (constituentPlainInputZ q p (b*m) (3*epsilon))).tensor := by
  classical
  let pg := constituentGridParent27 d hd m h.val
  let dg := constituentGridSpec27 d hd m h.val
  let count : Fin 6 → ℕ := fun r =>
    if (stagePopulationAt q pg dg b m r).n = 0 then 1 else (P.selected r).card
  let reserve : Fin 6 → ℕ := fun r => constituentRegionalReserve33 q P r
  let regionalSource : Fin 6 → ITensor := fun r =>
    if (stagePopulationAt q pg dg b m r).n = 0 then unitFamilyZ else
      dependentSumZ fun j : {j // j ∈ P.selected r} =>
        stageBrokenCopyZ25 q pg dg b epsilon m r (P.modulus r)
          (P.bucketSet r) (P.outcome r) j.val
  have hdg : ConstituentAdmissibleAt dg b := by
    apply constituent_grid_admissible28 d b m hd h.val
    apply (constituent_grid_boundary_or_zero28 q d m h.val).resolve_right
    intro hz
    apply hnonzero
    intro x y z
    exact congrFun (congrFun (congrFun hz x) y) z
  have hbg : ConstituentIntegral36 dg b m :=
    constituent_grid_integral36 d hd hb m h.val
  have hexact : ∀ r, ∃ j : (stagePopulationAt q pg dg b m r).Label,
      j ∈ (stagePopulationAt q pg dg b m r).target ∧
      Restricts (copiesZ (count r) (stageExactITensor27 q m pg dg r j)).tensor
        (copiesZ (reserve r) (regionalSource r)).tensor := by
    intro r
    by_cases hn : (stagePopulationAt q pg dg b m r).n = 0
    · let e := emptyStageTarget42 q m pg dg r hn
      refine ⟨e.val, e.property, ?_⟩
      have hc : count r = 1 := by
        dsimp only [count]
        rw [if_pos hn]
      have hr : reserve r = 1 := by
        dsimp only [reserve, constituentRegionalReserve33]
        rw [if_pos (by simpa only [pg, dg, stagePopulationAt] using hn)]
      have hs : regionalSource r = unitFamilyZ := by
        dsimp only [regionalSource]
        rw [if_pos hn]
      rw [hc, hr, hs]
      dsimp only [e]
      exact (emptyStageCopies_restricts_unit42 q m pg dg r hn).trans
        unitFamily_restricts_oneCopy42
    · have hjpos : 0 < (P.selected r).card := hselected r (by simpa [pg, dg] using hn)
      obtain ⟨j, hj, hrepair⟩ := occupiedRegion_fresh_repair42 q m hq pg dg hdg hbg
        epsilon r (P.modulus r) (P.bucketSet r) (P.outcome r) (P.selected r)
        (P.good r) hn hjpos
      refine ⟨j, hj, ?_⟩
      have hc : count r = (P.selected r).card := by
        dsimp only [count]
        rw [if_neg hn]
      have hr : reserve r = repairReserve (stagePopulationAt q pg dg b m r).n
          (fun W => (P.selected r).sup fun k =>
            (exactPartsAt q b m pg dg r k W).card) := by
        dsimp only [reserve, constituentRegionalReserve33]
        rw [if_neg (by simpa only [pg, dg, stagePopulationAt] using hn)]
      have hs : regionalSource r = dependentSumZ fun j : {j // j ∈ P.selected r} =>
          stageBrokenCopyZ25 q pg dg b epsilon m r (P.modulus r)
            (P.bucketSet r) (P.outcome r) j.val := by
        dsimp only [regionalSource]
        rw [if_neg hn]
      rw [hc, hr, hs]
      exact hrepair
  choose j hj hregional using hexact
  have hout := CExact36RepairAux.repairSixRegionOutput27 q m pg dg hdg hbg j hj
  have hcopy : Restricts
      (copiesZ (∏ r, count r) (constituentGridTensorZ27 q d m h.val)).tensor
      (copiesZ (∏ r, count r) (constituentOutputZ q dg m 0)).tensor :=
    copiesZ_restricts33 _ _ _ (constituent_grid_output_restricts36 q d hd m h.val)
  have htoRegions : Restricts
      (copiesZ (∏ r, count r) (constituentOutputZ q dg m 0)).tensor
      (regionProductZ fun r => copiesZ (count r)
        (stageExactITensor27 q m pg dg r (j r))).tensor :=
    (copiesZ_restricts33 _ _ _ hout).trans
      (CExact36RepairAux.copiesZ_regionProductZ_restricts count
        (fun r => stageExactITensor27 q m pg dg r (j r)))
  have hregions : Restricts
      (regionProductZ fun r => copiesZ (count r)
        (stageExactITensor27 q m pg dg r (j r))).tensor
      (regionProductZ fun r => copiesZ (reserve r) (regionalSource r)).tensor :=
    regionProductZ_restricts33 _ _ hregional
  have hregroup : Restricts
      (regionProductZ fun r => copiesZ (reserve r) (regionalSource r)).tensor
      (copiesZ (∏ r, reserve r) (regionProductZ regionalSource)).tensor :=
    regionProductZ_copies_restricts_copies42 reserve regionalSource
  have hvalid : goodBrokenFamilyZ25 q pg dg b epsilon m P.modulus P.bucketSet
      P.outcome P.selected = regionProductZ regionalSource := by
    simpa only [regionalSource] using goodBrokenFamilyZ25_valid_eq q pg dg b epsilon m
      P.modulus P.bucketSet P.outcome P.selected P.valid
  have hbroken : Restricts
      (copiesZ (∏ r, reserve r) (regionProductZ regionalSource)).tensor
      (copiesZ (∏ r, reserve r)
        (goodBrokenFamilyZ25 q pg dg b epsilon m P.modulus P.bucketSet
          P.outcome P.selected)).tensor := by
    rw [hvalid]
    exact ADVXXZ.restricts_of_sub id id id (fun _ _ _ => rfl)
  have hdom : ∏ r, reserve r ≤ constituentRepairPool33 q p d b m := by
    simpa only [reserve] using constituent_reserve_pool_dominated33 q P
  have hmore : Restricts
      (copiesZ (∏ r, reserve r)
        (goodBrokenFamilyZ25 q pg dg b epsilon m P.modulus P.bucketSet
          P.outcome P.selected)).tensor
      (copiesZ (constituentRepairPool33 q p d b m)
        (goodBrokenFamilyZ25 q pg dg b epsilon m P.modulus P.bucketSet
          P.outcome P.selected)).tensor := by
    simpa only [copiesZ] using OmegaBound.ADVXXZStage.famDS_copies_mono
      (R := ℤ) hdom
      (goodBrokenFamilyZ25 q pg dg b epsilon m P.modulus P.bucketSet
        P.outcome P.selected).tensor
  have hsource := copiesZ_restricts33 (constituentRepairPool33 q p d b m) _ _
    P.source_to_broken
  have hwindow := copiesZ_restricts33 (constituentRepairPool33 q p d b m) _ _
    (constituent_grid_input_window36 q d hd epsilon hepsilon m h)
  simpa only [count, pg, dg] using hcopy.trans
    (htoRegions.trans (hregions.trans (hregroup.trans
      (hbroken.trans (hmore.trans (hsource.trans hwindow))))))

end
end OmegaBound.ADVXXZGeneral
end
