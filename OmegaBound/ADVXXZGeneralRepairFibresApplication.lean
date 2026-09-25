import OmegaBound.ADVXXZGeneralRepairFibresFinal
import OmegaBound.ADVXXZEpsCnt

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

private noncomputable def fibreSequence27
    {I A C : Type} [Fintype I] [Fintype A] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq C] [Nonempty C]
    (c : I → A) (k : A → C → ℕ)
    (hsum : ∀ a, ∑ x, k a x = Nat.card {i : I // c i = a}) (a : A) :
    Fin (Nat.card {i : I // c i = a}) → C :=
  Classical.choose (ADVXXZEps.exists_typeCnt_eq (k a) (hsum a))

private theorem fibreSequence27_spec
    {I A C : Type} [Fintype I] [Fintype A] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq C] [Nonempty C]
    (c : I → A) (k : A → C → ℕ)
    (hsum : ∀ a, ∑ x, k a x = Nat.card {i : I // c i = a}) (a : A) (x : C) :
    OmegaBound.ADVXXZ.typeCnt (fibreSequence27 c k hsum a) x = k a x :=
  Classical.choose_spec (ADVXXZEps.exists_typeCnt_eq (k a) (hsum a)) x

private noncomputable def fibreWord27
    {I A C : Type} [Fintype I] [Fintype A] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq C] [Nonempty C]
    (c : I → A) (k : A → C → ℕ)
    (hsum : ∀ a, ∑ x, k a x = Nat.card {i : I // c i = a}) : I → C :=
  fun i => fibreSequence27 c k hsum (c i)
    (Finite.equivFin {j : I // c j = c i} ⟨i, rfl⟩)

private theorem fibreWord27_apply
    {I A C : Type} [Fintype I] [Fintype A] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq C] [Nonempty C]
    (c : I → A) (k : A → C → ℕ)
    (hsum : ∀ a, ∑ x, k a x = Nat.card {i : I // c i = a})
    (a : A) (i : {i : I // c i = a}) :
    fibreWord27 c k hsum i.val =
      fibreSequence27 c k hsum a (Finite.equivFin _ i) := by
  rcases i with ⟨i, hi⟩
  subst a
  rfl

private theorem fibreWord27_histogram
    {I A C : Type} [Fintype I] [Fintype A] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq C] [Nonempty C]
    (c : I → A) (k : A → C → ℕ)
    (hsum : ∀ a, ∑ x, k a x = Nat.card {i : I // c i = a}) (a : A) (x : C) :
    histogram27 (fun i => (c i, fibreWord27 c k hsum i)) (a, x) = k a x := by
  classical
  let e := Finite.equivFin {i : I // c i = a}
  have hcard :
      (Finset.univ.filter fun i : I =>
        (c i, fibreWord27 c k hsum i) = (a, x)).card =
      (Finset.univ.filter fun z : Fin (Nat.card {i : I // c i = a}) =>
        fibreSequence27 c k hsum a z = x).card := by
    refine Finset.card_bij (fun i hi => e ⟨i, congrArg Prod.fst
      (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
    · intro i hi
      have hp := (Finset.mem_filter.mp hi).2
      have hc : c i = a := congrArg Prod.fst hp
      have hx : fibreWord27 c k hsum i = x := congrArg Prod.snd hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [fibreWord27_apply c k hsum a ⟨i, hc⟩] at hx
      simpa only [e] using hx
    · intro i₁ hi₁ i₂ hi₂ he
      have he' : e ⟨i₁, congrArg Prod.fst (Finset.mem_filter.mp hi₁).2⟩ =
          e ⟨i₂, congrArg Prod.fst (Finset.mem_filter.mp hi₂).2⟩ := he
      exact congrArg Subtype.val (e.injective he')
    · intro z hz
      let iz := (e.symm z).val
      have hc : c iz = a := (e.symm z).property
      have hx : fibreSequence27 c k hsum a z = x := (Finset.mem_filter.mp hz).2
      have hiz : (⟨iz, hc⟩ : {i : I // c i = a}) = e.symm z := Subtype.ext rfl
      have hez : Finite.equivFin {i : I // c i = a} ⟨iz, hc⟩ = z := by
        change e ⟨iz, hc⟩ = z
        rw [hiz, e.apply_symm_apply]
      refine ⟨iz, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Prod.ext hc ?_⟩
        rw [fibreWord27_apply c k hsum a ⟨iz, hc⟩]
        rw [hez]
        exact hx
      · exact hez
  unfold histogram27
  rw [hcard]
  exact fibreSequence27_spec c k hsum a x

theorem partitionExact_nonempty27
    {T : Type} [Fintype T] [DecidableEq T]
    {I A : T → Type} [∀ t, Fintype (I t)] [∀ t, DecidableEq (I t)]
    [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)] {w : ℕ}
    (c : (t : T) → I t → A t) (shape : (t : T) → A t → Shape w)
    (counts : Side → (t : T) → A t → Chunk w → ℕ) (W : Side)
    (hsum : ∀ t u, ∑ σ, counts W t u σ = Nat.card {i : I t // c t i = u})
    (hlevel : ∀ t u σ, 0 < counts W t u σ →
      chunkLvl σ = coord W (shape t u)) :
    Nonempty (PartitionPart27 c shape counts W) := by
  classical
  let a : PartitionWord27 (I := I) (w := w) := fun z =>
    fibreWord27 (c z.1) (counts W z.1) (hsum z.1) z.2
  refine ⟨⟨a, ?_⟩⟩
  constructor
  · intro t i
    let u := c t i
    let σ := fibreWord27 (c t) (counts W t) (hsum t) i
    have hpos : 0 < histogram27
        (fun z => (c t z, fibreWord27 (c t) (counts W t) (hsum t) z)) (u, σ) := by
      unfold histogram27
      apply Finset.card_pos.mpr
      refine ⟨i, ?_⟩
      simp [u, σ]
    have hc : 0 < counts W t u σ := by
      rw [← fibreWord27_histogram (c t) (counts W t) (hsum t) u σ]
      exact hpos
    exact hlevel t u σ hc
  · intro t u σ
    exact fibreWord27_histogram (c t) (counts W t) (hsum t) u σ

private theorem rat_floor_nat27 (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem stageAlphaCount_cast27 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (m : ℕ) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) :
    (((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u).floor.toNat : ℕ) : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u := by
  rcases ((hb.2 t r).2 u).1 with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u =
        ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) * ((b : ℚ) * p.baseN t * (d.A t).prob r *
          (d.alpha t r).prob u) := by push_cast; ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  rw [hscaled, rat_floor_nat27]

private theorem stageCounts27_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (m : ℕ) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ := by
  rcases ((hb.2 t r).2 u).2.2 W σ with ⟨n, hn⟩
  have hscaled :
      (((m * d.outBase ⟨t,r,u⟩ : ℕ) : ℚ) *
          (d.betaChild W t r u).prob σ) = ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) * ((d.outBase ⟨t,r,u⟩ : ℚ) *
          (d.betaChild W t r u).prob σ) := by push_cast; ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  unfold stageCounts27
  rw [hscaled, rat_floor_nat27]
  calc
    ((m * n : ℕ) : ℚ) = (m : ℚ) * n := by norm_cast
    _ = (m : ℚ) * ((d.outBase ⟨t,r,u⟩ : ℚ) *
        (d.betaChild W t r u).prob σ) := congrArg (fun x : ℚ => (m : ℚ) * x) hn.symm
    _ = (m : ℚ) * d.outBase ⟨t,r,u⟩ *
        (d.betaChild W t r u).prob σ := by ring

theorem stageCounts27_sum {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : StepIntegralAt p d b) (m : ℕ) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) :
    ∑ σ, stageCounts27 m p d r W t u σ = m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sum]
  simp_rw [stageCounts27_cast p d hb m r W t u]
  rw [← Finset.mul_sum, RatDist.sum_prob]
  push_cast
  ring

theorem stageAlphaPair27 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (m : ℕ) (r : Fin 6) (t : Fin s) (u : ChildShape p t) :
    ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u).floor.toNat +
      ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob (complement p t u)).floor.toNat)) =
      m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_add, stageAlphaCount_cast27 p d hb m r t u,
    stageAlphaCount_cast27 p d hb m r t (complement p t u)]
  push_cast
  rw [hd.out_eq t r u]
  ring

private theorem prod_fin2_filter_card27 {I : Type} [Fintype I]
    (P : I × Fin 2 → Prop) :
    (by classical exact (Finset.univ.filter P).card) =
      (by classical exact (Finset.univ.filter fun i : I => P (i, 0)).card) +
        (by classical exact (Finset.univ.filter fun i : I => P (i, 1)).card) := by
  classical
  have hfiber : ∀ h : Fin 2,
      ((Finset.univ.filter P).filter fun ih => ih.2 = h).card =
        (Finset.univ.filter fun i : I => P (i, h)).card := by
    intro h
    refine Finset.card_bij (fun ih _ => ih.1) ?_ ?_ ?_
    · intro ih hih
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hih).1).2
          have hh := (Finset.mem_filter.mp hih).2
          have hi : (ih.1, h) = ih := Prod.ext rfl hh.symm
          exact hi.symm ▸ hp⟩
    · intro ih₁ hi₁ ih₂ hi₂ heq
      apply Prod.ext heq
      exact ((Finset.mem_filter.mp hi₁).2).trans ((Finset.mem_filter.mp hi₂).2).symm
    · intro i hi
      refine ⟨(i, h), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ih : I × Fin 2 => ih.2)
    (s := Finset.univ.filter P) (t := (Finset.univ : Finset (Fin 2)))]
  · rw [Fin.sum_univ_two]
    rw [hfiber 0, hfiber 1]
  · intro ih _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)

private def transportedStageHoles27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    Finset (StageExactPart27 q b m p d r j W) :=
  (stageExactHoles27 q b m M ε p d r B ω k W).map
    (labelExactPartEquiv27 q m p d r j k hj hk W).symm.toEmbedding

private theorem stageExactHoles27_card {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    (stageExactHoles27 q b m M ε p d r B ω j W).card =
      (holesAt25 q b m M ε p d r B ω j W).card := by
  classical
  apply Finset.card_bij (fun a _ => a.val)
  · intro a ha
    simpa [stageExactHoles27] using ha
  · intro a₁ h₁ a₂ h₂ h
    exact Subtype.ext h
  · intro a ha
    have hexact : a ∈ exactPartsAt q b m p d r j W := by
      have hmem : a ∈ exactPartsAt q b m p d r j W ∧
          ¬ stagePartKeepAt25 q b m M ε p d r B ω .zUseful W a := by
        simpa only [holesAt25, Finset.mem_filter] using ha
      exact hmem.1
    refine ⟨⟨a, hexact⟩, ?_, rfl⟩
    simp [stageExactHoles27, ha]

private theorem transportedStageHoles27_card {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    (transportedStageHoles27 q m M ε p d r B ω j k hj hk W).card =
      (holesAt25 q b m M ε p d r B ω k W).card := by
  rw [transportedStageHoles27, Finset.card_map, stageExactHoles27_card]

private theorem mem_transportedStageHoles27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side)
    (a : StageExactPart27 q b m p d r j W) :
    a ∈ transportedStageHoles27 q m M ε p d r B ω j k hj hk W ↔
      (labelExactPartEquiv27 q m p d r j k hj hk W a).val ∈
        holesAt25 q b m M ε p d r B ω k W := by
  simp [transportedStageHoles27, stageExactHoles27]

end
end OmegaBound.ADVXXZGeneral
end
