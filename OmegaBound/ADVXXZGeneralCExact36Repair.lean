import OmegaBound.ADVXXZGeneralCExact36GridPartition
import OmegaBound.ADVXXZGeneralCExact36Embedding
import OmegaBound.ADVXXZGeneralRepairFibresAssembly

set_option autoImplicit false

section
universe u v
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
namespace CExact36RepairAux
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/- The private combinatorial helpers of `ADVXXZGeneralCoarseTransportParent25` use neither
admissibility nor `StepIntegralAt`.  Expose three of them, already kernel-checked. -/
open Lean Elab Command in
private def findCoarseTransportPrivate36
    (env : Environment) (suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains "_private.OmegaBound.ADVXXZGeneralCoarseTransportParent25." ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then
    return names[0]
  else
    throwError "expected one coarse-transport declaration ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_coarse_transport36 " id:ident " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findCoarseTransportPrivate36 env suffix.getString
  let newName := (← getCurrNamespace) ++ id.getId
  let some info := env.find? oldName | throwError "coarse-transport declaration vanished"
  let value := mkConst oldName (info.levelParams.map Level.param)
  match info with
  | .defnInfo d =>
      liftCoreM <| addDecl <| .defnDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value
        hints := d.hints
        safety := d.safety
      }
  | .thmInfo d =>
      liftCoreM <| addDecl <| .thmDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value
      }
  | _ => throwError "unsupported coarse-transport declaration kind for {oldName}"

expose_coarse_transport36 coarseAmbientPartEquiv36 :=
  ".OmegaBound.ADVXXZGeneral.ambientPartEquiv"
expose_coarse_transport36 coarseRepresentedPartsEquiv36 :=
  ".OmegaBound.ADVXXZGeneral.representedPartsEquiv"
expose_coarse_transport36 coarseParentCompatibleLabelsCard36 :=
  ".OmegaBound.ADVXXZGeneral.parentCompatibleLabels_card"

theorem coarse_transport_parent36 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (J K : AlphaLabel p d b m r) (W : Side) :
  ∃ e : RepresentedParts p d b m J W ≃ RepresentedParts p d b m K W,
    ∀ x, Parent25.compatibleDegree p d b m K W (e x) =
      Parent25.compatibleDegree p d b m J W x := by
  classical
  let e := coarseRepresentedPartsEquiv36 p d r J K W
  refine ⟨e, ?_⟩
  intro x
  change (Parent25.compatibleLabels p d b m r W
      (coarseAmbientPartEquiv36 p d r J K W x.1)).card =
    (Parent25.compatibleLabels p d b m r W x.1).card
  exact coarseParentCompatibleLabelsCard36 p d r J K W x.1

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
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
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
  obtain ⟨e, _he⟩ := coarse_transport_parent36 q m p d r J K W
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
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
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

set_option maxHeartbeats 1000000 in
-- This repeats the dependent stage-family envelope of the maximum transport above.
/-- The reserve appearing in `stageRepairedCount` is the reserve of any selected label. -/
theorem selected_repairReserve_sup_eq {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
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
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) :
    (((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u).floor.toNat : ℕ) : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u := by
  rcases hb.alphaIntegral t r u with ⟨n, hn⟩
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
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ :=
  hb.countsExact r W t u σ

theorem stageCounts27_sum {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) :
    ∑ σ, stageCounts27 m p d r W t u σ = m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sum]
  simp_rw [stageCounts27_cast p d m hb r W t u]
  rw [← Finset.mul_sum, RatDist.sum_prob]
  push_cast
  ring

theorem stageAlphaPair27 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ)
    (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) (u : ChildShape p t) :
    ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u).floor.toNat +
      ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob (complement p t u)).floor.toNat)) =
      m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_add, stageAlphaCount_cast27 p d m hb r t u,
    stageAlphaCount_cast27 p d m hb r t (complement p t u)]
  push_cast
  rw [hd.out_eq t r u]
  ring

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Split a predicate fibre on `I × Fin 2` into its two literal half fibres. -/
def twoHalfFibreEquiv27 {I : Type} (P : I × Fin 2 → Prop) :
    {x : I × Fin 2 // P x} ≃
      {i : I // P (i, 0)} ⊕ {i : I // P (i, 1)} where
  toFun x := if h : x.val.2 = 0 then
    Sum.inl ⟨x.val.1, by
      have hx : x.val = (x.val.1, 0) := Prod.ext rfl h
      exact hx ▸ x.property⟩
  else
    Sum.inr ⟨x.val.1, by
      have h1 : x.val.2 = 1 := Fin.eq_one_of_ne_zero x.val.2 h
      have hx : x.val = (x.val.1, 1) := Prod.ext rfl h1
      exact hx ▸ x.property⟩
  invFun x := x.elim
    (fun i => ⟨(i.val, 0), i.property⟩)
    (fun i => ⟨(i.val, 1), i.property⟩)
  left_inv x := by
    rcases x with ⟨⟨i, h⟩, hx⟩
    apply Subtype.ext
    fin_cases h <;> rfl
  right_inv x := by
    rcases x with x | x <;> rfl

private noncomputable def stageWholeFibreFintype27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    Fintype {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} :=
  Fintype.ofFinite _

private noncomputable def stageWholeFibreDecidableEq27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    DecidableEq {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} :=
  Classical.decEq _

private noncomputable def stageHalfFibreFintype27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (h : Fin 2) :
    Fintype {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, h) = u} :=
  Fintype.ofFinite _

private noncomputable def stageHalfFibreDecidableEq27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (h : Fin 2) :
    DecidableEq {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, h) = u} :=
  Classical.decEq _

set_option maxHeartbeats 1000000 in
-- Target membership unfolds the dependent raw-population label only at this boundary.
private theorem stageTargetHalfZeroCard27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 0) = u}
      (stageHalfFibreFintype27 q m p d r j t u 0) =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob u).floor.toNat := by
  letI := stageHalfFibreFintype27 q m p d r j t u 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 0
  rw [Fintype.card_subtype]
  have h := (Finset.mem_filter.mp hj).2 t u
  simpa only [stageColour27] using h

set_option maxHeartbeats 1000000 in
-- The label complementarity projection has the same dependent stage-label envelope.
private def stageHalfOneComplementEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 1) = u} ≃
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 0) = complement p t u} where
  toFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 0)⟩ = complement p t u
    calc
      j.val ⟨t, (i.val, 0)⟩ =
          complement p t (complement p t (j.val ⟨t, (i.val, 0)⟩)) :=
        (OmegaBound.ADVXXZPaper.complement_complement t _).symm
      _ = complement p t (j.val ⟨t, (i.val, 1)⟩) :=
        (congrArg (complement p t) hc).symm
      _ = complement p t u := congrArg (complement p t) i.property⟩
  invFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 1)⟩ = u
    calc
      j.val ⟨t, (i.val, 1)⟩ = complement p t (j.val ⟨t, (i.val, 0)⟩) := hc
      _ = complement p t (complement p t u) :=
        congrArg (complement p t) i.property
      _ = u := OmegaBound.ADVXXZPaper.complement_complement t u⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

set_option maxHeartbeats 1000000 in
-- Applying the half-zero result at the complementary child retains that envelope.
private theorem stageTargetHalfOneCard27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 1) = u}
      (stageHalfFibreFintype27 q m p d r j t u 1) =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r *
          (d.alpha t r).prob (complement p t u)).floor.toNat := by
  letI := stageHalfFibreFintype27 q m p d r j t u 1
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 1
  letI := stageHalfFibreFintype27 q m p d r j t (complement p t u) 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t (complement p t u) 0
  calc
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 1) = u} =
        Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
          stageColour27 q b m p d r j t (i, 0) = complement p t u} :=
      Fintype.card_congr (stageHalfOneComplementEquiv27 q m p d r j t u)
    _ = _ := stageTargetHalfZeroCard27 q m p d r j hj t (complement p t u)

set_option maxHeartbeats 1000000 in
-- The result type contains the target label and its explicitly fixed fibre instances.
/-- A target label uses exactly `m * outBase` positions of each child colour across both halves. -/
theorem stageTargetFibre_card27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
        stageColour27 q b m p d r j t i = u}
      (stageWholeFibreFintype27 q m p d r j t u) =
      m * d.outBase ⟨t, r, u⟩ := by
  letI := stageWholeFibreFintype27 q m p d r j t u
  letI := stageWholeFibreDecidableEq27 q m p d r j t u
  letI := stageHalfFibreFintype27 q m p d r j t u 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 0
  letI := stageHalfFibreFintype27 q m p d r j t u 1
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 1
  calc
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
        stageColour27 q b m p d r j t i = u} =
        Fintype.card
          ({i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 0) = u} ⊕
            {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 1) = u}) :=
      Fintype.card_congr (twoHalfFibreEquiv27
        (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
          stageColour27 q b m p d r j t i = u))
    _ = Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 0) = u} +
        Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 1) = u} := Fintype.card_sum
    _ = (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob u).floor.toNat +
        (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob (complement p t u)).floor.toNat :=
      congrArg₂ (fun x y : ℕ => x + y)
        (stageTargetHalfZeroCard27 q m p d r j hj t u)
        (stageTargetHalfOneCard27 q m p d r j hj t u)
    _ = m * d.outBase ⟨t, r, u⟩ := stageAlphaPair27 p d hd m hb r t u

set_option maxHeartbeats 1000000 in
-- The exact-part equivalence repeats the dependent stage label in every partition parameter.
/-- Every target label has a realized exact part alphabet on each physical side. -/
theorem stageExactPart_nonempty27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    Nonempty (StageExactPart27 q b m p d r j W) := by
  letI stagePositionFintype27 :
      ∀ t : Fin s,
        Fintype (Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :=
    fun _ => inferInstance
  letI stagePositionDecidableEq27 :
      ∀ t : Fin s,
        DecidableEq (Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :=
    fun _ => inferInstance
  letI childShapeFintype27 : ∀ t : Fin s, Fintype (ChildShape p t) :=
    fun _ => inferInstance
  letI childShapeDecidableEq27 : ∀ t : Fin s, DecidableEq (ChildShape p t) :=
    fun _ => inferInstance
  have hsum : ∀ t u,
      ∑ σ, stageCounts27 m p d r W t u σ =
        Nat.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
          stageColour27 q b m p d r j t i = u} := by
    intro t u
    rw [stageCounts27_sum p d m hb r W t u]
    letI := stageWholeFibreFintype27 q m p d r j t u
    letI := stageWholeFibreDecidableEq27 q m p d r j t u
    rw [Nat.card_eq_fintype_card]
    exact (stageTargetFibre_card27 q m p d hd hb r j hj t u).symm
  have hlevel : ∀ t u σ, 0 < stageCounts27 m p d r W t u σ →
      chunkLvl σ = coord W u.val := by
    intro t u σ hpos
    apply hd.child_support W t r u σ
    intro hzero
    have hcount : stageCounts27 m p d r W t u σ = 0 := by
      unfold stageCounts27
      rw [show (d.betaChild W t r u).prob σ = 0 by
        simp [RatDist.prob, hzero]]
      simp only [mul_zero]
      change ((((0 : ℤ) : ℚ).floor).toNat) = 0
      rw [Rat.floor_intCast]
      exact Int.toNat_zero
    omega
  obtain ⟨a⟩ := partitionExact_nonempty27
    (stageColour27 q b m p d r j) (fun _ u => u.val)
    (stageCounts27 m p d r) W hsum hlevel
  exact ⟨(stagePartEquiv27 q b m p d r j W).symm a⟩

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The exact physical tensor attached to one target label, packaged with its three leg types. -/
def stageExactITensor27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) : ITensor :=
  { X := StageExactLeg27 q b m p d r j .X
    Y := StageExactLeg27 q b m p d r j .Y
    Z := StageExactLeg27 q b m p d r j .Z
    tensor := stageExactTensorZ27 q b m p d r j }

private theorem goodLabel_target27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : stageGood25 q p d b ε m r M B ω j) :
    j ∈ (stagePopulationAt q p d b m r).target := by
  simp only [stageGood25, selected, Finset.mem_filter] at hj
  exact hj.1.2.1

/-- The numeric position of a member of a full quotient group in the retained prefix. -/
def repairGroupIndex27 (good copies reserve : ℕ) (hprefix : copies * reserve ≤ good) :
    Fin copies × Fin reserve → Fin good := fun gi =>
  Fin.castLE hprefix (finProdFinEquiv gi)


/-- The first `copies * reserve` elements of a finite selected family, indexed by full groups. -/
def repairGroupLabel27 {L : Type*} [Fintype L] [DecidableEq L]
    (J : Finset L) (copies reserve : ℕ) (hprefix : copies * reserve ≤ J.card) :
    Fin copies × Fin reserve → {j // j ∈ J} := fun gi =>
  let e : Fin J.card ≃ {j // j ∈ J} :=
    (finCongr (Fintype.card_coe J).symm).trans (Fintype.equivFin {j // j ∈ J}).symm
  e (repairGroupIndex27 J.card copies reserve hprefix gi)

theorem repairGroupLabel27_injective {L : Type*} [Fintype L] [DecidableEq L]
    (J : Finset L) (copies reserve : ℕ) (hprefix : copies * reserve ≤ J.card) :
    Function.Injective (repairGroupLabel27 J copies reserve hprefix) := by
  intro a b hab
  apply finProdFinEquiv.injective
  apply Fin.castLE_injective hprefix
  exact ((finCongr (Fintype.card_coe J).symm).trans
    (Fintype.equivFin {j // j ∈ J}).symm).injective hab

private def transportedStageHolesAssembly27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    Finset (StageExactPart27 q b m p d r j W) :=
  (stageExactHoles27 q b m M ε p d r B ω k W).map
    (labelExactPartEquiv27 q m p d r j k hj hk W).symm.toEmbedding

private theorem stageExactHolesAssembly27_card {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
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

private theorem transportedStageHolesAssembly27_card {w s b : ℕ}
    (q m M : ℕ) (ε : ℚ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    (transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk W).card =
      (holesAt25 q b m M ε p d r B ω k W).card := by
  rw [transportedStageHolesAssembly27, Finset.card_map,
    stageExactHolesAssembly27_card]

private theorem mem_transportedStageHolesAssembly27 {w s b : ℕ}
    (q m M : ℕ) (ε : ℚ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side)
    (a : StageExactPart27 q b m p d r j W) :
    a ∈ transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk W ↔
      (labelExactPartEquiv27 q m p d r j k hj hk W a).val ∈
        holesAt25 q b m M ε p d r B ω k W := by
  simp [transportedStageHolesAssembly27, stageExactHoles27]

private theorem boxZO_restricts_subtypeAssembly27
    {R X Y Z PX PY PZ : Type*} [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
    (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ)
    (A : Finset PX) (C : Finset PY) (E : Finset PZ) (T : Tensor3 R X Y Z) :
    Restricts (boxZO pX pY pZ A C E T)
      (fun x : {x // pX x ∈ A} => fun y : {y // pY y ∈ C} =>
        fun z : {z // pZ z ∈ E} => T x.val y.val z.val) := by
  classical
  refine ⟨(fun x x' => if x'.val = x then 1 else 0),
    (fun y y' => if y'.val = y then 1 else 0),
    (fun z z' => if z'.val = z then 1 else 0), ?_⟩
  funext x y z
  simp only [Tensor3.act]
  by_cases hx : pX x ∈ A
  · rw [Finset.sum_eq_single ⟨x, hx⟩]
    · by_cases hy : pY y ∈ C
      · rw [Finset.sum_eq_single ⟨y, hy⟩]
        · by_cases hz : pZ z ∈ E
          · rw [Finset.sum_eq_single ⟨z, hz⟩]
            · simp [boxZO, hx, hy, hz]
            · intro z' _ hz'
              have hne : z'.val ≠ z := fun h => hz' (Subtype.ext h)
              simp [hne]
            · intro h
              exact (h (Finset.mem_univ (⟨z, hz⟩ : {z // pZ z ∈ E}))).elim
          · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hz]]
            symm
            apply Finset.sum_eq_zero
            intro z' _
            have hne : z'.val ≠ z := fun h => hz (h ▸ z'.property)
            simp [hne]
        · intro y' _ hy'
          rw [Finset.sum_eq_zero]
          intro z' _
          have hne : y'.val ≠ y := fun h => hy' (Subtype.ext h)
          simp [hne]
        · intro h
          exact (h (Finset.mem_univ (⟨y, hy⟩ : {y // pY y ∈ C}))).elim
      · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hy]]
        symm
        apply Finset.sum_eq_zero
        intro y' _
        apply Finset.sum_eq_zero
        intro z' _
        have hne : y'.val ≠ y := fun h => hy (h ▸ y'.property)
        simp [hne]
    · intro x' _ hx'
      rw [Finset.sum_eq_zero]
      intro y' _
      rw [Finset.sum_eq_zero]
      intro z' _
      have hne : x'.val ≠ x := fun h => hx' (Subtype.ext h)
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ (⟨x, hx⟩ : {x // pX x ∈ A}))).elim
  · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hx]]
    symm
    apply Finset.sum_eq_zero
    intro x' _
    apply Finset.sum_eq_zero
    intro y' _
    apply Finset.sum_eq_zero
    intro z' _
    have hne : x'.val ≠ x := fun h => hx (h ▸ x'.property)
    simp [hne]

private abbrev StageBrokenLegAssembly27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (k : (stagePopulationAt q p d b m r).Label) (W : Side) :=
  {x : StagePhysicalWord q p d b m r //
    (stagePopulationAt q p d b m r).incidence W k
        (stagePhysicalPart q p d b m r W x) ∧
      stagePhysicalPart q p d b m r W x ∉
        holesAt25 q b m M ε p d r B ω k W}

private def stageBrokenLegEquivAssembly27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (k : (stagePopulationAt q p d b m r).Label) (W : Side) :
    StageBrokenLegAssembly27 q m M ε p d r B ω k W ≃
      (stageBrokenCopyZ25 q p d b ε m r M B ω k).leg W := by
  cases W <;> exact Equiv.refl _

private def stageBoxToBrokenLegAssembly27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    {x : StageExactLeg27 q b m p d r j W //
      stageExactPart27 q b m p d r j W x ∈
        (transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk W)ᶜ} →
      (stageBrokenCopyZ25 q p d b ε m r M B ω k).leg W := by
  intro x
  let y := labelExactLegEquiv27 q m p d r j k hj hk W x.val
  have hnotRef : stageExactPart27 q b m p d r j W x.val ∉
      transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk W := by
    simpa using x.property
  have hnot : stagePhysicalPart q p d b m r W y.val ∉
      holesAt25 q b m M ε p d r B ω k W := by
    intro hmem
    apply hnotRef
    apply (mem_transportedStageHolesAssembly27 q m M ε p d r B ω
      j k hj hk W (stageExactPart27 q b m p d r j W x.val)).2
    rw [labelExactPart_comm27 q m p d r j k hj hk W x.val]
    exact hmem
  have hinc : (stagePopulationAt q p d b m r).incidence W k
      (stagePhysicalPart q p d b m r W y.val) := by
    have := y.property
    simpa [exactPartsAt] using this
  exact stageBrokenLegEquivAssembly27 q m M ε p d r B ω k W ⟨y.val, hinc, hnot⟩

set_option maxHeartbeats 1000000 in
/-- A transported common-box summand is a restriction of its label-specific physical broken copy. -/
theorem stageCommonBox_restricts_broken27 {w s b : ℕ} (q m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j k : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (hk : k ∈ (stagePopulationAt q p d b m r).target) :
    Restricts
      (boxZO (stageExactPart27 q b m p d r j .X)
        (stageExactPart27 q b m p d r j .Y)
        (stageExactPart27 q b m p d r j .Z)
        (transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .X)ᶜ
        (transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .Y)ᶜ
        (transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .Z)ᶜ
        (stageExactTensorZ27 q b m p d r j))
      (stageBrokenCopyZ25 q p d b ε m r M B ω k).tensor := by
  let HX := transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .X
  let HY := transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .Y
  let HZ := transportedStageHolesAssembly27 q m M ε p d r B ω j k hj hk .Z
  have hbox := boxZO_restricts_subtypeAssembly27
    (stageExactPart27 q b m p d r j .X)
    (stageExactPart27 q b m p d r j .Y)
    (stageExactPart27 q b m p d r j .Z) HXᶜ HYᶜ HZᶜ
    (stageExactTensorZ27 q b m p d r j)
  refine Tensor3.Restricts.trans hbox (ADVXXZ.restricts_of_sub
    (stageBoxToBrokenLegAssembly27 q m M ε p d r B ω j k hj hk .X)
    (stageBoxToBrokenLegAssembly27 q m M ε p d r B ω j k hj hk .Y)
    (stageBoxToBrokenLegAssembly27 q m M ε p d r B ω j k hj hk .Z) ?_)
  intro x y z
  simpa only [stageBrokenCopyZ25, stageBoxToBrokenLegAssembly27,
    stageBrokenLegEquivAssembly27, ITensor.leg] using
      (labelExactTensor_equiv27 q m p d r j k hj hk x.val y.val z.val).symm

set_option maxHeartbeats 1000000 in
-- Dependent sigma-leg sums require normalization after all three index equalities are split.
private theorem famDS_restricts_dependentSumAssembly27
    {X' Y' Z' ι : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype ι] [DecidableEq ι]
    (Bf : ι → Tensor3 ℤ X' Y' Z') (T : ι → ITensor)
    (h : ∀ i, Restricts (Bf i) (T i).tensor) :
    Restricts (famDS (Finset.univ : Finset ι) Bf) (dependentSumZ T).tensor := by
  classical
  choose A₁ A₂ A₃ hA using h
  refine ⟨fun p q => if hq : q.1 = p.1 then A₁ p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A₂ p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A₃ p.1 p.2 (hq ▸ q.2) else 0, ?_⟩
  funext p q r
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  obtain ⟨k, z⟩ := r
  by_cases hij : i = j
  · subst hij
    by_cases hjk : i = k
    · subst hjk
      have hv := congrFun (congrFun (congrFun (hA i) x) y) z
      simp only [famDS, Finset.mem_univ, and_self, if_true]
      rw [hv]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      simp
    · simp only [famDS, true_and, Finset.mem_univ, and_true, hjk, if_false]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      have hki : k ≠ i := Ne.symm hjk
      simp [hjk, hki]
  · simp only [famDS, hij, false_and, if_false]
    simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]
    intro hkj hki
    exact (hij (hki.symm.trans hkj)).elim

private theorem sum_side_three27 (f : Side → ℕ) :
    ∑ W, f W = f .X + f .Y + f .Z := by
  rw [show (Finset.univ : Finset Side) = {.X, .Y, .Z} by decide +kernel]
  simp [Nat.add_assoc]

set_option maxHeartbeats 1000000 in
-- The stage-population label and exact-part types require the larger elaboration allowance.
/-- One full reserve-sized group of actual good labels repairs to the reference exact tensor. -/
theorem repairExactGroup27 {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : stageGood25 q p d b ε m r M B ω j)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (K : Fin (repairReserve (stagePopulationAt q p d b m r).n
      (fun W => (exactPartsAt q b m p d r j W).card)) →
        (stagePopulationAt q p d b m r).Label)
    (hK : ∀ i, stageGood25 q p d b ε m r M B ω (K i)) :
    Restricts (stageExactTensorZ27 q b m p d r j)
      (dependentSumZ fun i =>
        stageBrokenCopyZ25 q p d b ε m r M B ω (K i)).tensor := by
  classical
  let P := stagePopulationAt q p d b m r
  let reserve := repairReserve P.n
    (fun W => (exactPartsAt q b m p d r j W).card)
  have hjt := goodLabel_target27 q m M ε p d r B ω j hj
  have hKt : ∀ i, K i ∈ P.target := fun i =>
    goodLabel_target27 q m M ε p d r B ω (K i) (hK i)
  letI : Nonempty (StageExactPart27 q b m p d r j .X) :=
    stageExactPart_nonempty27 q m p d hd hb r j hjt .X
  letI : Nonempty (StageExactPart27 q b m p d r j .Y) :=
    stageExactPart_nonempty27 q m p d hd hb r j hjt .Y
  letI : Nonempty (StageExactPart27 q b m p d r j .Z) :=
    stageExactPart_nonempty27 q m p d hd hb r j hjt .Z
  let HX := fun i => transportedStageHolesAssembly27 q m M ε p d r B ω
    j (K i) hjt (hKt i) .X
  let HY := fun i => transportedStageHolesAssembly27 q m M ε p d r B ω
    j (K i) hjt (hKt i) .Y
  let HZ := fun i => transportedStageHolesAssembly27 q m M ε p d r B ω
    j (K i) hjt (hKt i) .Z
  have hcap (W : Side) (i : Fin reserve) :
      4 * P.n *
          (transportedStageHolesAssembly27 q m M ε p d r B ω
            j (K i) hjt (hKt i) W).card ≤
        Fintype.card (StageExactPart27 q b m p d r j W) := by
    rw [transportedStageHolesAssembly27_card]
    rw [Fintype.card_coe]
    calc
      4 * P.n * (holesAt25 q b m M ε p d r B ω (K i) W).card ≤
          (exactPartsAt q b m p d r (K i) W).card := (hK i).2 W
      _ = (exactPartsAt q b m p d r j W).card :=
        selected_exactPartsAt_card_eq q m p d hd hb r M B ω (K i) j
          (hK i).1 hj.1 W
  have hreserve :
      4 ^ (Nat.log P.n (Fintype.card (StageExactPart27 q b m p d r j .X)) +
        Nat.log P.n (Fintype.card (StageExactPart27 q b m p d r j .Y)) +
        Nat.log P.n (Fintype.card (StageExactPart27 q b m p d r j .Z)) + 1) ≤
        Fintype.card (Fin reserve) := by
    simp only [Fintype.card_coe, Fintype.card_fin]
    rw [show reserve = 4 ^
        (Nat.log P.n (exactPartsAt q b m p d r j .X).card +
         Nat.log P.n (exactPartsAt q b m p d r j .Y).card +
         Nat.log P.n (exactPartsAt q b m p d r j .Z).card + 1) by
      simp only [reserve, repairReserve, sum_side_three27]]
  have hfix := fix_holes_general (stageExactTensorZ27 q b m p d r j)
    (stageExactPart27 q b m p d r j .X)
    (stageExactPart27 q b m p d r j .Y)
    (stageExactPart27 q b m p d r j .Z)
    (exact_interface_shuffles q b m p d r j) P.n
    (stagePopulationAt_n_ge_two q b m p d r hn)
    HX HY HZ (fun i => hcap .X i) (fun i => hcap .Y i) (fun i => hcap .Z i)
    (Finset.univ : Finset (Fin reserve)) hreserve
  refine Tensor3.Restricts.trans hfix
    (famDS_restricts_dependentSumAssembly27
      (fun i => boxZO (stageExactPart27 q b m p d r j .X)
        (stageExactPart27 q b m p d r j .Y)
        (stageExactPart27 q b m p d r j .Z) (HX i)ᶜ (HY i)ᶜ (HZ i)ᶜ
        (stageExactTensorZ27 q b m p d r j))
      (fun i => stageBrokenCopyZ25 q p d b ε m r M B ω (K i)) ?_)
  intro i
  exact stageCommonBox_restricts_broken27 q m M ε p d r B ω
    j (K i) hjt (hKt i)

private theorem nestedDependentSumZ_restrictsAssembly27
    {κ ι L : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
    (U : L → ITensor) (e : κ × ι → L) (he : Function.Injective e) :
    Restricts
      (dependentSumZ fun k => dependentSumZ fun i => U (e (k, i))).tensor
      (dependentSumZ U).tensor := by
  classical
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨e (x.1, x.2.1), x.2.2⟩)
    (fun y => ⟨e (y.1, y.2.1), y.2.2⟩)
    (fun z => ⟨e (z.1, z.2.1), z.2.2⟩) ?_
  rintro ⟨a, i, x⟩ ⟨b, j, y⟩ ⟨c, k, z⟩
  simp only [dependentSumZ]
  by_cases hab : (a, i) = (b, j)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    by_cases hac : (a, i) = (c, k)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
      simp
    · have heac : e (a, i) ≠ e (c, k) := fun h => hac (he h)
      by_cases hac₀ : a = c
      · subst hac₀
        have hik : i ≠ k := fun h => hac (congrArg (fun t => (a, t)) h)
        simp [hik, heac]
      · simp [hac₀, heac]
  · have heab : e (a, i) ≠ e (b, j) := fun h => hab (he h)
    by_cases hab₀ : a = b
    · subst hab₀
      have hij : i ≠ j := fun h => hab (congrArg (fun t => (a, t)) h)
      simp [hij, heab]
    · simp [hab₀, heab]

set_option maxHeartbeats 1000000 in
-- The quotient statement repeats the dependent stage family in both the full prefix and remainder.
/-- All full repair groups in one occupied region give the exact quotient number of copies. -/
theorem repairRegionalQuotient27 {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (r : Fin 6) (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (J : Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ j, j ∈ J → stageGood25 q p d b ε m r M B ω j)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hcopies : 0 < J.card / repairReserve (stagePopulationAt q p d b m r).n
      (fun W => J.sup (fun j => (exactPartsAt q b m p d r j W).card))) :
    ∃ (j : (stagePopulationAt q p d b m r).Label), j ∈ J ∧
      Restricts
        (copiesZ (J.card / repairReserve (stagePopulationAt q p d b m r).n
            (fun W => J.sup (fun j => (exactPartsAt q b m p d r j W).card)))
          (stageExactITensor27 q m p d r j)).tensor
        (dependentSumZ fun k : {k // k ∈ J} =>
          stageBrokenCopyZ25 q p d b ε m r M B ω k.val).tensor := by
  classical
  let P := stagePopulationAt q p d b m r
  let parts := fun W => J.sup (fun j => (exactPartsAt q b m p d r j W).card)
  let reserve := repairReserve P.n parts
  let copies := J.card / reserve
  have hprefix : copies * reserve ≤ J.card := Nat.div_mul_le_self J.card reserve
  have hreserve : 0 < reserve := repairReserve_pos P.n parts
  let e := repairGroupLabel27 J copies reserve hprefix
  have he : Function.Injective e := repairGroupLabel27_injective J copies reserve hprefix
  let g₀ : Fin copies := ⟨0, hcopies⟩
  let i₀ : Fin reserve := ⟨0, hreserve⟩
  let j₀ := (e (g₀, i₀)).val
  have hj₀mem : j₀ ∈ J := (e (g₀, i₀)).property
  have hj₀good := hJ j₀ hj₀mem
  let reserve₀ := repairReserve P.n
    (fun W => (exactPartsAt q b m p d r j₀ W).card)
  have hreserveEq : reserve = reserve₀ :=
    selected_repairReserve_sup_eq q m p d hd hb ε r M B ω J hJ j₀ hj₀mem
  let ec : Fin copies × Fin reserve₀ → {j // j ∈ J} := fun gi =>
    e (gi.1, (finCongr hreserveEq.symm) gi.2)
  have hec : Function.Injective ec := by
    intro a c hac
    have hp : (a.1, (finCongr hreserveEq.symm) a.2) =
        (c.1, (finCongr hreserveEq.symm) c.2) := he hac
    apply Prod.ext
    · exact congrArg (fun x : Fin copies × Fin reserve => x.1) hp
    · exact (finCongr hreserveEq.symm).injective
        (congrArg (fun x : Fin copies × Fin reserve => x.2) hp)
  let U := fun k : {k // k ∈ J} =>
    stageBrokenCopyZ25 q p d b ε m r M B ω k.val
  have hgroup (g : Fin copies) :
      Restricts (stageExactTensorZ27 q b m p d r j₀)
        (dependentSumZ fun i : Fin reserve₀ => U (ec (g, i))).tensor := by
    apply repairExactGroup27 q m hq p d hd hb ε r M B ω j₀ hj₀good hn
    intro i
    exact hJ (ec (g, i)).val (ec (g, i)).property
  have hgroups : Restricts
      (copiesZ copies (stageExactITensor27 q m p d r j₀)).tensor
      (dependentSumZ fun g : Fin copies =>
        dependentSumZ fun i : Fin reserve₀ => U (ec (g, i))).tensor := by
    simpa only [copiesZ, stageExactITensor27] using
      famDS_restricts_dependentSumAssembly27
        (fun _g : Fin copies => stageExactTensorZ27 q b m p d r j₀)
        (fun g : Fin copies => dependentSumZ fun i : Fin reserve₀ => U (ec (g, i)))
        hgroup
  have hreindex : Restricts
      (dependentSumZ fun g : Fin copies =>
        dependentSumZ fun i : Fin reserve₀ => U (ec (g, i))).tensor
      (dependentSumZ U).tensor :=
    nestedDependentSumZ_restrictsAssembly27 U ec hec
  refine ⟨j₀, hj₀mem, ?_⟩
  exact Tensor3.Restricts.trans hgroups hreindex

private theorem ratFloorNatAssembly27 (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem stageCountsCastAssembly27 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ :=
  hb.countsExact r W t u σ

private def stageHalfOneComplementEquivAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 1) = u} ≃
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 0) = complement p t u} where
  toFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 0)⟩ = complement p t u
    calc
      j.val ⟨t, (i.val, 0)⟩ =
          complement p t (complement p t (j.val ⟨t, (i.val, 0)⟩)) :=
        (OmegaBound.ADVXXZPaper.complement_complement t _).symm
      _ = complement p t (j.val ⟨t, (i.val, 1)⟩) :=
        (congrArg (complement p t) hc).symm
      _ = complement p t u := congrArg (complement p t) i.property⟩
  invFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 1)⟩ = u
    calc
      j.val ⟨t, (i.val, 1)⟩ = complement p t (j.val ⟨t, (i.val, 0)⟩) := hc
      _ = complement p t (complement p t u) :=
        congrArg (complement p t) i.property
      _ = u := OmegaBound.ADVXXZPaper.complement_complement t u⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

private theorem stageHalfZeroCardAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 0) = u} =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob u).floor.toNat := by
  rw [Fintype.card_subtype]
  have h := (Finset.mem_filter.mp hj).2 t u
  simpa only [stageColour27] using h

private theorem stageFibreCardAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} = m * d.outBase ⟨t,r,u⟩ := by
  calc
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
        stageColour27 q b m p d r j t i = u} =
        Fintype.card
          ({i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 0) = u} ⊕
            {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 1) = u}) :=
      Fintype.card_congr (twoHalfFibreEquiv27
        (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
          stageColour27 q b m p d r j t i = u))
    _ = Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 0) = u} +
        Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 1) = u} := Fintype.card_sum
    _ = (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob u).floor.toNat +
        (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob (complement p t u)).floor.toNat := by
      rw [stageHalfZeroCardAssembly27 q m p d r j hj t u,
        Fintype.card_congr (stageHalfOneComplementEquivAssembly27 q m p d r j t u),
        stageHalfZeroCardAssembly27 q m p d r j hj t (complement p t u)]
    _ = m * d.outBase ⟨t,r,u⟩ := stageAlphaPair27 p d hd m hb r t u

set_option maxHeartbeats 1000000 in
private def stageFibreEquivAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} ≃ Fin (m * d.outBase ⟨t,r,u⟩) :=
  by
    classical
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    exact stageFibreCardAssembly27 q m p d hd hb r j hj t u

private abbrev ConstituentOutputLegAssembly27 {w s : ℕ} (q m : ℕ)
    {p : ConstituentInput w s} (d : ConstituentSpec p) :=
  (t : Fin (Fintype.card (ConstituentTerm p))) →
    Fin (constituentOutN d.toPaper m t) → Fin w → CW90.Idx7 q

private def constituentOutputExactAssembly27 {w s : ℕ} (q m : ℕ)
    {p : ConstituentInput w s} (d : ConstituentSpec p) (W : Side)
    (x : ConstituentOutputLegAssembly27 q m d) : Prop :=
  ∀ t, constituentOutN d.toPaper m t = 0 ∨
    ApproxConsistent 0 (constituentOutBeta d.toPaper W t) (chunkSeq (x t))

private def constituentOutputRawAssembly27 {w s : ℕ} (q m : ℕ)
    {p : ConstituentInput w s} (d : ConstituentSpec p) :
    Tensor3 ℤ (ConstituentOutputLegAssembly27 q m d)
      (ConstituentOutputLegAssembly27 q m d)
      (ConstituentOutputLegAssembly27 q m d) :=
  fun x y z => ∏ t,
    tensorPower (conZ q w (constituentOutI (p := p) t)
      (constituentOutJ (p := p) t) (constituentOutK (p := p) t))
      (constituentOutN d.toPaper m t) (x t) (y t) (z t)

set_option maxHeartbeats 1000000 in
private theorem constituentOutputTensor_eq_zoPAssembly27 {w s : ℕ} (q m : ℕ)
    {p : ConstituentInput w s} (d : ConstituentSpec p) :
    (constituentOutputZ q d m 0).tensor =
      zoP (constituentOutputExactAssembly27 q m d .X)
        (constituentOutputExactAssembly27 q m d .Y)
        (constituentOutputExactAssembly27 q m d .Z)
        (constituentOutputRawAssembly27 q m d) := by
  funext x y z
  simp only [constituentOutputZ, ifaceZ, constituentOutputRawAssembly27,
    constituentOutputExactAssembly27, zoP]
  by_cases h : (∀ t, constituentOutN d.toPaper m t = 0 ∨
      ApproxConsistent 0 (constituentOutBeta d.toPaper .X t) (chunkSeq (x t))) ∧
    (∀ t, constituentOutN d.toPaper m t = 0 ∨
      ApproxConsistent 0 (constituentOutBeta d.toPaper .Y t) (chunkSeq (y t))) ∧
    (∀ t, constituentOutN d.toPaper m t = 0 ∨
      ApproxConsistent 0 (constituentOutBeta d.toPaper .Z t) (chunkSeq (z t)))
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro t _
    simp only [ifaceTermZ]
    by_cases hn : constituentOutN d.toPaper m t = 0
    · rw [if_pos hn]
      symm
      apply Finset.prod_eq_one
      intro i _
      have hp : 0 < constituentOutN d.toPaper m t := Fin.pos_iff_nonempty.mpr ⟨i⟩
      omega
    · rw [if_neg hn, if_pos ⟨(h.1 t).resolve_left hn,
        (h.2.1 t).resolve_left hn, (h.2.2 t).resolve_left hn⟩]
  · rw [if_neg h]
    rw [not_and_or, not_and_or] at h
    rcases h with hx | hy | hz
    · obtain ⟨t, ht⟩ := not_forall.mp hx
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp only [ifaceTermZ]
      push_neg at ht
      rw [if_neg ht.1, if_neg]
      exact fun hkeep => ht.2 hkeep.1
    · obtain ⟨t, ht⟩ := not_forall.mp hy
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp only [ifaceTermZ]
      push_neg at ht
      rw [if_neg ht.1, if_neg]
      exact fun hkeep => ht.2 hkeep.2.1
    · obtain ⟨t, ht⟩ := not_forall.mp hz
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp only [ifaceTermZ]
      push_neg at ht
      rw [if_neg ht.1, if_neg]
      exact fun hkeep => ht.2 hkeep.2.2

private def constituentTermAssembly27 {w s : ℕ} {p : ConstituentInput w s}
    (t : Fin s) (r : Fin 6) (u : ChildShape p t) :
    Fin (Fintype.card (ConstituentTerm p)) :=
  Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩

@[simp] private theorem constituentIndex_termAssembly27 {w s : ℕ}
    {p : ConstituentInput w s} (t : Fin s) (r : Fin 6) (u : ChildShape p t) :
    constituentIndex (p := p) (constituentTermAssembly27 t r u) = ⟨t,r,u⟩ :=
  (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨t,r,u⟩

@[simp] private theorem constituentOutN_termAssembly27 {w s m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (t : Fin s) (r : Fin 6) (u : ChildShape p t) :
    constituentOutN d.toPaper m (constituentTermAssembly27 t r u) =
      d.outBase ⟨t,r,u⟩ * m := by
  simp [constituentOutN, ConstituentSpec.toPaper]

private def stageOutputPositionEquivAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} ≃
      Fin (constituentOutN d.toPaper m (constituentTermAssembly27 t r u)) :=
  (stageFibreEquivAssembly27 q m p d hd hb r j hj t u).trans
    (finCongr (calc
      m * d.outBase ⟨t,r,u⟩ = d.outBase ⟨t,r,u⟩ * m := Nat.mul_comm _ _
      _ = constituentOutN d.toPaper m (constituentTermAssembly27 t r u) :=
        (constituentOutN_termAssembly27 d t r u).symm))

private def constituentToStageWordAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (x : ConstituentOutputLegAssembly27 q m d) :
    StagePhysicalWord q p d b m r := fun z =>
  x (constituentTermAssembly27 z.1 r (stageColour27 q b m p d r j z.1 z.2))
    (stageOutputPositionEquivAssembly27 q m p d hd hb r j hj z.1
      (stageColour27 q b m p d r j z.1 z.2) ⟨z.2, rfl⟩)

private theorem constituentToStageWord_at_fibreAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (x : ConstituentOutputLegAssembly27 q m d) (t : Fin s)
    (u : ChildShape p t)
    (i : {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u}) :
    constituentToStageWordAssembly27 q m p d hd hb r j hj x ⟨t,i.val⟩ =
      x (constituentTermAssembly27 t r u)
        (stageOutputPositionEquivAssembly27 q m p d hd hb r j hj t u i) := by
  rcases i with ⟨i, hi⟩
  subst u
  rfl

private theorem constituentToStageWord_fibreAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (x : ConstituentOutputLegAssembly27 q m d) (t : Fin s)
    (u : ChildShape p t)
    (i : {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u}) :
    chunkOf (constituentToStageWordAssembly27 q m p d hd hb r j hj x ⟨t,i.val⟩) =
      chunkSeq (x (constituentTermAssembly27 t r u))
        (stageOutputPositionEquivAssembly27 q m p d hd hb r j hj t u i) := by
  exact congrArg chunkOf
    (constituentToStageWord_at_fibreAssembly27 q m p d hd hb r j hj x t u i)

private theorem constituentOutputTypeCntAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : ConstituentIntegral36 d b m) (W : Side)
    (x : ConstituentOutputLegAssembly27 q m d)
    (hx : constituentOutputExactAssembly27 q m d W x)
    (t : Fin s) (r : Fin 6) (u : ChildShape p t) (σ : Chunk w) :
    typeCnt (chunkSeq (x (constituentTermAssembly27 t r u))) σ =
      stageCounts27 m p d r W t u σ := by
  let a := constituentTermAssembly27 t r u
  have hn : constituentOutN d.toPaper m a = d.outBase ⟨t,r,u⟩ * m :=
    constituentOutN_termAssembly27 d t r u
  by_cases hzero : constituentOutN d.toPaper m a = 0
  · have hsum := stageCounts27_sum p d m hb r W t u
    have hsum0 : ∑ τ, stageCounts27 m p d r W t u τ = 0 := by
      rw [hsum, Nat.mul_comm, ← hn, hzero]
    have hcount0 : stageCounts27 m p d r W t u σ = 0 := by
      have hle : stageCounts27 m p d r W t u σ ≤
          ∑ τ, stageCounts27 m p d r W t u τ :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
      omega
    rw [hcount0]
    unfold typeCnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    have hp : 0 < constituentOutN d.toPaper m a := Fin.pos_iff_nonempty.mpr ⟨i⟩
    omega
  · have hpos : 0 < constituentOutN d.toPaper m a := Nat.pos_of_ne_zero hzero
    have hcons : Consistent (constituentOutBeta d.toPaper W a)
        (chunkSeq (x a)) :=
      (approxConsistent_zero_iff _ _ hpos).mp ((hx a).resolve_left hzero)
    have hprob := (consistent_iff_prob _ _ hpos).mp hcons σ
    have hcast : (typeCnt (chunkSeq (x a)) σ : ℚ) =
        (constituentOutN d.toPaper m a : ℚ) *
          (constituentOutBeta d.toPaper W a).prob σ := by
      unfold emp at hprob
      have hh := (div_eq_iff (Nat.cast_ne_zero.mpr hzero)).mp hprob
      exact hh.trans (mul_comm _ _)
    apply Nat.cast_injective (R := ℚ)
    rw [hcast, stageCountsCastAssembly27 p d m hb r W t u]
    rw [hn]
    have hbeta : constituentOutBeta d.toPaper W a = d.betaChild W t r u := by
      unfold constituentOutBeta
      simp only [ConstituentSpec.toPaper]
      rw [show constituentIndex a = ⟨t,r,u⟩ from
        constituentIndex_termAssembly27 t r u]
    rw [hbeta]
    push_cast
    ring

private theorem stageWordHistogramAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (x : ConstituentOutputLegAssembly27 q m d)
    (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    histogram27 (fun i => (stageColour27 q b m p d r j t i,
      chunkOf (constituentToStageWordAssembly27 q m p d hd hb r j hj x ⟨t,i⟩)))
      (u,σ) = typeCnt (chunkSeq (x (constituentTermAssembly27 t r u))) σ := by
  classical
  let e := stageOutputPositionEquivAssembly27 q m p d hd hb r j hj t u
  unfold histogram27 typeCnt
  apply Finset.card_bij (fun i hi =>
    e ⟨i, congrArg Prod.fst (Finset.mem_filter.mp hi).2⟩)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsnd := congrArg Prod.snd hi.2
    rw [constituentToStageWord_fibreAssembly27 q m p d hd hb r j hj x t u
      ⟨i, congrArg Prod.fst hi.2⟩] at hsnd
    exact hsnd
  · intro i₁ h₁ i₂ h₂ heq
    apply e.injective at heq
    exact congrArg Subtype.val heq
  · intro k hk
    refine ⟨(e.symm k).val, ?_, ?_⟩
    · rw [Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ _, Prod.ext (e.symm k).property ?_⟩
      rw [constituentToStageWord_fibreAssembly27 q m p d hd hb r j hj x t u
        (e.symm k), e.apply_symm_apply]
      exact hk.2
    · exact e.apply_symm_apply k

private def constituentToExactStageLegAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target) (W : Side)
    (x : {x : ConstituentOutputLegAssembly27 q m d //
      constituentOutputExactAssembly27 q m d W x}) :
    StageExactLeg27 q b m p d r j W := by
  let a := constituentToStageWordAssembly27 q m p d hd hb r j hj x.val
  refine ⟨a, (stageExact_iff_partition27 q b m p d r j W
    (stagePhysicalPart q p d b m r W a)).mpr ?_⟩
  constructor
  · intro t i
    let u := stageColour27 q b m p d r j t i
    let σ := chunkOf (a ⟨t,i⟩)
    have hhist : 0 < histogram27 (fun k =>
        (stageColour27 q b m p d r j t k, chunkOf (a ⟨t,k⟩))) (u,σ) := by
      unfold histogram27
      rw [Finset.card_pos]
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rfl
    have hcount : 0 < stageCounts27 m p d r W t u σ := by
      rw [stageWordHistogramAssembly27 q m p d hd hb r j hj x.val t u σ,
        constituentOutputTypeCntAssembly27 q m p d hb W x.val x.property t r u σ]
        at hhist
      exact hhist
    have hlevel : chunkLvl σ = coord W u.val := by
      apply hd.child_support W t r u σ
      intro hzero
      have hc : stageCounts27 m p d r W t u σ = 0 := by
        unfold stageCounts27
        rw [show (d.betaChild W t r u).prob σ = 0 by
          simp [RatDist.prob, hzero]]
        simp only [mul_zero]
        change ((((0 : ℤ) : ℚ).floor).toNat) = 0
        rw [Rat.floor_intCast]
        exact Int.toNat_zero
      omega
    exact hlevel
  · intro t u σ
    exact (stageWordHistogramAssembly27 q m p d hd hb r j hj x.val t u σ).trans
      (constituentOutputTypeCntAssembly27 q m p d hb W x.val x.property t r u σ)

private theorem stageExactTensor_outputAssembly27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (x : {x : ConstituentOutputLegAssembly27 q m d //
      constituentOutputExactAssembly27 q m d .X x})
    (y : {y : ConstituentOutputLegAssembly27 q m d //
      constituentOutputExactAssembly27 q m d .Y y})
    (z : {z : ConstituentOutputLegAssembly27 q m d //
      constituentOutputExactAssembly27 q m d .Z z}) :
    stageExactTensorZ27 q b m p d r j
        (constituentToExactStageLegAssembly27 q m p d hd hb r j hj .X x)
        (constituentToExactStageLegAssembly27 q m p d hd hb r j hj .Y y)
        (constituentToExactStageLegAssembly27 q m p d hd hb r j hj .Z z) =
      ∏ t : Fin s, ∏ u : ChildShape p t,
        tensorPower (conZ q w (coord .X u.val) (coord .Y u.val) (coord .Z u.val))
          (constituentOutN d.toPaper m (constituentTermAssembly27 t r u))
          (x.val (constituentTermAssembly27 t r u))
          (y.val (constituentTermAssembly27 t r u))
          (z.val (constituentTermAssembly27 t r u)) := by
  classical
  unfold stageExactTensorZ27
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro t _
  rw [← Fintype.prod_fiberwise (stageColour27 q b m p d r j t)
    (fun i => conZ q w (coord .X (j.val ⟨t,i⟩).val)
      (coord .Y (j.val ⟨t,i⟩).val) (coord .Z (j.val ⟨t,i⟩).val)
      ((constituentToExactStageLegAssembly27 q m p d hd hb r j hj .X x).val ⟨t,i⟩)
      ((constituentToExactStageLegAssembly27 q m p d hd hb r j hj .Y y).val ⟨t,i⟩)
      ((constituentToExactStageLegAssembly27 q m p d hd hb r j hj .Z z).val ⟨t,i⟩))]
  apply Finset.prod_congr rfl
  intro u _
  let e := stageOutputPositionEquivAssembly27 q m p d hd hb r j hj t u
  let f := fun k : Fin (constituentOutN d.toPaper m
      (constituentTermAssembly27 t r u)) =>
    conZ q w (coord .X u.val) (coord .Y u.val) (coord .Z u.val)
      (x.val (constituentTermAssembly27 t r u) k)
      (y.val (constituentTermAssembly27 t r u) k)
      (z.val (constituentTermAssembly27 t r u) k)
  change (∏ i : {i // stageColour27 q b m p d r j t i = u}, _) = ∏ k, f k
  calc
    _ = ∏ i : {i // stageColour27 q b m p d r j t i = u}, f (e i) := by
      apply Finset.prod_congr rfl
      intro i _
      change conZ q w (coord .X (j.val ⟨t,i.val⟩).val)
        (coord .Y (j.val ⟨t,i.val⟩).val) (coord .Z (j.val ⟨t,i.val⟩).val) _ _ _ = _
      rw [show j.val ⟨t,i.val⟩ = u from i.property]
      simp only [f, e, constituentToExactStageLegAssembly27]
      rw [constituentToStageWord_at_fibreAssembly27 q m p d hd hb r j hj x.val t u i,
        constituentToStageWord_at_fibreAssembly27 q m p d hd hb r j hj y.val t u i,
        constituentToStageWord_at_fibreAssembly27 q m p d hd hb r j hj z.val t u i]
    _ = _ := Equiv.prod_comp e f

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent raw-population cardinal requires the larger local budget.

set_option maxHeartbeats 1000000 in
-- The zero-position label is constructed only after unfolding the dependent population once.
private noncomputable def emptyStageTargetAssembly27 {w s b : ℕ} (q m : ℕ)
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
    have hp' : 0 < StageCandidateRaw.stageParentCount b m p d r t := Nat.pos_of_ne_zero hp
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
  have halphaRaw' : ∀ t u, ((b : ℚ) * m * p.baseN t *
      (d.A t).prob r * (d.alpha t r).prob u).floor.toNat = 0 := by
    intro t u
    simpa only [Nat.cast_mul] using halphaRaw t u
  have hparentRaw' : ∀ t, ∑ u : ChildShape p t,
      ((b : ℚ) * m * p.baseN t * (d.A t).prob r *
        (d.alpha t r).prob u).floor.toNat = 0 := by
    intro t
    simpa only [Nat.cast_mul] using hparentRaw t
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

private theorem constituentOutputRaw_reindexAssembly27 {w s : ℕ} (q m : ℕ)
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (x y z : ConstituentOutputLegAssembly27 q m d) :
    constituentOutputRawAssembly27 q m d x y z =
      ∏ r : Fin 6, ∏ t : Fin s, ∏ u : ChildShape p t,
        tensorPower (conZ q w (coord .X u.val) (coord .Y u.val) (coord .Z u.val))
          (constituentOutN d.toPaper m (constituentTermAssembly27 t r u))
          (x (constituentTermAssembly27 t r u))
          (y (constituentTermAssembly27 t r u))
          (z (constituentTermAssembly27 t r u)) := by
  classical
  let e := Fintype.equivFin (ConstituentTerm p)
  let f := fun a : Fin (Fintype.card (ConstituentTerm p)) =>
    tensorPower (conZ q w (constituentOutI (p := p) a)
      (constituentOutJ (p := p) a) (constituentOutK (p := p) a))
      (constituentOutN d.toPaper m a) (x a) (y a) (z a)
  change (∏ a, f a) = _
  calc
    _ = ∏ v : ConstituentTerm p, f (e v) := (Equiv.prod_comp e f).symm
    _ = ∏ t : Fin s, ∏ ru : Fin 6 × ChildShape p t, f (e ⟨t,ru⟩) :=
      Fintype.prod_sigma _
    _ = ∏ t : Fin s, ∏ r : Fin 6, ∏ u : ChildShape p t,
        tensorPower (conZ q w (coord .X u.val) (coord .Y u.val) (coord .Z u.val))
          (constituentOutN d.toPaper m (constituentTermAssembly27 t r u))
          (x (constituentTermAssembly27 t r u))
          (y (constituentTermAssembly27 t r u))
          (z (constituentTermAssembly27 t r u)) := by
      apply Finset.prod_congr rfl
      intro t _
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro r _
      apply Finset.prod_congr rfl
      intro u _
      simp only [f, e, constituentTermAssembly27, constituentOutI, constituentOutJ,
        constituentOutK]
      rw [show constituentIndex (p := p)
        ((Fintype.equivFin (ConstituentTerm p)) ⟨t,(r,u)⟩) = ⟨t,r,u⟩ from
          (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨t,r,u⟩]
    _ = _ := Finset.prod_comm

private theorem zoP_restricts_subtypeAssembly27
    {R X Y Z : Type*} [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) :
    Restricts (zoP pX pY pZ T)
      (fun x : {x // pX x} => fun y : {y // pY y} =>
        fun z : {z // pZ z} => T x.val y.val z.val) := by
  rw [zoP_eq_boxZO]
  have hbox := boxZO_restricts_subtypeAssembly27 (fun x => decide (pX x))
    (fun y => decide (pY y)) (fun z => decide (pZ z))
    {true} {true} {true} T
  let fX : {x // decide (pX x) ∈ ({true} : Finset Bool)} → {x // pX x} :=
    fun x => ⟨x.val, by simpa using x.property⟩
  let fY : {y // decide (pY y) ∈ ({true} : Finset Bool)} → {y // pY y} :=
    fun y => ⟨y.val, by simpa using y.property⟩
  let fZ : {z // decide (pZ z) ∈ ({true} : Finset Bool)} → {z // pZ z} :=
    fun z => ⟨z.val, by simpa using z.property⟩
  have hrename : Restricts
      (fun x : {x // decide (pX x) ∈ ({true} : Finset Bool)} =>
        fun y : {y // decide (pY y) ∈ ({true} : Finset Bool)} =>
        fun z : {z // decide (pZ z) ∈ ({true} : Finset Bool)} => T x.val y.val z.val)
      (fun x : {x // pX x} => fun y : {y // pY y} =>
        fun z : {z // pZ z} => T x.val y.val z.val) := by
    apply restricts_of_sub fX fY fZ
    intro x y z
    rfl
  exact Tensor3.Restricts.trans hbox hrename

private noncomputable def outputToExactRegionsXAssembly27 {w s b : ℕ}
    (q m : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (j : (r : Fin 6) → (stagePopulationAt q p d b m r).Label)
    (hj : ∀ r, j r ∈ (stagePopulationAt q p d b m r).target) :
    {x : ConstituentOutputLegAssembly27 q m d //
        constituentOutputExactAssembly27 q m d .X x} →
      (regionProductZ (fun r => stageExactITensor27 q m p d r (j r))).X :=
  fun x r => constituentToExactStageLegAssembly27 q m p d hd hb r (j r) (hj r) .X x

private noncomputable def outputToExactRegionsYAssembly27 {w s b : ℕ}
    (q m : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (j : (r : Fin 6) → (stagePopulationAt q p d b m r).Label)
    (hj : ∀ r, j r ∈ (stagePopulationAt q p d b m r).target) :
    {y : ConstituentOutputLegAssembly27 q m d //
        constituentOutputExactAssembly27 q m d .Y y} →
      (regionProductZ (fun r => stageExactITensor27 q m p d r (j r))).Y :=
  fun y r => constituentToExactStageLegAssembly27 q m p d hd hb r (j r) (hj r) .Y y

private noncomputable def outputToExactRegionsZAssembly27 {w s b : ℕ}
    (q m : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (j : (r : Fin 6) → (stagePopulationAt q p d b m r).Label)
    (hj : ∀ r, j r ∈ (stagePopulationAt q p d b m r).target) :
    {z : ConstituentOutputLegAssembly27 q m d //
        constituentOutputExactAssembly27 q m d .Z z} →
      (regionProductZ (fun r => stageExactITensor27 q m p d r (j r))).Z :=
  fun z r => constituentToExactStageLegAssembly27 q m p d hd hb r (j r) (hj r) .Z z

set_option maxHeartbeats 1000000 in
-- This is the displayed six-region coefficient regrouping, including the dependent term index.
/-- The product of the six repaired regional exact tensors is the exact constituent output. -/
theorem repairSixRegionOutput27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (j : (r : Fin 6) → (stagePopulationAt q p d b m r).Label)
    (hj : ∀ r, j r ∈ (stagePopulationAt q p d b m r).target) :
    Restricts (constituentOutputZ q d m 0).tensor
      (regionProductZ (fun r => stageExactITensor27 q m p d r (j r))).tensor := by
  classical
  rw [constituentOutputTensor_eq_zoPAssembly27]
  have hsub := zoP_restricts_subtypeAssembly27
    (constituentOutputExactAssembly27 q m d .X)
    (constituentOutputExactAssembly27 q m d .Y)
    (constituentOutputExactAssembly27 q m d .Z)
    (constituentOutputRawAssembly27 q m d)
  apply Tensor3.Restricts.trans hsub
  apply restricts_of_sub
    (outputToExactRegionsXAssembly27 q m p d hd hb j hj)
    (outputToExactRegionsYAssembly27 q m p d hd hb j hj)
    (outputToExactRegionsZAssembly27 q m p d hd hb j hj)
  intro x y z
  rw [constituentOutputRaw_reindexAssembly27]
  change (∏ r : Fin 6, ∏ t : Fin s, ∏ u : ChildShape p t,
      tensorPower (conZ q w (coord .X u.val) (coord .Y u.val) (coord .Z u.val))
        (constituentOutN d.toPaper m (constituentTermAssembly27 t r u))
        (x.val (constituentTermAssembly27 t r u))
        (y.val (constituentTermAssembly27 t r u))
        (z.val (constituentTermAssembly27 t r u))) = _
  simp only [regionProductZ]
  apply Finset.prod_congr rfl
  intro r _
  exact (stageExactTensor_outputAssembly27 q m p d hd hb r (j r) (hj r) x y z).symm

private theorem prod_sum3IntAssembly27 {n : ℕ}
    {X Y Z : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, Fintype (Z i)] (f : ∀ i, X i → Y i → Z i → ℤ) :
    (∏ i, ∑ a : X i, ∑ b : Y i, ∑ c : Z i, f i a b c) =
      ∑ a : (∀ i, X i), ∑ b : (∀ i, Y i), ∑ c : (∀ i, Z i),
        ∏ i, f i (a i) (b i) (c i) := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (X i)))
      (fun i a => ∑ b : Y i, ∑ c : Z i, f i a b c), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Y i)))
      (fun i b => ∑ c : Z i, f i (a i) b c), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Z i)))
      (fun i c => f i (a i) (b i) c), Fintype.piFinset_univ]

private theorem regionProductZ_restrictsAssembly27 (S T : Fin 6 → ITensor)
    (h : ∀ r, Restricts (S r).tensor (T r).tensor) :
    Restricts (regionProductZ S).tensor (regionProductZ T).tensor := by
  classical
  choose A₁ A₂ A₃ hA using h
  refine ⟨fun x a => ∏ r, A₁ r (x r) (a r),
    fun y b => ∏ r, A₂ r (y r) (b r),
    fun z c => ∏ r, A₃ r (z r) (c r), ?_⟩
  funext x y z
  have hfac : ∀ r, (S r).tensor (x r) (y r) (z r) =
      ∑ a : (T r).X, ∑ b : (T r).Y, ∑ c : (T r).Z,
        A₁ r (x r) a * A₂ r (y r) b * A₃ r (z r) c *
          (T r).tensor a b c := by
    intro r
    rw [hA r]
    rfl
  have hleft : (regionProductZ S).tensor x y z =
      ∏ r, ∑ a : (T r).X, ∑ b : (T r).Y, ∑ c : (T r).Z,
        A₁ r (x r) a * A₂ r (y r) b * A₃ r (z r) c *
          (T r).tensor a b c := by
    simp only [regionProductZ]
    exact Finset.prod_congr rfl fun r _ => hfac r
  rw [hleft, prod_sum3IntAssembly27]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [regionProductZ, Finset.prod_mul_distrib]

private theorem copiesZ_restrictsAssembly27 (k : ℕ) (S T : ITensor)
    (h : Restricts S.tensor T.tensor) :
    Restricts (copiesZ k S).tensor (copiesZ k T).tensor := by
  simpa only [copiesZ] using
    (ADVXXZStage.famDS_const_mono (Finset.univ : Finset (Fin k)) h)

private theorem copiesZ_zero_restrictsAssembly27 (T U : ITensor) :
    Restricts (copiesZ 0 T).tensor U.tensor := by
  apply restricts_of_sub (fun x => Fin.elim0 x.1) (fun y => Fin.elim0 y.1)
    (fun z => Fin.elim0 z.1)
  intro x
  exact Fin.elim0 x.1

set_option maxHeartbeats 1000000 in
private theorem emptyStageCopies_restricts_unitAssembly27 {w s b : ℕ}
    (q m : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (hn : (stagePopulationAt q p d b m r).n = 0) :
    Restricts
      (copiesZ 1 (stageExactITensor27 q m p d r
        (emptyStageTargetAssembly27 q m p d r hn).val)).tensor
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

set_option maxHeartbeats 2000000 in
/-- Actual full repair groups in all six regions restrict to exact constituent-output copies. -/
theorem repair_fibres {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ r j, j ∈ J r → stageGood25 q p d b ε m r (M r) (B r) (ω r) j)
    (hvalid : ValidStageHashes p d b m M B) :
  Restricts (copiesZ (stageRepairedCount q p d b ε m M B ω J)
      (constituentOutputZ q d m 0)).tensor
    (goodBrokenFamilyZ25 q p d b ε m M B ω J).tensor := by
  classical
  let copies : Fin 6 → ℕ := fun r =>
    let P := stagePopulationAt q p d b m r
    if P.n = 0 then 1 else
      (J r).card / repairReserve P.n
        (fun W => (J r).sup (fun j => (exactPartsAt q b m p d r j W).card))
  let regionalSource : Fin 6 → ITensor := fun r =>
    if (stagePopulationAt q p d b m r).n = 0 then unitFamilyZ else
      dependentSumZ fun j : {j // j ∈ J r} =>
        stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val
  have hcount : stageRepairedCount q p d b ε m M B ω J = ∏ r, copies r := by
    rfl
  rw [hcount]
  by_cases hzero : ∏ r, copies r = 0
  · rw [hzero]
    exact copiesZ_zero_restrictsAssembly27 _ _
  have hcopies : ∀ r, 0 < copies r := by
    intro r
    apply Nat.pos_of_ne_zero
    intro hr
    apply hzero
    exact Finset.prod_eq_zero (Finset.mem_univ r) hr
  have hexact : ∀ r, ∃ j : (stagePopulationAt q p d b m r).Label,
      j ∈ (stagePopulationAt q p d b m r).target ∧
        Restricts (copiesZ (copies r) (stageExactITensor27 q m p d r j)).tensor
          (regionalSource r).tensor := by
    intro r
    by_cases hn : (stagePopulationAt q p d b m r).n = 0
    · let e := emptyStageTargetAssembly27 q m p d r hn
      refine ⟨e.val, e.property, ?_⟩
      have hc : copies r = 1 := by
        dsimp only [copies]
        rw [if_pos hn]
      have hs : regionalSource r = unitFamilyZ := by
        dsimp only [regionalSource]
        rw [if_pos hn]
      rw [hc, hs]
      dsimp only [e]
      exact emptyStageCopies_restricts_unitAssembly27 q m p d r hn
    · have hc : 0 < (J r).card /
          repairReserve (stagePopulationAt q p d b m r).n
            (fun W => (J r).sup
              (fun j => (exactPartsAt q b m p d r j W).card)) := by
        simpa only [copies, hn, if_false] using hcopies r
      obtain ⟨j, hj, hrepair⟩ := repairRegionalQuotient27 q m hq p d hd hb ε r
        (M r) (B r) (ω r) (J r) (hJ r) hn hc
      refine ⟨j, goodLabel_target27 q m (M r) ε p d r (B r) (ω r) j
        (hJ r j hj), ?_⟩
      have hc' : copies r = (J r).card /
          repairReserve (stagePopulationAt q p d b m r).n
            (fun W => (J r).sup
              (fun j => (exactPartsAt q b m p d r j W).card)) := by
        dsimp only [copies]
        rw [if_neg hn]
      have hs : regionalSource r = dependentSumZ fun j : {j // j ∈ J r} =>
          stageBrokenCopyZ25 q p d b ε m r (M r) (B r) (ω r) j.val := by
        dsimp only [regionalSource]
        rw [if_neg hn]
      rw [hc', hs]
      exact hrepair
  choose j hj hregional using hexact
  have hout := repairSixRegionOutput27 q m p d hd hb j hj
  have hcopy : Restricts
      (copiesZ (∏ r, copies r) (constituentOutputZ q d m 0)).tensor
      (copiesZ (∏ r, copies r)
        (regionProductZ fun r => stageExactITensor27 q m p d r (j r))).tensor :=
    copiesZ_restrictsAssembly27 (∏ r, copies r) _ _ hout
  have hsplit := copiesZ_regionProductZ_restricts copies
    (fun r => stageExactITensor27 q m p d r (j r))
  have hregions : Restricts
      (regionProductZ fun r => copiesZ (copies r)
        (stageExactITensor27 q m p d r (j r))).tensor
      (regionProductZ regionalSource).tensor :=
    regionProductZ_restrictsAssembly27 _ _ hregional
  have hfinal := Tensor3.Restricts.trans hcopy
    (Tensor3.Restricts.trans hsplit hregions)
  change Restricts (copiesZ (∏ r, copies r) (constituentOutputZ q d m 0)).tensor
    ((if ValidStageHashes p d b m M B then regionProductZ regionalSource
      else emptyFamilyZ).tensor)
  rw [if_pos hvalid]
  exact hfinal
end
end CExact36RepairAux

-- Generic version for the empirical-grid consumer; P/constituent.tex:338-350,479; H/hole.tex:121-125.
theorem repair_fibres_integral36 {w s b : ℕ} (q m : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m) (ε : ℚ)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ r j, j ∈ J r → stageGood25 q p d b ε m r (M r) (B r) (ω r) j)
    (hvalid : ValidStageHashes p d b m M B) :
  Restricts (copiesZ (stageRepairedCount q p d b ε m M B ω J)
      (constituentOutputZ q d m 0)).tensor
    (goodBrokenFamilyZ25 q p d b ε m M B ω J).tensor :=
  CExact36RepairAux.repair_fibres q m hq p d hd hb ε M B ω J hJ hvalid

#print axioms OmegaBound.ADVXXZGeneral.repair_fibres_integral36
end OmegaBound.ADVXXZGeneral
end
