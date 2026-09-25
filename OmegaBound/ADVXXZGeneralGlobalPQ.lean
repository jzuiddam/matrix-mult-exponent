import OmegaBound.ADVXXZGeneralAmend25GlobalBridge

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem filter_card_eq_of_perm {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ ↦ e i) (fun i _ ↦ e.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (h (e.symm i)).mpr (by simpa using (Finset.mem_filter.mp hi).2)
  · intro i _
    exact e.symm_apply_apply i
  · intro i _
    exact e.apply_symm_apply i

private theorem typeCnt_comp_perm {A : Type*} [Fintype A] [DecidableEq A]
    {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → A) (a : A) :
    typeCnt (fun i ↦ x (e i)) a = typeCnt x a := by
  unfold typeCnt
  exact filter_card_eq_of_perm e
    (fun i ↦ x (e i) = a) (fun i ↦ x i = a) (fun _ ↦ Iff.rfl)

private theorem exists_perm_of_typeCnt
    {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (x y : Fin n → A) (h : ∀ a, typeCnt x a = typeCnt y a) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, y (e i) = x i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // x i = a} ≃ {i // y i = a}) :=
    ⟨fun a ↦ Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), fun i ↦ ?_⟩
  exact (e (x i) ⟨i, rfl⟩).2

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent target-label permutation needs more than the project default.
private noncomputable def globalTargetLabelPerm {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n ξ r).n)) :
    {j // j ∈ (globalPopulation g n ξ r).target} ≃
      {j // j ∈ (globalPopulation g n ξ r).target} := by
  classical
  unfold globalPopulation at e ⊢
  dsimp only
  refine
    { toFun := fun j ↦ ⟨⟨fun i ↦ j.val.val (e.symm i), ?_⟩, ?_⟩
      invFun := fun j ↦ ⟨⟨fun i ↦ j.val.val (e i), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro W a
    cases W with
    | X =>
        exact (filter_card_eq_of_perm e.symm _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .X a)
    | Y =>
        exact (filter_card_eq_of_perm e.symm _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .Y a)
    | Z =>
        exact (filter_card_eq_of_perm e.symm _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .Z a)
  · apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_univ]
    intro u
    exact (filter_card_eq_of_perm e.symm _ _ (fun _ ↦ Iff.rfl)).trans
      ((Finset.mem_filter.mp j.property).2 u)
  · intro W a
    cases W with
    | X =>
        exact (filter_card_eq_of_perm e _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .X a)
    | Y =>
        exact (filter_card_eq_of_perm e _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .Y a)
    | Z =>
        exact (filter_card_eq_of_perm e _ _ (fun _ ↦ Iff.rfl)).trans
          (j.val.property .Z a)
  · apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_univ]
    intro u
    exact (filter_card_eq_of_perm e _ _ (fun _ ↦ Iff.rfl)).trans
      ((Finset.mem_filter.mp j.property).2 u)
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp

set_option maxHeartbeats 1000000 in
-- Unfolding the preceding dependent equivalence in this computation lemma is heartbeat-heavy.
private theorem globalTargetLabelPerm_apply {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n ξ r).n))
    (j : {j // j ∈ (globalPopulation g n ξ r).target}) (i : Fin _) :
    ((globalTargetLabelPerm g ξ r e) j).val.val (e i) = j.val.val i := by
  classical
  change j.val.val (e.symm (e i)) = j.val.val i
  simp

private theorem target_filter_card_eq_of_equiv {A : Type*} [DecidableEq A]
    (S : Finset A) (e : {x // x ∈ S} ≃ {x // x ∈ S})
    (P Q : A → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x.val ↔ Q (e x).val) :
    (S.filter P).card = (S.filter Q).card := by
  refine Finset.card_bij'
    (fun x hx ↦ (e ⟨x, (Finset.mem_filter.mp hx).1⟩).val)
    (fun x hx ↦ (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h ⟨x, (Finset.mem_filter.mp hx).1⟩).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩)).mpr (by
        simpa using (Finset.mem_filter.mp hx).2)⟩
  · intro x hx
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)
  · intro x hx
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)

private theorem targetSubtype_filter_card {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (P : A → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : {x // x ∈ S} ↦ P x.val).card = (S.filter P).card := by
  refine Finset.card_bij' (fun x _ ↦ x.val)
    (fun x hx ↦ ⟨x, (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x hx
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_univ]
    exact (Finset.mem_filter.mp hx).2
  · intro x _
    rfl
  · intro x _
    rfl

private theorem card_filter_prod_eq {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (P : A → X → Prop) (B : X → Prop)
    [DecidablePred B] [∀ x, DecidablePred (P · x)] (c : ℕ)
    (hcard : ∀ x, B x → (Finset.univ.filter fun a ↦ P a x).card = c) :
    (Finset.univ.filter fun z : A × X ↦ P z.1 z.2 ∧ B z.2).card =
      (Finset.univ.filter B).card * c := by
  classical
  let e : {z : A × X // P z.1 z.2 ∧ B z.2} ≃
      (x : {x : X // B x}) × {a : A // P a x.1} :=
    { toFun := fun z ↦ ⟨⟨z.1.2, z.2.2⟩, ⟨z.1.1, z.2.1⟩⟩
      invFun := fun z ↦ ⟨(z.2.1, z.1.1), z.2.2, z.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (Finset.univ.filter fun z : A × X ↦ P z.1 z.2 ∧ B z.2).card =
        Fintype.card {z : A × X // P z.1 z.2 ∧ B z.2} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card ((x : {x : X // B x}) × {a : A // P a x.1}) :=
      Fintype.card_congr e
    _ = ∑ x : {x : X // B x}, Fintype.card {a : A // P a x.1} :=
      Fintype.card_sigma
    _ = ∑ _x : {x : X // B x}, c := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.card_subtype]
      exact hcard x x.property
    _ = (Finset.univ.filter B).card * c := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      congr 1
      rw [Fintype.card_subtype]
      congr 1

private theorem globalCoarseContains_perm {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n ξ r).Part S)
    (e : Equiv.Perm (Fin (globalPopulation g n ξ r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n ξ r).target}) :
    globalCoarseContains g n ξ r S j.val x ↔
      globalCoarseContains g n ξ r S (globalTargetLabelPerm g ξ r e j).val y := by
  unfold globalCoarseContains
  constructor
  · intro h k
    have hy : y k = x (e.symm k) := by simpa using he (e.symm k)
    have hj := globalTargetLabelPerm_apply g ξ r e j (e.symm k)
    simpa [hy] using (h (e.symm k)).trans (congrArg (coord S) hj.symm)
  · intro h i
    have hi := h (e i)
    rw [he i, globalTargetLabelPerm_apply g ξ r e j i] at hi
    exact hi

private theorem globalCellCount_perm {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n ξ r).Part S)
    (e : Equiv.Perm (Fin (globalPopulation g n ξ r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n ξ r).target})
    (cell : Shape w → Prop) (σ : Chunk w) :
    globalCellCount g n ξ r S j.val x cell σ =
      globalCellCount g n ξ r S (globalTargetLabelPerm g ξ r e j).val y cell σ := by
  classical
  unfold globalCellCount
  exact filter_card_eq_of_perm e _ _ (fun i ↦ by
    rw [he i, globalTargetLabelPerm_apply g ξ r e j i])

private theorem globalCompatible_perm {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (x y : (globalPopulation g n ξ r).Part
      (g.perm r (if W = 0 then .Y else .Z)))
    (e : Equiv.Perm (Fin (globalPopulation g n ξ r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n ξ r).target}) :
    globalCompatible g n ξ r W j.val x ↔
      globalCompatible g n ξ r W (globalTargetLabelPerm g ξ r e j).val y := by
  unfold globalCompatible
  dsimp only
  constructor
  · rintro ⟨hboundary, hresidual⟩
    constructor
    · intro u hu σ
      calc
        _ = globalCellCount g n ξ r (g.perm r (if W = 0 then .Y else .Z))
            j.val x (fun v ↦ v = u) σ := by
          symm
          exact globalCellCount_perm g ξ r _ x y e he j _ _
        _ = _ := hboundary u hu σ
    · intro k σ
      calc
        _ = globalCellCount g n ξ r (g.perm r (if W = 0 then .Y else .Z))
            j.val x (fun u ↦ coord (if W = 0 then g.perm r .Y else g.perm r .Z) u = k.val) σ := by
          symm
          exact globalCellCount_perm g ξ r _ x y e he j _ _
        _ = _ := hresidual k σ
  · rintro ⟨hboundary, hresidual⟩
    constructor
    · intro u hu σ
      calc
        _ = globalCellCount g n ξ r (g.perm r (if W = 0 then .Y else .Z))
            (globalTargetLabelPerm g ξ r e j).val y (fun v ↦ v = u) σ :=
          globalCellCount_perm g ξ r _ x y e he j _ _
        _ = _ := hboundary u hu σ
    · intro k σ
      calc
        _ = globalCellCount g n ξ r (g.perm r (if W = 0 then .Y else .Z))
            (globalTargetLabelPerm g ξ r e j).val y
              (fun u ↦ coord (if W = 0 then g.perm r .Y else g.perm r .Z) u = k.val) σ :=
          globalCellCount_perm g ξ r _ x y e he j _ _
        _ = _ := hresidual k σ

private theorem global_exists_perm_of_empirical_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n ξ r).Part S)
    (hxy : globalEmpiricalLaw g n ξ r S x =
      globalEmpiricalLaw g n ξ r S y) :
    ∃ e : Equiv.Perm (Fin (globalPopulation g n ξ r).n), ∀ i, y (e i) = x i := by
  apply exists_perm_of_typeCnt x y
  intro σ
  exact congrFun hxy σ

private noncomputable def globalContainingLabels {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (S : Side)
    (x : (globalPopulation g n ξ r).Part S) :
    Finset (globalPopulation g n ξ r).Label := by
  classical
  exact (globalPopulation g n ξ r).target.filter fun j ↦
    globalCoarseContains g n ξ r S j x

private theorem globalContainingLabels_card_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n ξ r).Part S)
    (hxy : globalEmpiricalLaw g n ξ r S x =
      globalEmpiricalLaw g n ξ r S y) :
    (globalContainingLabels g ξ r S x).card =
      (globalContainingLabels g ξ r S y).card := by
  classical
  obtain ⟨e, he⟩ := global_exists_perm_of_empirical_eq g ξ r S x y hxy
  unfold globalContainingLabels
  exact target_filter_card_eq_of_equiv (globalPopulation g n ξ r).target
    (globalTargetLabelPerm g ξ r e)
    (fun j ↦ globalCoarseContains g n ξ r S j x)
    (fun j ↦ globalCoarseContains g n ξ r S j y)
    (globalCoarseContains_perm g ξ r S x y e he)

private noncomputable def globalCompatibleLabels {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (x : (globalPopulation g n ξ r).Part
      (g.perm r (if W = 0 then .Y else .Z))) :
    Finset (globalPopulation g n ξ r).Label := by
  classical
  exact (globalPopulation g n ξ r).target.filter fun j ↦
    globalCoarseContains g n ξ r (g.perm r (if W = 0 then .Y else .Z)) j x ∧
      globalCompatible g n ξ r W j x

private theorem globalCompatibleLabels_card_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (x y : (globalPopulation g n ξ r).Part
      (g.perm r (if W = 0 then .Y else .Z)))
    (hxy : globalEmpiricalLaw g n ξ r
      (g.perm r (if W = 0 then .Y else .Z)) x =
      globalEmpiricalLaw g n ξ r
        (g.perm r (if W = 0 then .Y else .Z)) y) :
    (globalCompatibleLabels g ξ r W x).card =
      (globalCompatibleLabels g ξ r W y).card := by
  classical
  obtain ⟨e, he⟩ := global_exists_perm_of_empirical_eq g ξ r _ x y hxy
  unfold globalCompatibleLabels
  apply target_filter_card_eq_of_equiv (globalPopulation g n ξ r).target
    (globalTargetLabelPerm g ξ r e)
    (fun j ↦ globalCoarseContains g n ξ r
      (g.perm r (if W = 0 then .Y else .Z)) j x ∧ globalCompatible g n ξ r W j x)
    (fun j ↦ globalCoarseContains g n ξ r
      (g.perm r (if W = 0 then .Y else .Z)) j y ∧ globalCompatible g n ξ r W j y)
  intro j
  exact and_congr (globalCoarseContains_perm g ξ r _ x y e he j)
    (globalCompatible_perm g ξ r W x y e he j)

private theorem globalLawSamples_nonempty {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    (globalLawSamples g n ξ r W β).Nonempty := by
  have hmem := (Finset.mem_filter.mp β.property).1
  rcases Finset.mem_image.mp hmem with ⟨z, hz, heq⟩
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩

private theorem globalFirstLawSample_mem {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    globalFirstLawSample g n ξ r W β ∈ globalLawSamples g n ξ r W β := by
  classical
  let candidates := globalLawSamples g n ξ r W β
  have hcandidates : candidates.Nonempty := globalLawSamples_nonempty g ξ r W β
  let e := Fintype.equivFin (GlobalLawSample g n ξ r W)
  letI := LinearOrder.lift' e e.injective
  change candidates.min' hcandidates ∈ candidates
  exact Finset.min'_mem _ _

private noncomputable def globalFineWords {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    Finset ((globalPopulation g n ξ r).Part
      (g.perm r (if W = 0 then .Y else .Z))) := by
  classical
  exact Finset.univ.filter fun x ↦
    globalEmpiricalLaw g n ξ r (g.perm r (if W = 0 then .Y else .Z)) x = β.val

private theorem globalLawSamples_card_factor {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    (globalLawSamples g n ξ r W β).card =
      (globalFineWords g ξ r W β).card *
        (globalContainingLabels g ξ r
          (g.perm r (if W = 0 then .Y else .Z))
          (globalFirstLawSample g n ξ r W β).2).card := by
  classical
  let S := g.perm r (if W = 0 then .Y else .Z)
  let a := (globalFirstLawSample g n ξ r W β).2
  have haMem := globalFirstLawSample_mem g ξ r W β
  have haLaw : globalEmpiricalLaw g n ξ r S a = β.val :=
    (Finset.mem_filter.mp haMem).2
  have hcard := card_filter_prod_eq
    (fun j : {j // j ∈ (globalPopulation g n ξ r).target} ↦ fun x ↦
      globalCoarseContains g n ξ r S j.val x)
    (fun x ↦ globalEmpiricalLaw g n ξ r S x = β.val)
    (globalContainingLabels g ξ r S a).card
    (fun x hx ↦ by
      calc
        _ = (globalContainingLabels g ξ r S x).card := by
          unfold globalContainingLabels
          exact targetSubtype_filter_card (globalPopulation g n ξ r).target
            (fun j ↦ globalCoarseContains g n ξ r S j x)
        _ = _ := globalContainingLabels_card_eq g ξ r S x a
          (hx.trans haLaw.symm))
  simpa only [S, a, globalFineWords, globalContainingLabels, globalLawSamples,
    globalContainingSamples, Finset.filter_filter, and_left_comm, and_assoc, and_comm] using hcard

private noncomputable def globalCompatibleLawSamples {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) : Finset (GlobalLawSample g n ξ r W) := by
  classical
  exact (globalLawSamples g n ξ r W β).filter fun z ↦
    globalCompatible g n ξ r W z.1.val z.2

private theorem globalCompatibleSamples_card_factor {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    (globalCompatibleLawSamples g ξ r W β).card =
      (globalFineWords g ξ r W β).card *
        (globalCompatibleLabels g ξ r W
          (globalFirstLawSample g n ξ r W β).2).card := by
  classical
  let S := g.perm r (if W = 0 then .Y else .Z)
  let a := (globalFirstLawSample g n ξ r W β).2
  have haMem := globalFirstLawSample_mem g ξ r W β
  have haLaw : globalEmpiricalLaw g n ξ r S a = β.val :=
    (Finset.mem_filter.mp haMem).2
  have hcard := card_filter_prod_eq
    (fun j : {j // j ∈ (globalPopulation g n ξ r).target} ↦ fun x ↦
      globalCoarseContains g n ξ r S j.val x ∧ globalCompatible g n ξ r W j.val x)
    (fun x ↦ globalEmpiricalLaw g n ξ r S x = β.val)
    (globalCompatibleLabels g ξ r W a).card
    (fun x hx ↦ by
      calc
        _ = (globalCompatibleLabels g ξ r W x).card := by
          unfold globalCompatibleLabels
          simpa only [S] using
            (targetSubtype_filter_card (globalPopulation g n ξ r).target
              (fun j ↦ globalCoarseContains g n ξ r S j x ∧
                globalCompatible g n ξ r W j x))
        _ = _ := globalCompatibleLabels_card_eq g ξ r W x a
          (hx.trans haLaw.symm))
  simpa only [S, a, globalFineWords, globalCompatibleLawSamples,
    globalCompatibleLabels, globalLawSamples,
    globalContainingSamples, Finset.filter_filter, and_left_comm, and_assoc, and_comm] using hcard

private theorem globalJointP_pos {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    0 < globalJointP g n ξ r W β := by
  classical
  unfold globalJointP
  apply div_pos
  · exact_mod_cast Finset.card_pos.mpr (globalLawSamples_nonempty g ξ r W β)
  · exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(globalLawSamples_nonempty g ξ r W β).choose⟩

private theorem globalJointP_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    globalJointP g n ξ r W β =
      ((globalLawSamples g n ξ r W β).card : ℝ) /
        Fintype.card (GlobalLawSample g n ξ r W) := by
  rfl

private theorem globalJointQ_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    globalJointQ g n ξ r W β =
      ((globalCompatibleLawSamples g ξ r W β).card : ℝ) /
        Fintype.card (GlobalLawSample g n ξ r W) := by
  rfl

private theorem globalPcomp_eq {w n : ℕ} (g : GlobalSpec w)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r W) :
    globalPcomp g n ξ r W β =
      ((globalCompatibleLabels g ξ r W
        (globalFirstLawSample g n ξ r W β).2).card : ℝ) /
      (globalContainingLabels g ξ r
        (g.perm r (if W = 0 then .Y else .Z))
        (globalFirstLawSample g n ξ r W β).2).card := by
  classical
  unfold globalPcomp globalCompatibleLabels globalContainingLabels
  dsimp only
  rw [Finset.filter_filter]

private theorem nat_ratio_cancel (words incident compatible total : ℕ)
    (hwords : (words : ℝ) ≠ 0) (hincident : (incident : ℝ) ≠ 0)
    (htotal : (total : ℝ) ≠ 0) :
    (compatible : ℝ) / incident =
      ((words * compatible : ℕ) : ℝ) / total /
        (((words * incident : ℕ) : ℝ) / total) := by
  push_cast
  field_simp

theorem global_compatibility_quotient {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (ξ : ExactGrid g (b*m)) (hξ : GridBoundaryCompatible ξ)
    (r : Fin 6) (W : Fin 2) (β : GlobalRepresentedLaw g (b*m) ξ r W) :
  0 < globalJointP g (b*m) ξ r W β ∧
    globalPcomp g (b*m) ξ r W β =
      globalJointQ g (b*m) ξ r W β / globalJointP g (b*m) ξ r W β := by
  constructor
  · exact globalJointP_pos g ξ r W β
  · classical
    let S := g.perm r (if W = 0 then .Y else .Z)
    let a := (globalFirstLawSample g (b*m) ξ r W β).2
    let words := globalFineWords g ξ r W β
    let incident := globalContainingLabels g ξ r S a
    let compatible := globalCompatibleLabels g ξ r W a
    let total := Fintype.card (GlobalLawSample g (b*m) ξ r W)
    have haMem := globalFirstLawSample_mem g ξ r W β
    have haContaining : globalCoarseContains g (b*m) ξ r S
        (globalFirstLawSample g (b*m) ξ r W β).1.val a :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp haMem).1).2
    have haLaw : globalEmpiricalLaw g (b*m) ξ r S a = β.val :=
      (Finset.mem_filter.mp haMem).2
    have hwordsNat : 0 < words.card := Finset.card_pos.mpr ⟨a, by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haLaw⟩⟩
    have hincidentNat : 0 < incident.card := Finset.card_pos.mpr
      ⟨(globalFirstLawSample g (b*m) ξ r W β).1.val, by
        exact Finset.mem_filter.mpr
          ⟨(globalFirstLawSample g (b*m) ξ r W β).1.property, haContaining⟩⟩
    have htotalNat : 0 < total := Fintype.card_pos_iff.mpr
      ⟨globalFirstLawSample g (b*m) ξ r W β⟩
    have hwords : (words.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hwordsNat
    have hincident : (incident.card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hincidentNat
    have htotal : (total : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt htotalNat
    rw [globalPcomp_eq, globalJointQ_eq, globalJointP_eq,
      globalLawSamples_card_factor, globalCompatibleSamples_card_factor]
    change (compatible.card : ℝ) / incident.card =
      ((words.card * compatible.card : ℕ) : ℝ) / total /
        (((words.card * incident.card : ℕ) : ℝ) / total)
    exact nat_ratio_cancel words.card incident.card compatible.card total
      hwords hincident htotal

end OmegaBound.ADVXXZGeneral
end
