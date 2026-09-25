import OmegaBound.ADVXXZGeneralCExact37Survival

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem filter_card_eq_of_perm37 {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ => e i) (fun i _ => e.symm i) ?_ ?_ ?_ ?_
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

private theorem exists_perm_of_typeCnt37
    {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (x y : Fin n → A) (h : ∀ a, typeCnt x a = typeCnt y a) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, y (e i) = x i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // x i = a} ≃ {i // y i = a}) :=
    ⟨fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), fun i => ?_⟩
  exact (e (x i) ⟨i, rfl⟩).2

set_option maxHeartbeats 2000000 in
-- Unfolding the dependent stage-label marginal and complement laws is elaboration-heavy.
private noncomputable def stageLabelReindex37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (e : ∀ t : Fin s,
      Equiv.Perm (Fin (StageCandidateRaw.stageParentCount b m p d r t))) :
    (stagePopulationAt q p d b m r).Label ≃
      (stagePopulationAt q p d b m r).Label := by
  classical
  unfold stagePopulationAt
  dsimp only
  refine
    { toFun := fun j => ⟨fun z => j.val ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩, ?_⟩
      invFun := fun j => ⟨fun z => j.val ⟨z.1, (e z.1 z.2.1, z.2.2)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro t h W a
      exact (filter_card_eq_of_perm37 (e t).symm _ _ (fun _ => Iff.rfl)).trans
        (j.property.1 t h W a)
    · intro t i
      exact j.property.2 t ((e t).symm i)
  · constructor
    · intro t h W a
      exact (filter_card_eq_of_perm37 (e t) _ _ (fun _ => Iff.rfl)).trans
        (j.property.1 t h W a)
    · intro t i
      exact j.property.2 t (e t i)
  · intro j
    apply Subtype.ext
    funext z
    change j.val ⟨z.1, ((e z.1).symm ((e z.1) z.2.1), z.2.2)⟩ = j.val z
    rw [(e z.1).symm_apply_apply]
  · intro j
    apply Subtype.ext
    funext z
    change j.val ⟨z.1, ((e z.1) ((e z.1).symm z.2.1), z.2.2)⟩ = j.val z
    rw [(e z.1).apply_symm_apply]

private theorem coord_complement_eq37 {w s : ℕ} (p : ConstituentInput w s)
    (t : Fin s) (W : Side) (u v : ChildShape p t)
    (h : coord W u.val = coord W v.val) :
    coord W (complement p t u).val = coord W (complement p t v).val := by
  cases W <;>
    simp only [coord] at h ⊢ <;>
    simp [complement, coord, h]

private theorem stage_half_typeCnt_eq37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label) (t : Fin s) (W : Side)
    (a : Fin (2 * w + 1)) :
    typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
        Parent25.coordFin W (j.val ⟨t, (i, 0)⟩).val) a =
      typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
        Parent25.coordFin W (k.val ⟨t, (i, 0)⟩).val) a := by
  classical
  unfold stagePopulationAt at j k
  dsimp only at j k ⊢
  exact (j.property.1 t 0 W a).trans (k.property.1 t 0 W a).symm

private theorem stage_coarse_eq_iff_of_equiv37 {w s b m n : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (E : Parent25.Pos p d b m r ≃ Fin n)
    (j k : (z : Parent25.Pos p d b m r) → ChildShape p z.1) (W : Side) :
    (fun i => Parent25.coordFin W (j (E.symm i)).val) =
        (fun i => Parent25.coordFin W (k (E.symm i)).val) ↔
      ∀ z, coord W (j z).val = coord W (k z).val := by
  constructor
  · intro h z
    have hz := congrArg Fin.val (congrFun h (E z))
    have he : E.symm (E z) = z := E.symm_apply_apply z
    rw [he] at hz
    cases W <;> simpa [Parent25.coordFin, coord] using hz
  · intro h
    funext i
    apply Fin.ext
    have hi := h (E.symm i)
    cases W <;> simpa [Parent25.coordFin, coord] using hi

private theorem stage_role_coarse_eq_iff_coords37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label) (S : Side) :
    (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j S =
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse k S ↔
      ∀ z : Parent25.Pos p d b m r,
        coord (d.perm r S) (j.val z).val = coord (d.perm r S) (k.val z).val := by
  dsimp [rolePopulation, stagePopulationAt]
  exact stage_coarse_eq_iff_of_equiv37 p d r _ _ _ (d.perm r S)

private theorem stageLabelReindex37_apply {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (e : ∀ t : Fin s,
      Equiv.Perm (Fin (StageCandidateRaw.stageParentCount b m p d r t)))
    (j : (stagePopulationAt q p d b m r).Label)
    (z : Parent25.Pos p d b m r) :
    (stageLabelReindex37 q p d r e j).val z =
      j.val ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩ := by
  unfold stageLabelReindex37
  rfl

private theorem stage_label_complement37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    j.val ⟨t, (i, 1)⟩ = complement p t (j.val ⟨t, (i, 0)⟩) := by
  unfold stagePopulationAt at j
  exact j.property.2 t i

set_option maxHeartbeats 2000000 in
-- The fibre bijection carries dependent stage labels and six role permutations.
theorem stage_role_hashXFiber_card_eq37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : (stagePopulationAt q p d b m r).Label) :
    (hashXFiber27
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j).card =
      (hashXFiber27
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) k).card := by
  classical
  let W := d.perm r .X
  have htypes : ∀ t : Fin s, ∀ a : Fin (2 * w + 1),
      typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          Parent25.coordFin W (j.val ⟨t, (i, 0)⟩).val) a =
        typeCnt (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
          Parent25.coordFin W (k.val ⟨t, (i, 0)⟩).val) a :=
    fun t a => stage_half_typeCnt_eq37 q p d r j k t W a
  choose e he using fun t => exists_perm_of_typeCnt37
    (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      Parent25.coordFin W (j.val ⟨t, (i, 0)⟩).val)
    (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) =>
      Parent25.coordFin W (k.val ⟨t, (i, 0)⟩).val) (htypes t)
  let phi := stageLabelReindex37 q p d r e
  have hpair (t : Fin s)
      (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) (h : Fin 2) :
      coord W (j.val ⟨t, ((e t).symm i, h)⟩).val =
        coord W (k.val ⟨t, (i, h)⟩).val := by
    fin_cases h
    · change coord W (j.val ⟨t, ((e t).symm i, (0 : Fin 2))⟩).val =
        coord W (k.val ⟨t, (i, (0 : Fin 2))⟩).val
      have hi := he t ((e t).symm i)
      rw [(e t).apply_symm_apply] at hi
      have hi' := congrArg Fin.val hi.symm
      generalize hS : W = S at hi' ⊢
      cases S <;> simpa [Parent25.coordFin, coord] using hi'
    · change coord W (j.val ⟨t, ((e t).symm i, (1 : Fin 2))⟩).val =
        coord W (k.val ⟨t, (i, (1 : Fin 2))⟩).val
      rw [stage_label_complement37 q p d r j t,
        stage_label_complement37 q p d r k t]
      apply coord_complement_eq37
      have hi := he t ((e t).symm i)
      rw [(e t).apply_symm_apply] at hi
      have hi' := congrArg Fin.val hi.symm
      generalize hS : W = S at hi' ⊢
      cases S <;> simpa [Parent25.coordFin, coord] using hi'
  have hmem (l : (stagePopulationAt q p d b m r).Label) :
      l ∈ hashXFiber27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j ↔
        phi l ∈ hashXFiber27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) k := by
    simp only [hashXFiber27, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hl
      apply (stage_role_coarse_eq_iff_coords37 q p d r (phi l) k .X).2
      have hlc := (stage_role_coarse_eq_iff_coords37 q p d r l j .X).1 hl
      intro z
      rw [stageLabelReindex37_apply]
      exact (hlc ⟨z.1, ((e z.1).symm z.2.1, z.2.2)⟩).trans
        (hpair z.1 z.2.1 z.2.2)
    · intro hl
      apply (stage_role_coarse_eq_iff_coords37 q p d r l j .X).2
      have hlc := (stage_role_coarse_eq_iff_coords37 q p d r (phi l) k .X).1 hl
      intro z
      have hz := hlc ⟨z.1, (e z.1 z.2.1, z.2.2)⟩
      rw [stageLabelReindex37_apply, (e z.1).symm_apply_apply] at hz
      have hp := hpair z.1 (e z.1 z.2.1) z.2.2
      rw [(e z.1).symm_apply_apply] at hp
      exact hz.trans hp.symm
  refine Finset.card_bij' (fun l _ => phi l) (fun l _ => phi.symm l) ?_ ?_ ?_ ?_
  · intro l hl
    exact (hmem l).1 hl
  · intro l hl
    apply (hmem (phi.symm l)).2
    simpa using hl
  · intro l _
    exact phi.symm_apply_apply l
  · intro l _
    exact phi.apply_symm_apply l

/-- Uniform role-X fibres partition the complete constituent stage-label space. -/
theorem stage_role_hashXFiber_mul_image37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) :
    (hashXFiber27
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j).card *
      (hashXImage27
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))).card =
      Fintype.card (stagePopulationAt q p d b m r).Label := by
  classical
  let RP := rolePopulation (stagePopulationAt q p d b m r) (d.perm r)
  have hpartition : Fintype.card RP.Label =
      ∑ x ∈ hashXImage27 RP,
        ((Finset.univ : Finset RP.Label).filter fun k => RP.coarse k .X = x).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset RP.Label))
        (t := hashXImage27 RP) (f := fun k => RP.coarse k .X)
        (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  calc
    (hashXFiber27 RP j).card * (hashXImage27 RP).card =
        ∑ _x ∈ hashXImage27 RP, (hashXFiber27 RP j).card := by simp [Nat.mul_comm]
    _ = ∑ x ∈ hashXImage27 RP,
        ((Finset.univ : Finset RP.Label).filter fun k => RP.coarse k .X = x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx
      subst x
      exact stage_role_hashXFiber_card_eq37 q p d r j k
    _ = Fintype.card RP.Label := hpartition.symm

/-- The constituent demand therefore gives the paper's unconditional `3/4` target-bucket
survival estimate on the real paired-parent stage population. -/
theorem stageTargetBucket_survival37 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor ε m r ≤ M)
    (j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B) :
    (3 : ℝ) / 4 ≤ cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega => j ∈ stageSelectedTargets37 q p d r B omega) :=
  stageTargetBucket_survival_of_demand37 q floor p d hd ε r B hprime hodd hfloor
    hdemand j z (stage_role_hashXFiber_mul_image37 q p d r j.val)

end
end OmegaBound.ADVXXZGeneral
