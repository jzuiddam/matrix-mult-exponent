import OmegaBound.ADVXXZGeneralGlobalExactBrokenAssembly

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private abbrev GlobalGridLegReindex27 {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ) :=
  (t : Fin (Fintype.card (Fin 6 × Shape w))) →
    Fin (((n : ℚ) * g.joint.prob
      ((Fintype.equivFin (Fin 6 × Shape w)).symm t)).floor.toNat) →
      Fin w → CW90.Idx7 q

private def globalGridKeepReindex27 {q w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (xi : ExactGrid g n) (W : Side)
    (x : GlobalGridLegReindex27 q g n) : Prop :=
  ∀ t sigma, typeCnt (chunkSeq (x t)) sigma =
    xi.count W ((Fintype.equivFin (Fin 6 × Shape w)).symm t).1
      ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2 sigma

private def globalGridRawReindex27 {w : ℕ} (q : ℕ) (g : GlobalSpec w) (n : ℕ) :
    Tensor3 ℤ (GlobalGridLegReindex27 q g n) (GlobalGridLegReindex27 q g n)
      (GlobalGridLegReindex27 q g n) :=
  fun x y z => ∏ t,
    tensorPower (conZ q w
      (coord .X ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Y ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Z ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2))
      (((n : ℚ) * g.joint.prob
        ((Fintype.equivFin (Fin 6 × Shape w)).symm t)).floor.toNat)
      (x t) (y t) (z t)

private theorem exactGridTensor_tensor_eq_zoPReindex27 {q w n : ℕ}
    (g : GlobalSpec w) (xi : ExactGrid g n) :
    (exactGridTensor q g n xi).tensor =
      zoP (globalGridKeepReindex27 g n xi .X)
        (globalGridKeepReindex27 g n xi .Y)
        (globalGridKeepReindex27 g n xi .Z)
        (globalGridRawReindex27 q g n) := by
  funext x y z
  simp only [exactGridTensor, globalGridKeepReindex27, globalGridRawReindex27, zoP]

private def globalGridCellReindex27 {w : ℕ} (r : Fin 6) (u : Shape w) :
    Fin (Fintype.card (Fin 6 × Shape w)) :=
  Fintype.equivFin (Fin 6 × Shape w) (r, u)

@[simp] private theorem globalGridCellReindex27_spec {w : ℕ} (r : Fin 6)
    (u : Shape w) :
    (Fintype.equivFin (Fin 6 × Shape w)).symm
      (globalGridCellReindex27 r u) = (r, u) :=
  (Fintype.equivFin (Fin 6 × Shape w)).symm_apply_apply (r, u)

/-- Positions of a target label having a fixed physical shape are exactly the positions
    of the corresponding cell of `exactGridTensor`. -/
def globalGridShapePositionEquiv27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target) (u : Shape w) :
    {i : Fin (globalPopulation g n xi r).n // j.val i = u} ≃
      Fin (((n : ℚ) * g.joint.prob
        ((Fintype.equivFin (Fin 6 × Shape w)).symm
          (globalGridCellReindex27 r u))).floor.toNat) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_subtype, Fintype.card_fin,
    globalGridCellReindex27_spec]
  exact globalTargetHistogram27 g xi r j hj u

private def globalGridToRegionalWord27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (x : GlobalGridLegReindex27 q g n) : GlobalPhysicalWord q g n xi r :=
  fun i => x (globalGridCellReindex27 r (j.val i))
    (globalGridShapePositionEquiv27 g xi r j hj (j.val i) ⟨i, rfl⟩)

private theorem globalGridToRegionalWord_at_fibre27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (x : GlobalGridLegReindex27 q g n) (u : Shape w)
    (i : {i : Fin (globalPopulation g n xi r).n // j.val i = u}) :
    globalGridToRegionalWord27 q g xi r j hj x i.val =
      x (globalGridCellReindex27 r u)
        (globalGridShapePositionEquiv27 g xi r j hj u i) := by
  rcases i with ⟨i, hi⟩
  subst u
  rfl

private theorem globalGridWordHistogram27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (x : GlobalGridLegReindex27 q g n) (u : Shape w) (sigma : Chunk w) :
    histogram27 (fun i =>
      (j.val i, chunkOf (globalGridToRegionalWord27 q g xi r j hj x i))) (u, sigma) =
      typeCnt (chunkSeq (x (globalGridCellReindex27 r u))) sigma := by
  classical
  let e := globalGridShapePositionEquiv27 g xi r j hj u
  unfold histogram27 typeCnt
  apply Finset.card_bij (fun i hi =>
    e ⟨i, congrArg Prod.fst (Finset.mem_filter.mp hi).2⟩)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsnd := congrArg Prod.snd hi.2
    rw [globalGridToRegionalWord_at_fibre27 q g xi r j hj x u
      ⟨i, congrArg Prod.fst hi.2⟩] at hsnd
    exact hsnd
  · intro i₁ h₁ i₂ h₂ heq
    apply e.injective at heq
    exact congrArg Subtype.val heq
  · intro k hk
    refine ⟨(e.symm k).val, ?_, ?_⟩
    · rw [Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ _, Prod.ext (e.symm k).property ?_⟩
      rw [globalGridToRegionalWord_at_fibre27 q g xi r j hj x u (e.symm k),
        e.apply_symm_apply]
      exact hk.2
    · exact e.apply_symm_apply k

private def globalGridToExactRegionalLeg27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target) (W : Side)
    (x : {x : GlobalGridLegReindex27 q g n //
      globalGridKeepReindex27 g n xi W x}) :
    GlobalExactLeg27 q g n xi r j W := by
  let a := globalGridToRegionalWord27 q g xi r j hj x.val
  refine ⟨a, ?_⟩
  change (∀ i, chunkLvl (chunkOf (a i)) = coord W (j.val i)) ∧
    ∀ u sigma, (Finset.univ.filter fun i =>
      j.val i = u ∧ chunkOf (a i) = sigma).card = xi.count W r u sigma
  constructor
  · intro i
    let u := j.val i
    let sigma := chunkOf (a i)
    have hhist : 0 < histogram27 (fun k => (j.val k, chunkOf (a k))) (u, sigma) := by
      unfold histogram27
      rw [Finset.card_pos]
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hcount : 0 < xi.count W r u sigma := by
      rw [globalGridWordHistogram27 q g xi r j hj x.val u sigma,
        x.property (globalGridCellReindex27 r u) sigma] at hhist
      simpa using hhist
    by_contra hlevel
    have hz := xi.graded W r u sigma hlevel
    omega
  · intro u sigma
    simpa only [histogram27, a, Prod.mk.injEq] using
      (globalGridWordHistogram27 q g xi r j hj x.val u sigma).trans
        (by simpa using x.property (globalGridCellReindex27 r u) sigma)

private theorem globalExactTensor_gridCells27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (x : {x : GlobalGridLegReindex27 q g n //
      globalGridKeepReindex27 g n xi .X x})
    (y : {y : GlobalGridLegReindex27 q g n //
      globalGridKeepReindex27 g n xi .Y y})
    (z : {z : GlobalGridLegReindex27 q g n //
      globalGridKeepReindex27 g n xi .Z z}) :
    globalExactTensorZ27 q g n xi r j
        (globalGridToExactRegionalLeg27 q g xi r j hj .X x)
        (globalGridToExactRegionalLeg27 q g xi r j hj .Y y)
        (globalGridToExactRegionalLeg27 q g xi r j hj .Z z) =
      ∏ u : Shape w,
        tensorPower (conZ q w (coord .X u) (coord .Y u) (coord .Z u))
          (((n : ℚ) * g.joint.prob
            ((Fintype.equivFin (Fin 6 × Shape w)).symm
              (globalGridCellReindex27 r u))).floor.toNat)
          (x.val (globalGridCellReindex27 r u))
          (y.val (globalGridCellReindex27 r u))
          (z.val (globalGridCellReindex27 r u)) := by
  classical
  unfold globalExactTensorZ27
  let F := fun i : Fin (globalPopulation g n xi r).n =>
    conZ q w (coord .X (j.val i)) (coord .Y (j.val i)) (coord .Z (j.val i))
      ((globalGridToExactRegionalLeg27 q g xi r j hj .X x).val i)
      ((globalGridToExactRegionalLeg27 q g xi r j hj .Y y).val i)
      ((globalGridToExactRegionalLeg27 q g xi r j hj .Z z).val i)
  change (∏ i, F i) = _
  calc
    _ = ∏ u : Shape w, ∏ i : {i // j.val i = u}, F i.val :=
      (Fintype.prod_fiberwise j.val F).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro u _
      let e := globalGridShapePositionEquiv27 g xi r j hj u
      let f := fun k =>
        conZ q w (coord .X u) (coord .Y u) (coord .Z u)
          (x.val (globalGridCellReindex27 r u) k)
          (y.val (globalGridCellReindex27 r u) k)
          (z.val (globalGridCellReindex27 r u) k)
      change (∏ i : {i // j.val i = u}, F i.val) = ∏ k, f k
      calc
        _ = ∏ i : {i // j.val i = u}, f (e i) := by
          apply Finset.prod_congr rfl
          intro i _
          change conZ q w (coord .X (j.val i.val)) (coord .Y (j.val i.val))
            (coord .Z (j.val i.val)) _ _ _ = _
          rw [show j.val i.val = u from i.property]
          simp only [f, e, globalGridToExactRegionalLeg27]
          rw [globalGridToRegionalWord_at_fibre27 q g xi r j hj x.val u i,
            globalGridToRegionalWord_at_fibre27 q g xi r j hj y.val u i,
            globalGridToRegionalWord_at_fibre27 q g xi r j hj z.val u i]
        _ = _ := Equiv.prod_comp e f

private theorem globalGridRaw_reindex27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (x y z : GlobalGridLegReindex27 q g n) :
    globalGridRawReindex27 q g n x y z =
      ∏ r : Fin 6, ∏ u : Shape w,
        tensorPower (conZ q w (coord .X u) (coord .Y u) (coord .Z u))
          (((n : ℚ) * g.joint.prob
            ((Fintype.equivFin (Fin 6 × Shape w)).symm
              (globalGridCellReindex27 r u))).floor.toNat)
          (x (globalGridCellReindex27 r u))
          (y (globalGridCellReindex27 r u))
          (z (globalGridCellReindex27 r u)) := by
  classical
  let e := Fintype.equivFin (Fin 6 × Shape w)
  let f := fun t : Fin (Fintype.card (Fin 6 × Shape w)) =>
    tensorPower (conZ q w
      (coord .X ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Y ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Z ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2))
      (((n : ℚ) * g.joint.prob
        ((Fintype.equivFin (Fin 6 × Shape w)).symm t)).floor.toNat)
      (x t) (y t) (z t)
  change (∏ t, f t) = _
  calc
    _ = ∏ ru : Fin 6 × Shape w, f (e ru) := (Equiv.prod_comp e f).symm
    _ = _ := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro r _
      apply Finset.prod_congr rfl
      intro u _
      simp only [f, e, globalGridCellReindex27, Equiv.symm_apply_apply]

private theorem boxZO_restricts_subtypeGrid27
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

private theorem zoP_restricts_subtypeGrid27
    {R X Y Z : Type*} [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (pX : X → Prop) [DecidablePred pX] (pY : Y → Prop) [DecidablePred pY]
    (pZ : Z → Prop) [DecidablePred pZ] (T : Tensor3 R X Y Z) :
    Restricts (zoP pX pY pZ T)
      (fun x : {x // pX x} => fun y : {y // pY y} =>
        fun z : {z // pZ z} => T x.val y.val z.val) := by
  rw [zoP_eq_boxZO]
  have hbox := boxZO_restricts_subtypeGrid27 (fun x => decide (pX x))
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
    apply ADVXXZ.restricts_of_sub fX fY fZ
    intro x y z
    rfl
  exact Tensor3.Restricts.trans hbox hrename

set_option maxHeartbeats 1000000 in
-- The dependent substitution type requires the larger elaboration budget.
/-- The literal six-region exact tensor on any family of target labels contains precisely
    the kept exact-grid tensor, including its zero extension on non-histogram words. -/
theorem globalSixRegionExactGrid27 {q w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n)
    (j : (r : Fin 6) → (globalPopulation g n xi r).Label)
    (hj : ∀ r, j r ∈ (globalPopulation g n xi r).target) :
    Restricts (exactGridTensor q g n xi).tensor
      (regionProductZ fun r => globalExactITensor27 q g xi r (j r)).tensor := by
  classical
  rw [exactGridTensor_tensor_eq_zoPReindex27]
  have hsub := zoP_restricts_subtypeGrid27
    (globalGridKeepReindex27 g n xi .X)
    (globalGridKeepReindex27 g n xi .Y)
    (globalGridKeepReindex27 g n xi .Z)
    (globalGridRawReindex27 q g n)
  apply Tensor3.Restricts.trans hsub
  apply ADVXXZ.restricts_of_sub
    (fun x r => globalGridToExactRegionalLeg27 q g xi r (j r) (hj r) .X x)
    (fun y r => globalGridToExactRegionalLeg27 q g xi r (j r) (hj r) .Y y)
    (fun z r => globalGridToExactRegionalLeg27 q g xi r (j r) (hj r) .Z z)
  intro x y z
  rw [globalGridRaw_reindex27]
  simp only [regionProductZ]
  apply Finset.prod_congr rfl
  intro r _
  exact (globalExactTensor_gridCells27 q g xi r (j r) (hj r) x y z).symm


-- The full repaired-family telescope requires the larger elaboration budget.

end
end OmegaBound.ADVXXZGeneral
end
