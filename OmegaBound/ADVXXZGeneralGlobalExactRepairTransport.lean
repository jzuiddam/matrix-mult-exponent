import OmegaBound.ADVXXZGeneralAmend27GExactNear

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open OmegaBound.ADVXXZShuf
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Target labels of one global population have the prescribed shape histogram. -/
theorem globalTargetHistogram27 {w n : ℕ} (g : GlobalSpec w) (xi : ExactGrid g n)
    (r : Fin 6) (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target) (v : Shape w) :
    histogram27 j.val v = ((n : ℚ) * g.joint.prob (r, v)).floor.toNat := by
  have h := (Finset.mem_filter.mp hj).2 v
  simpa only [histogram27] using h

/-- The shape-preserving permutation carrying one target label to another. -/
def globalLabelPosEquiv27 {w n : ℕ} (g : GlobalSpec w) (xi : ExactGrid g n)
    (r : Fin 6) (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) :
    Equiv.Perm (Fin (globalPopulation g n xi r).n) :=
  histogramEquiv27 j.val k.val fun v =>
    (globalTargetHistogram27 g xi r j hj v).trans
      (globalTargetHistogram27 g xi r k hk v).symm

/-- The global target-label permutation preserves the physical shape at every position. -/
theorem globalLabelPosEquiv27_spec {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target)
    (i : Fin (globalPopulation g n xi r).n) :
    k.val (globalLabelPosEquiv27 g xi r j k hj hk i) = j.val i := by
  exact histogramEquiv27_spec j.val k.val
    (fun v => (globalTargetHistogram27 g xi r j hj v).trans
      (globalTargetHistogram27 g xi r k hk v).symm) i

/-- Relabelling positions transports the full global incidence predicate. -/
theorem globalIncidence_relabel27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side)
    (a : (globalPopulation g n xi r).Part W) :
    (globalPopulation g n xi r).incidence W j a ↔
      (globalPopulation g n xi r).incidence W k
        (a ∘ (globalLabelPosEquiv27 g xi r j k hj hk).symm) := by
  let e := globalLabelPosEquiv27 g xi r j k hj hk
  change ((∀ i, chunkLvl (a i) = coord W (j.val i)) ∧
      ∀ u sigma, (Finset.univ.filter fun i => j.val i = u ∧ a i = sigma).card =
        xi.count W r u sigma) ↔
    ((∀ i, chunkLvl ((a ∘ e.symm) i) = coord W (k.val i)) ∧
      ∀ u sigma, (Finset.univ.filter fun i =>
        k.val i = u ∧ (a ∘ e.symm) i = sigma).card = xi.count W r u sigma)
  have hshape (i : Fin (globalPopulation g n xi r).n) :
      k.val i = j.val (e.symm i) := by
    have h := globalLabelPosEquiv27_spec g xi r j k hj hk (e.symm i)
    simpa only [e, Equiv.apply_symm_apply] using h
  have hcount (u : Shape w) (sigma : Chunk w) :
      (Finset.univ.filter fun i => k.val i = u ∧ (a ∘ e.symm) i = sigma).card =
        (Finset.univ.filter fun i => j.val i = u ∧ a i = sigma).card := by
    let f := fun i : Fin (globalPopulation g n xi r).n => (j.val i, a i)
    have hf : (fun i : Fin (globalPopulation g n xi r).n =>
        (k.val i, (a ∘ e.symm) i)) = fun i => f (e.symm i) := by
      funext i
      simp only [Function.comp_apply, f, hshape i]
    have hp := histogram_perm27 f e.symm (u, sigma)
    rw [← hf] at hp
    simpa only [histogram27, Prod.mk.injEq, f] using hp
  constructor
  · rintro ⟨hgrade, hhist⟩
    exact ⟨fun i => by simpa only [Function.comp_apply, hshape i] using hgrade (e.symm i),
      fun u sigma => (hcount u sigma).trans (hhist u sigma)⟩
  · rintro ⟨hgrade, hhist⟩
    refine ⟨fun i => ?_, fun u sigma => ?_⟩
    · have h := hgrade (e i)
      simpa only [Function.comp_apply, e, Equiv.symm_apply_apply,
        globalLabelPosEquiv27_spec g xi r j k hj hk i] using h
    · exact (hcount u sigma).symm.trans (hhist u sigma)

/-- Position relabelling on global physical words. -/
def globalLabelWordEquiv27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) :
    GlobalPhysicalWord q g n xi r ≃ GlobalPhysicalWord q g n xi r :=
  preComp (globalLabelPosEquiv27 g xi r j k hj hk).symm

/-- Position relabelling on global exact parts. -/
def globalLabelExactPartEquiv27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side) :
    GlobalExactPart27 g n xi r j W ≃ GlobalExactPart27 g n xi r k W :=
  Equiv.subtypeEquiv
    (preComp (globalLabelPosEquiv27 g xi r j k hj hk).symm)
    (globalIncidence_relabel27 g xi r j k hj hk W)

/-- Position relabelling on global exact tensor legs. -/
def globalLabelExactLegEquiv27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side) :
    GlobalExactLeg27 q g n xi r j W ≃ GlobalExactLeg27 q g n xi r k W :=
  Equiv.subtypeEquiv (globalLabelWordEquiv27 q g xi r j k hj hk)
    (fun x => globalIncidence_relabel27 g xi r j k hj hk W
      (globalPhysicalPart q g n xi r W x))

/-- Relabelling commutes with the exact-part projections. -/
theorem globalLabelExactPart_comm27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side)
    (x : GlobalExactLeg27 q g n xi r j W) :
    globalLabelExactPartEquiv27 q g xi r j k hj hk W
        (globalExactPart27 q g n xi r j W x) =
      globalExactPart27 q g n xi r k W
        (globalLabelExactLegEquiv27 q g xi r j k hj hk W x) := by
  rfl

/-- All target labels carry the same exact regional tensor, up to the shape-preserving relabelling. -/
theorem globalLabelExactTensor_equiv27 {w n : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target)
    (x : GlobalExactLeg27 q g n xi r j .X)
    (y : GlobalExactLeg27 q g n xi r j .Y)
    (z : GlobalExactLeg27 q g n xi r j .Z) :
    globalExactTensorZ27 q g n xi r k
        (globalLabelExactLegEquiv27 q g xi r j k hj hk .X x)
        (globalLabelExactLegEquiv27 q g xi r j k hj hk .Y y)
        (globalLabelExactLegEquiv27 q g xi r j k hj hk .Z z) =
      globalExactTensorZ27 q g n xi r j x y z := by
  let e := globalLabelPosEquiv27 g xi r j k hj hk
  let f := fun i : Fin (globalPopulation g n xi r).n =>
    conZ q w (coord .X (j.val i)) (coord .Y (j.val i)) (coord .Z (j.val i))
      (x.val i) (y.val i) (z.val i)
  change (∏ i, conZ q w (coord .X (k.val i)) (coord .Y (k.val i)) (coord .Z (k.val i))
      (x.val (e.symm i)) (y.val (e.symm i)) (z.val (e.symm i))) = ∏ i, f i
  calc
    _ = ∏ i, f (e.symm i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hs := globalLabelPosEquiv27_spec g xi r j k hj hk (e.symm i)
      have hshape : k.val i = j.val (e.symm i) := by
        simpa only [e, Equiv.apply_symm_apply] using hs
      rw [hshape]
    _ = ∏ i, f i := Equiv.prod_comp e.symm f

end
end OmegaBound.ADVXXZGeneral
end
