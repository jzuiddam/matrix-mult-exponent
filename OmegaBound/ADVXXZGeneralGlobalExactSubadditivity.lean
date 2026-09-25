import OmegaBound.ADVXXZGeneralGlobalExactCopiesBound
import OmegaBound.ADVXXZGeneralGlobalExactEntropyCaps

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

set_option maxHeartbeats 1000000 in
/--
**Subadditivity of base-two entropy along a pair of separating coordinates.**  If `i ↦ (f i, g i)`
is injective on a finite type, a probability vector's entropy is at most the sum of the entropies
of its two coordinate marginals.  Proved from the Gibbs inequality
`Entropy.H_le_sum_neg_mul_log` with the product comparison law `q i = m₁(f i)·m₂(g i)`, restricted
to the support where both marginals are positive.
-/
theorem entropy_le_add_marginals_of_injective27 {iota k1 k2 : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype k1] [DecidableEq k1]
    [Fintype k2] [DecidableEq k2]
    (p : iota → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (f : iota → k1) (g : iota → k2)
    (hinj : ∀ i j : iota, f i = f j → g i = g j → i = j) :
    entropy p ≤
      entropy (fun a => ∑ i ∈ Finset.univ.filter (fun i => f i = a), p i) +
      entropy (fun b => ∑ i ∈ Finset.univ.filter (fun i => g i = b), p i) := by
  classical
  set m1 : k1 → ℝ := fun a => ∑ i ∈ Finset.univ.filter (fun i => f i = a), p i with hm1def
  set m2 : k2 → ℝ := fun b => ∑ i ∈ Finset.univ.filter (fun i => g i = b), p i with hm2def
  have hm1nonneg : ∀ a, 0 ≤ m1 a := fun a => Finset.sum_nonneg (fun i _ => hp0 i)
  have hm2nonneg : ∀ b, 0 ≤ m2 b := fun b => Finset.sum_nonneg (fun i _ => hp0 i)
  have hm1sum : ∑ a, m1 a = 1 := by
    rw [hm1def]
    rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (f i)) p]
    exact hp1
  have hm2sum : ∑ b, m2 b = 1 := by
    rw [hm2def]
    rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (g i)) p]
    exact hp1
  have hple1 : ∀ i, p i ≤ m1 (f i) := by
    intro i
    exact Finset.single_le_sum (f := p) (fun j _ => hp0 j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
  have hple2 : ∀ i, p i ≤ m2 (g i) := by
    intro i
    exact Finset.single_le_sum (f := p) (fun j _ => hp0 j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
  set s : Finset iota :=
    Finset.univ.filter (fun i => 0 < m1 (f i) ∧ 0 < m2 (g i)) with hsdef
  have hmem_s : ∀ i, i ∈ s ↔ (0 < m1 (f i) ∧ 0 < m2 (g i)) := by
    intro i
    rw [hsdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hzero_out : ∀ i, i ∉ s → p i = 0 := by
    intro i hi
    rw [hmem_s i] at hi
    rcases not_and_or.mp hi with h | h
    · have h1 : m1 (f i) ≤ 0 := not_lt.mp h
      have := hple1 i
      linarith [hp0 i]
    · have h2 : m2 (g i) ≤ 0 := not_lt.mp h
      have := hple2 i
      linarith [hp0 i]
  have hsum_s : ∑ i ∈ s, p i = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero_out i hi)]
    exact hp1
  have hq_sum : ∑ i ∈ s, m1 (f i) * m2 (g i) ≤ 1 := by
    have hinj' : ∀ x ∈ s, ∀ y ∈ s, (f x, g x) = (f y, g y) → x = y := by
      intro x _ y _ hxy
      exact hinj x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
    have himg : (∑ z ∈ s.image (fun i => (f i, g i)),
        m1 z.1 * m2 z.2) = ∑ i ∈ s, m1 (f i) * m2 (g i) :=
      Finset.sum_image hinj'
    rw [← himg]
    have hsub : (∑ z ∈ s.image (fun i => (f i, g i)), m1 z.1 * m2 z.2) ≤
        ∑ z : k1 × k2, m1 z.1 * m2 z.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _ _
      exact mul_nonneg (hm1nonneg z.1) (hm2nonneg z.2)
    have htotal : (∑ z : k1 × k2, m1 z.1 * m2 z.2) = 1 := by
      rw [Fintype.sum_prod_type]
      have hrow : ∀ a : k1, (∑ b : k2, m1 a * m2 b) = m1 a := by
        intro a
        rw [← Finset.mul_sum, hm2sum, mul_one]
      simp_rw [hrow]
      exact hm1sum
    linarith
  have hgibbs := Entropy.H_le_sum_neg_mul_log (s := s) (p := p)
    (q := fun i => m1 (f i) * m2 (g i)) (fun i _ => hp0 i)
    (fun i hi => mul_pos ((hmem_s i).mp hi).1 ((hmem_s i).mp hi).2) hsum_s hq_sum
  have hsplit : (∑ i ∈ s, -(p i * Real.log (m1 (f i) * m2 (g i)))) =
      (∑ i ∈ s, -(p i * Real.log (m1 (f i)))) +
        ∑ i ∈ s, -(p i * Real.log (m2 (g i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Real.log_mul (ne_of_gt ((hmem_s i).mp hi).1) (ne_of_gt ((hmem_s i).mp hi).2)]
    ring
  have hterm1 : (∑ i ∈ s, -(p i * Real.log (m1 (f i)))) = Entropy.H Finset.univ m1 := by
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
      rw [hzero_out i hi]; ring)]
    rw [← Finset.sum_fiberwise_of_maps_to (fun (i : iota) _ => Finset.mem_univ (f i))
      (fun i => -(p i * Real.log (m1 (f i))))]
    simp only [Entropy.H]
    refine Finset.sum_congr rfl ?_
    intro a _
    have hcongr : ∀ i ∈ Finset.univ.filter (fun i => f i = a),
        -(p i * Real.log (m1 (f i))) = -(p i * Real.log (m1 a)) := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, ← Finset.sum_mul,
      Entropy.negMulLog_eq]
  have hterm2 : (∑ i ∈ s, -(p i * Real.log (m2 (g i)))) = Entropy.H Finset.univ m2 := by
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
      rw [hzero_out i hi]; ring)]
    rw [← Finset.sum_fiberwise_of_maps_to (fun (i : iota) _ => Finset.mem_univ (g i))
      (fun i => -(p i * Real.log (m2 (g i))))]
    simp only [Entropy.H]
    refine Finset.sum_congr rfl ?_
    intro b _
    have hcongr : ∀ i ∈ Finset.univ.filter (fun i => g i = b),
        -(p i * Real.log (m2 (g i))) = -(p i * Real.log (m2 b)) := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, ← Finset.sum_mul,
      Entropy.negMulLog_eq]
  have hHp : Entropy.H Finset.univ p = Entropy.H s p := by
    simp only [Entropy.H]
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
      rw [hzero_out i hi]; simp)]
  have hmain : Entropy.H Finset.univ p ≤
      Entropy.H Finset.univ m1 + Entropy.H Finset.univ m2 := by
    rw [hHp, ← hterm1, ← hterm2, ← hsplit]
    exact hgibbs
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  simp only [entropy, Entropy.H₂]
  rw [div_add_div_same, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hlog2.le)

section ShapeSubadditivity
variable {w : ℕ}

/-- Two distinct shape coordinates determine the third, hence the shape. -/
theorem shapeCoordFin_injective27 (X Y : Side) (hXY : X ≠ Y) :
    ∀ u v : Shape w, Parent25.coordFin X u = Parent25.coordFin X v →
      Parent25.coordFin Y u = Parent25.coordFin Y v → u = v := by
  intro u v hx hy
  have hu : (u.val.1 : ℕ) + (u.val.2.1 : ℕ) + (u.val.2.2 : ℕ) = 2 * w := u.property
  have hv : (v.val.1 : ℕ) + (v.val.2.1 : ℕ) + (v.val.2.2 : ℕ) = 2 * w := v.property
  have hxn : ((Parent25.coordFin X u : Fin (2 * w + 1)) : ℕ) =
      ((Parent25.coordFin X v : Fin (2 * w + 1)) : ℕ) := congrArg Fin.val hx
  have hyn : ((Parent25.coordFin Y u : Fin (2 * w + 1)) : ℕ) =
      ((Parent25.coordFin Y v : Fin (2 * w + 1)) : ℕ) := congrArg Fin.val hy
  have key : (u.val.1 : ℕ) = (v.val.1 : ℕ) ∧ (u.val.2.1 : ℕ) = (v.val.2.1 : ℕ) ∧
      (u.val.2.2 : ℕ) = (v.val.2.2 : ℕ) := by
    cases X <;> cases Y <;>
      simp only [Parent25.coordFin] at hxn hyn <;>
      first
        | exact absurd rfl hXY
        | omega
  apply Subtype.ext
  simp only [Prod.ext_iff]
  exact ⟨Fin.eq_of_val_eq key.1, Fin.eq_of_val_eq key.2.1, Fin.eq_of_val_eq key.2.2⟩

/-- The paper's `marginal` is the coordinate fibre sum. -/
theorem marginal_eq_fiberSum27 (p : Shape w → ℝ) (W : Side) :
    (fun a => ∑ u ∈ Finset.univ.filter (fun u => Parent25.coordFin W u = a), p u) =
      marginal p W := by
  classical
  funext a
  unfold marginal
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h : Parent25.coordFin W u = a
  · rw [if_pos h, if_pos]
    cases W <;> exact congrArg Fin.val h
  · rw [if_neg h, if_neg]
    intro hc
    apply h
    apply Fin.eq_of_val_eq
    cases W <;> exact hc

/--
**Entropy subadditivity on shapes.**  For any two distinct sides, a probability law on `Shape w`
has entropy at most the sum of the entropies of those two coordinate marginals.  This is one
half of `penalty p ≤ entropy (marginal p X)`; the other half,
`entropy (marginal p W) ≤ entropy p`, is carried out inside
`ADVXXZGeneralGlobalExactDemandBound`.
-/
theorem entropy_le_add_marginals27 (p : Shape w → ℝ)
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1) (X Y : Side) (hXY : X ≠ Y) :
    entropy p ≤ entropy (marginal p X) + entropy (marginal p Y) := by
  classical
  have h := entropy_le_add_marginals_of_injective27 p hp0 hp1
    (Parent25.coordFin X) (Parent25.coordFin Y) (shapeCoordFin_injective27 X Y hXY)
  rwa [marginal_eq_fiberSum27 p X, marginal_eq_fiberSum27 p Y] at h


end ShapeSubadditivity

end
end OmegaBound.ADVXXZGeneral
end
