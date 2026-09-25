import OmegaBound.ADVXXZGeneralGlobalExactRateX

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The zero-safe perspective identity for base-two entropy. -/
theorem entropy_perspective27 {iota : Type*} [Fintype iota]
    (q : iota → ℝ) (hq : ∀ i, 0 ≤ q i) :
    let mass := ∑ i, q i
    mass * entropy (fun i => q i / mass) =
      entropy q - Real.negMulLog mass / Real.log 2 := by
  classical
  dsimp only
  have hnats : (∑ i, q i) * Entropy.H Finset.univ (fun i => q i / ∑ j, q j) =
      Entropy.H Finset.univ q - Real.negMulLog (∑ i, q i) := by
    by_cases hm : (∑ i, q i) = 0
    · have hq0 : q = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hq).mp hm
      subst q
      simp [Entropy.H]
    · have hmpos : 0 < ∑ i, q i := lt_of_le_of_ne
          (Finset.sum_nonneg fun i _ => hq i) (Ne.symm hm)
      unfold Entropy.H
      rw [Finset.mul_sum]
      calc
        (∑ i, (∑ j, q j) * Real.negMulLog (q i / ∑ j, q j)) =
            ∑ i, (Real.negMulLog (q i) -
              (q i / ∑ j, q j) * Real.negMulLog (∑ j, q j)) := by
          apply Finset.sum_congr rfl
          intro i _
          have hcancel : (∑ j, q j) * (q i / ∑ j, q j) = q i := by
            field_simp
          have hmul := Real.negMulLog_mul (∑ j, q j) (q i / ∑ j, q j)
          rw [hcancel] at hmul
          linarith
        _ = (∑ i, Real.negMulLog (q i)) -
            (∑ i, q i / ∑ j, q j) * Real.negMulLog (∑ j, q j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ i, Real.negMulLog (q i)) - Real.negMulLog (∑ j, q j) := by
          rw [← Finset.sum_div, div_self hm, one_mul]
  unfold entropy Entropy.H₂
  calc
    (∑ i, q i) * (Entropy.H Finset.univ (fun i => q i / ∑ j, q j) / Real.log 2) =
        ((∑ i, q i) * Entropy.H Finset.univ (fun i => q i / ∑ j, q j)) /
          Real.log 2 := by ring
    _ = (Entropy.H Finset.univ q - Real.negMulLog (∑ i, q i)) / Real.log 2 := by
      rw [hnats]
    _ = Entropy.H Finset.univ q / Real.log 2 -
        Real.negMulLog (∑ i, q i) / Real.log 2 := by ring

set_option maxHeartbeats 1000000 in
-- The proof expands the finite joint law only for the two marginal identifications.
/-- Entropy of a mixture dominates the mass-weighted entropies obtained after grouping its
    components into arbitrary finite cells.  Zero-mass cells are handled by the perspective
    convention. -/
theorem entropy_grouped_mixture_le27 {iota cell outcome : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype cell] [DecidableEq cell]
    [Fintype outcome] [DecidableEq outcome]
    (p : iota → ℝ) (hp : IsProbability p)
    (law : iota → outcome → ℝ)
    (hlaw0 : ∀ i x, 0 ≤ law i x) (hlaw1 : ∀ i, ∑ x, law i x = 1)
    (group : iota → cell) :
    (∑ c : cell,
      let mass := ∑ i ∈ Finset.univ.filter (fun i => group i = c), p i
      mass * entropy (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i => group i = c), p i * law i x) / mass)) ≤
      entropy (fun x => ∑ i, p i * law i x) := by
  classical
  let mass : cell → ℝ := fun c =>
    ∑ i ∈ Finset.univ.filter (fun i => group i = c), p i
  let q : cell → outcome → ℝ := fun c x =>
    ∑ i ∈ Finset.univ.filter (fun i => group i = c), p i * law i x
  let avg : outcome → ℝ := fun x => ∑ i, p i * law i x
  let joint : cell × outcome → ℝ := fun z => q z.1 z.2
  have hmass0 : ∀ c, 0 ≤ mass c := fun c =>
    Finset.sum_nonneg (fun i _ => hp.1 i)
  have hq0 : ∀ c x, 0 ≤ q c x := fun c x =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (hlaw0 i x))
  have hqsum : ∀ c, ∑ x, q c x = mass c := by
    intro c
    dsimp only [q, mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, hlaw1 i, mul_one]
  have hmassSum : ∑ c, mass c = 1 := by
    dsimp only [mass]
    rw [Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset iota)) (t := (Finset.univ : Finset cell))
      (g := group) (fun i _ => Finset.mem_univ (group i)) p]
    exact hp.2
  have havg : ∀ x, ∑ c, q c x = avg x := by
    intro x
    dsimp only [q, avg]
    rw [Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset iota)) (t := (Finset.univ : Finset cell))
      (g := group) (fun i _ => Finset.mem_univ (group i))
      (fun i => p i * law i x)]
  have hjoint0 : ∀ z, 0 ≤ joint z := fun z => hq0 z.1 z.2
  have hjointSum : ∑ z, joint z = 1 := by
    dsimp only [joint]
    rw [Fintype.sum_prod_type]
    calc
      (∑ c, ∑ x, q c x) = ∑ c, mass c := by
        apply Finset.sum_congr rfl
        intro c _
        exact hqsum c
      _ = 1 := hmassSum
  have hfirst :
      (fun c => ∑ z ∈ Finset.univ.filter (fun z : cell × outcome => z.1 = c), joint z) =
        mass := by
    funext c
    rw [Finset.sum_filter]
    dsimp only [joint]
    rw [Fintype.sum_prod_type]
    simp only
    calc
      (∑ x, ∑ x_1, if x = c then q x x_1 else 0) = ∑ x, q c x := by
        rw [Finset.sum_eq_single c]
        · simp
        · intro d _ hdc
          simp [hdc]
        · simp
      _ = mass c := hqsum c
  have hsecond :
      (fun x => ∑ z ∈ Finset.univ.filter (fun z : cell × outcome => z.2 = x), joint z) =
        avg := by
    funext x
    rw [Finset.sum_filter]
    dsimp only [joint]
    rw [Fintype.sum_prod_type]
    simp only [Prod.snd, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact havg x
  have hsub := entropy_le_add_marginals_of_injective27 joint hjoint0 hjointSum
    (fun z : cell × outcome => z.1) (fun z : cell × outcome => z.2)
    (fun a b ha hb => Prod.ext ha hb)
  rw [hfirst, hsecond] at hsub
  have hperspective :
      (∑ c, mass c * entropy (fun x => q c x / mass c)) =
        entropy joint - entropy mass := by
    calc
      (∑ c, mass c * entropy (fun x => q c x / mass c)) =
          ∑ c, (entropy (q c) - Real.negMulLog (mass c) / Real.log 2) := by
        apply Finset.sum_congr rfl
        intro c _
        have h := entropy_perspective27 (q c) (hq0 c)
        rw [hqsum c] at h
        exact h
      _ = entropy joint - entropy mass := by
        unfold entropy Entropy.H₂ Entropy.H
        dsimp only [joint]
        rw [Fintype.sum_prod_type, Finset.sum_sub_distrib]
        have hA : (∑ x, (∑ i, Real.negMulLog (q x i)) / Real.log 2) =
            (∑ x, ∑ i, Real.negMulLog (q x i)) / Real.log 2 :=
          by rw [Finset.sum_div]
        have hB : (∑ x, Real.negMulLog (mass x) / Real.log 2) =
            (∑ x, Real.negMulLog (mass x)) / Real.log 2 :=
          by rw [Finset.sum_div]
        rw [hA, hB]
  change (∑ c, mass c * entropy (fun x => q c x / mass c)) ≤ entropy avg
  rw [hperspective]
  linarith

end
end OmegaBound.ADVXXZGeneral
end
