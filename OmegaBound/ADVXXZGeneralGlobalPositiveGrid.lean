import OmegaBound.ADVXXZGeneralGlobalNear
import OmegaBound.ADVXXZGeneralGrid
import OmegaBound.ADVXXZGeneralGridFinite
import OmegaBound.ADVXXZGeneralGridTensorV22

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3 Filter
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private noncomputable def positiveCoefficientCount {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X) (W : Side) (r : Fin 6) (u : Shape w)
    (σ : Chunk w) : ℕ :=
  let t := Fintype.equivFin (Fin 6 × Shape w) (r, u)
  match W with
  | .X => typeCnt (chunkSeq (x t)) σ
  | .Y => typeCnt (chunkSeq (y t)) σ
  | .Z => typeCnt (chunkSeq (z t)) σ

private theorem positiveCoefficientCount_total {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X) (W : Side) (r : Fin 6) (u : Shape w) :
    ∑ σ, positiveCoefficientCount x y z W r u σ =
      (n * g.joint.prob (r, u)).floor.toNat := by
  cases W <;> simp [positiveCoefficientCount, ADVXXZ.sum_typeCnt]

private theorem positiveOutput_iface_ne {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (t : Fin (Fintype.card (Fin 6 × Shape w))) :
    let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
    ifaceTermZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2)
      ((n : ℚ) * g.joint.prob (e t)).floor.toNat
      (g.beta .X (e t).1 (e t).2) (g.beta .Y (e t).1 (e t).2)
      (g.beta .Z (e t).1 (e t).2) ε (x t) (y t) (z t) ≠ 0 := by
  dsimp
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  have hprod :
      (∏ s : Fin (Fintype.card (Fin 6 × Shape w)),
        ifaceTermZ q w (coord .X (e s).2) (coord .Y (e s).2) (coord .Z (e s).2)
          ((n : ℚ) * g.joint.prob (e s)).floor.toNat
          (g.beta .X (e s).1 (e s).2) (g.beta .Y (e s).1 (e s).2)
          (g.beta .Z (e s).1 (e s).2) ε (x s) (y s) (z s)) ≠ 0 := by
    simpa [globalOutputZ, ifaceZ] using hcoeff
  intro ht
  exact hprod (Finset.prod_eq_zero (Finset.mem_univ t) ht)

private theorem positiveOutput_nonzero_approx {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (r : Fin 6) (u : Shape w) (hk : 0 < (n * g.joint.prob (r, u)).floor.toNat) :
    ApproxConsistent ε (g.beta .X r u)
        (chunkSeq (x (Fintype.equivFin (Fin 6 × Shape w) (r, u)))) ∧
      ApproxConsistent ε (g.beta .Y r u)
        (chunkSeq (y (Fintype.equivFin (Fin 6 × Shape w) (r, u)))) ∧
      ApproxConsistent ε (g.beta .Z r u)
        (chunkSeq (z (Fintype.equivFin (Fin 6 × Shape w) (r, u)))) := by
  have ht := positiveOutput_iface_ne x y z hcoeff
    (Fintype.equivFin (Fin 6 × Shape w) (r, u))
  simp only [Equiv.symm_apply_apply] at ht
  by_contra hguard
  simp [ifaceTermZ, Nat.ne_of_gt hk, hguard] at ht

private theorem positive_conZ_ne_levels {q w i j k : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (h : conZ q w i j k x y z ≠ 0) :
    levOf x = i ∧ levOf y = j ∧ levOf z = k := by
  unfold conZ zoP at h
  split at h
  · assumption
  · simp at h

private theorem positiveOutput_conZ_ne {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (t : Fin (Fintype.card (Fin 6 × Shape w)))
    (a : Fin (((n : ℚ) * g.joint.prob
      ((Fintype.equivFin (Fin 6 × Shape w)).symm t)).floor.toNat)) :
    conZ q w (coord .X ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Y ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (coord .Z ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2)
      (x t a) (y t a) (z t a) ≠ 0 := by
  have hk : ((n : ℚ) * g.joint.prob
      ((Fintype.equivFin (Fin 6 × Shape w)).symm t)).floor.toNat ≠ 0 := by
    have := a.isLt
    omega
  have ht := positiveOutput_iface_ne x y z hcoeff t
  simp only [ifaceTermZ, if_neg hk] at ht
  split at ht
  · intro ha
    exact ht (Finset.prod_eq_zero (Finset.mem_univ a) ha)
  · simp at ht

private theorem positiveCoefficientCount_graded {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (W : Side) (r : Fin 6) (u : Shape w) (σ : Chunk w)
    (hgrade : chunkLvl σ ≠ coord W u) :
    positiveCoefficientCount x y z W r u σ = 0 := by
  by_contra hzero
  have hpos : 0 < positiveCoefficientCount x y z W r u σ := Nat.pos_of_ne_zero hzero
  have hle : positiveCoefficientCount x y z W r u σ ≤
      ∑ τ, positiveCoefficientCount x y z W r u τ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  have hk : 0 < (n * g.joint.prob (r, u)).floor.toNat := by
    rw [positiveCoefficientCount_total x y z W r u] at hle
    omega
  cases W with
  | X =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (x (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a = σ).card := by
        simpa [positiveCoefficientCount, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hcon := positiveOutput_conZ_ne x y z hcoeff
        (Fintype.equivFin (Fin 6 × Shape w) (r, u)) a
      simp only [Equiv.symm_apply_apply] at hcon
      have hl := (positive_conZ_ne_levels _ _ _ hcon).1
      have hchunk : chunkLvl
          (chunkSeq (x (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a) = coord .X u :=
        hl
      exact hgrade (by simpa [haeq] using hchunk)
  | Y =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (y (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a = σ).card := by
        simpa [positiveCoefficientCount, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hcon := positiveOutput_conZ_ne x y z hcoeff
        (Fintype.equivFin (Fin 6 × Shape w) (r, u)) a
      simp only [Equiv.symm_apply_apply] at hcon
      have hl := (positive_conZ_ne_levels _ _ _ hcon).2.1
      have hchunk : chunkLvl
          (chunkSeq (y (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a) = coord .Y u :=
        hl
      exact hgrade (by simpa [haeq] using hchunk)
  | Z =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (z (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a = σ).card := by
        simpa [positiveCoefficientCount, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hcon := positiveOutput_conZ_ne x y z hcoeff
        (Fintype.equivFin (Fin 6 × Shape w) (r, u)) a
      simp only [Equiv.symm_apply_apply] at hcon
      have hl := (positive_conZ_ne_levels _ _ _ hcon).2.2
      have hchunk : chunkLvl
          (chunkSeq (z (Fintype.equivFin (Fin 6 × Shape w) (r, u))) a) = coord .Z u :=
        hl
      exact hgrade (by simpa [haeq] using hchunk)

private noncomputable def positiveCoefficientExactGrid {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0) : ExactGrid g n where
  count := positiveCoefficientCount x y z
  total := positiveCoefficientCount_total x y z
  graded := positiveCoefficientCount_graded x y z hcoeff

private theorem positiveCoefficientCount_close {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (W : Side) (r : Fin 6) (u : Shape w)
    (hk : 0 < (n * g.joint.prob (r, u)).floor.toNat) (σ : Chunk w) :
    |(positiveCoefficientCount x y z W r u σ : ℚ) /
        (n * g.joint.prob (r, u)).floor.toNat - (g.beta W r u).prob σ| ≤ ε := by
  have h := positiveOutput_nonzero_approx x y z hcoeff r u hk
  cases W
  · simpa [positiveCoefficientCount, emp] using h.1 σ
  · simpa [positiveCoefficientCount, emp] using h.2.1 σ
  · simpa [positiveCoefficientCount, emp] using h.2.2 σ

private noncomputable def positiveCoefficientFullGrid {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0) : FullGrid g n ε := by
  refine ⟨positiveCoefficientExactGrid x y z hcoeff, ?_⟩
  intro W r u
  dsimp
  intro hk σ
  exact positiveCoefficientCount_close x y z hcoeff W r u hk σ

private theorem positiveExactGrid_ext {w n : ℕ} {g : GlobalSpec w}
    {ξ η : ExactGrid g n} (h : ξ.count = η.count) : ξ = η := by
  cases ξ
  cases η
  cases h
  rfl

private theorem positiveCoefficientFullGrid_matches {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0) :
    GridLegMatches (q := q) .X (positiveCoefficientFullGrid x y z hcoeff) x ∧
      GridLegMatches (q := q) .Y (positiveCoefficientFullGrid x y z hcoeff) y ∧
      GridLegMatches (q := q) .Z (positiveCoefficientFullGrid x y z hcoeff) z := by
  simp only [GridLegMatches, positiveCoefficientFullGrid, positiveCoefficientExactGrid,
    positiveCoefficientCount]
  constructor
  · intro t σ
    rw [Prod.eta, Equiv.apply_symm_apply]
  constructor
  · intro t σ
    rw [Prod.eta, Equiv.apply_symm_apply]
  · intro t σ
    rw [Prod.eta, Equiv.apply_symm_apply]

private theorem fullGrid_eq_of_matches {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (x y z : (globalOutputZ q g n ε).X)
    (hcoeff : (globalOutputZ q g n ε).tensor x y z ≠ 0)
    (ξ : FullGrid g n ε)
    (hmX : GridLegMatches (q := q) .X ξ x)
    (hmY : GridLegMatches (q := q) .Y ξ y)
    (hmZ : GridLegMatches (q := q) .Z ξ z) :
    ξ = positiveCoefficientFullGrid x y z hcoeff := by
  apply Subtype.ext
  apply positiveExactGrid_ext
  funext W r u σ
  simp only [GridLegMatches] at hmX hmY hmZ
  cases W
  · simpa [positiveCoefficientFullGrid, positiveCoefficientExactGrid,
      positiveCoefficientCount] using
      hmX (Fintype.equivFin (Fin 6 × Shape w) (r, u)) σ
  · simpa [positiveCoefficientFullGrid, positiveCoefficientExactGrid,
      positiveCoefficientCount] using
      hmY (Fintype.equivFin (Fin 6 × Shape w) (r, u)) σ
  · simpa [positiveCoefficientFullGrid, positiveCoefficientExactGrid,
      positiveCoefficientCount] using
      hmZ (Fintype.equivFin (Fin 6 × Shape w) (r, u)) σ

private theorem fullGridTensor_apply_positive {q w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (ξ : FullGrid g n ε) (x y z : (globalOutputZ q g n ε).X) :
    (fullGridTensor q g n ξ).tensor x y z =
      if GridLegMatches (q := q) .X ξ x ∧ GridLegMatches (q := q) .Y ξ y ∧
        GridLegMatches (q := q) .Z ξ z
      then (globalOutputZ q g n ε).tensor x y z else 0 := rfl

private theorem fullGridTensor_sum_apply_positive {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ} (x y z : (globalOutputZ q g n ε).X) :
    ((∑ ξ : FullGrid g n ε, (fullGridTensor q g n ξ).tensor) :
        Tensor3 ℤ (globalOutputZ q g n ε).X
          (globalOutputZ q g n ε).Y (globalOutputZ q g n ε).Z) x y z =
      ∑ ξ : FullGrid g n ε, (fullGridTensor q g n ξ).tensor x y z := by
  let f : FullGrid g n ε → Tensor3 ℤ (globalOutputZ q g n ε).X
      (globalOutputZ q g n ε).Y (globalOutputZ q g n ε).Z :=
    fun ξ => (fullGridTensor q g n ξ).tensor
  change (∑ ξ, f ξ) x y z = ∑ ξ, f ξ x y z
  rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]

/-- The plain positive-tolerance output is the coefficient sum over all close exact physical
grids.  This is deliberately the plain grid family; no centre-support hypothesis is imposed. -/
theorem globalOutputZ_eq_sum_fullGridTensor (q : ℕ) {w n : ℕ}
    (g : GlobalSpec w) (ε : ℚ) :
    (globalOutputZ q g n ε).tensor =
      ∑ ξ : FullGrid g n ε, (fullGridTensor q g n ξ).tensor := by
  classical
  funext x y z
  rw [fullGridTensor_sum_apply_positive]
  by_cases hcoeff : (globalOutputZ q g n ε).tensor x y z = 0
  · simp [fullGridTensor_apply_positive, hcoeff]
  · let ξ₀ := positiveCoefficientFullGrid x y z hcoeff
    symm
    calc
      ∑ ξ : FullGrid g n ε, (fullGridTensor q g n ξ).tensor x y z =
          (fullGridTensor q g n ξ₀).tensor x y z := by
        apply Finset.sum_eq_single ξ₀
        · intro ξ _ hne
          rw [fullGridTensor_apply_positive, if_neg (fun hm => hne
            (fullGrid_eq_of_matches x y z hcoeff ξ hm.1 hm.2.1 hm.2.2))]
        · simp
      _ = (globalOutputZ q g n ε).tensor x y z := by
        rw [fullGridTensor_apply_positive, if_pos]
        exact positiveCoefficientFullGrid_matches x y z hcoeff

private theorem fullGrid_iface_eq_tensorPower {q w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ} (ξ : FullGrid g n ε)
    (x y z : (globalOutputZ q g n ε).X)
    (hmX : GridLegMatches (q := q) .X ξ x)
    (hmY : GridLegMatches (q := q) .Y ξ y)
    (hmZ : GridLegMatches (q := q) .Z ξ z)
    (t : Fin (Fintype.card (Fin 6 × Shape w))) :
    let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
    let k := ((n : ℚ) * g.joint.prob (e t)).floor.toNat
    ifaceTermZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2) k
      (g.beta .X (e t).1 (e t).2) (g.beta .Y (e t).1 (e t).2)
      (g.beta .Z (e t).1 (e t).2) ε (x t) (y t) (z t) =
      tensorPower (conZ q w (coord .X (e t).2) (coord .Y (e t).2)
        (coord .Z (e t).2)) k (x t) (y t) (z t) := by
  dsimp
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  let k := ((n : ℚ) * g.joint.prob (e t)).floor.toNat
  by_cases hk : k = 0
  · change ifaceTermZ q w _ _ _ k _ _ _ ε (x t) (y t) (z t) = _
    simp only [ifaceTermZ, hk, if_pos]
    symm
    rw [tensorPower]
    apply Finset.prod_eq_one
    intro i _
    exact Fin.elim0 (hk ▸ i)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hX : ApproxConsistent ε (g.beta .X (e t).1 (e t).2) (chunkSeq (x t)) := by
      intro σ
      rw [emp, ← hmX t σ]
      exact ξ.property .X (e t).1 (e t).2 hkpos σ
    have hY : ApproxConsistent ε (g.beta .Y (e t).1 (e t).2) (chunkSeq (y t)) := by
      intro σ
      rw [emp, ← hmY t σ]
      exact ξ.property .Y (e t).1 (e t).2 hkpos σ
    have hZ : ApproxConsistent ε (g.beta .Z (e t).1 (e t).2) (chunkSeq (z t)) := by
      intro σ
      rw [emp, ← hmZ t σ]
      exact ξ.property .Z (e t).1 (e t).2 hkpos σ
    have hguard : ApproxConsistent ε
          (g.beta .X ((Fintype.equivFin (Fin 6 × Shape w)).symm t).1
            ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2) (chunkSeq (x t)) ∧
        ApproxConsistent ε
          (g.beta .Y ((Fintype.equivFin (Fin 6 × Shape w)).symm t).1
            ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2) (chunkSeq (y t)) ∧
        ApproxConsistent ε
          (g.beta .Z ((Fintype.equivFin (Fin 6 × Shape w)).symm t).1
            ((Fintype.equivFin (Fin 6 × Shape w)).symm t).2) (chunkSeq (z t)) := by
      simpa only [e] using And.intro hX (And.intro hY hZ)
    change ifaceTermZ q w _ _ _ k _ _ _ ε (x t) (y t) (z t) = _
    simp only [ifaceTermZ, hk, if_false, hguard, true_and, if_true]
    simp only [k, e]

/-- The raw exact-grid tensor `exactGridTensor` agrees with the common-leg histogram zero-out used by the
finite grid enumeration. -/
theorem exactGridTensor_eq_fullGridTensor (q : ℕ) {w n : ℕ}
    (g : GlobalSpec w) {ε : ℚ} (ξ : FullGrid g n ε) :
    (exactGridTensor q g n ξ.val).tensor = (fullGridTensor q g n ξ).tensor := by
  classical
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  let k := fun t => ((n : ℚ) * g.joint.prob (e t)).floor.toNat
  let L := (t : Fin (Fintype.card (Fin 6 × Shape w))) →
    Fin (k t) → Fin w → CW90.Idx7 q
  let keep := fun (W : Side) (x : L) =>
    ∀ t σ, typeCnt (chunkSeq (x t)) σ = ξ.val.count W (e t).1 (e t).2 σ
  change zoP (keep .X) (keep .Y) (keep .Z)
      (fun x y z => ∏ t, tensorPower
        (conZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2))
        (k t) (x t) (y t) (z t)) =
    zoP (GridLegMatches (q := q) .X ξ) (GridLegMatches (q := q) .Y ξ)
      (GridLegMatches (q := q) .Z ξ) (globalOutputZ q g n ε).tensor
  funext x y z
  by_cases hk : keep .X x ∧ keep .Y y ∧ keep .Z z
  · have hmX : GridLegMatches (q := q) .X ξ x := by
      intro t σ
      exact (hk.1 t σ).symm
    have hmY : GridLegMatches (q := q) .Y ξ y := by
      intro t σ
      exact (hk.2.1 t σ).symm
    have hmZ : GridLegMatches (q := q) .Z ξ z := by
      intro t σ
      exact (hk.2.2 t σ).symm
    have hm : GridLegMatches (q := q) .X ξ x ∧
        GridLegMatches (q := q) .Y ξ y ∧ GridLegMatches (q := q) .Z ξ z :=
      ⟨hmX, hmY, hmZ⟩
    simp only [zoP, if_pos hk, if_pos hm]
    change (∏ t, tensorPower
        (conZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2))
        (k t) (x t) (y t) (z t)) =
      ∏ t, ifaceTermZ q w (coord .X (e t).2) (coord .Y (e t).2)
        (coord .Z (e t).2) (k t) (g.beta .X (e t).1 (e t).2)
        (g.beta .Y (e t).1 (e t).2) (g.beta .Z (e t).1 (e t).2) ε
        (x t) (y t) (z t)
    apply Finset.prod_congr rfl
    intro t _
    exact (fullGrid_iface_eq_tensorPower ξ x y z hmX hmY hmZ t).symm
  · have hm : ¬ (GridLegMatches (q := q) .X ξ x ∧
        GridLegMatches (q := q) .Y ξ y ∧ GridLegMatches (q := q) .Z ξ z) := by
      rintro ⟨hmX, hmY, hmZ⟩
      apply hk
      exact ⟨fun t σ => (hmX t σ).symm, fun t σ => (hmY t σ).symm,
        fun t σ => (hmZ t σ).symm⟩
    simp [zoP, hk, hm]

/-- The literal exact-grid decomposition of the positive-tolerance global output. -/
theorem globalOutputZ_eq_sum_exactGridTensor (q : ℕ) {w n : ℕ}
    (g : GlobalSpec w) (ε : ℚ) :
    (globalOutputZ q g n ε).tensor =
      ∑ ξ : FullGrid g n ε, (exactGridTensor q g n ξ.val).tensor := by
  rw [globalOutputZ_eq_sum_fullGridTensor]
  apply Finset.sum_congr rfl
  intro ξ _
  exact (exactGridTensor_eq_fullGridTensor q g ξ).symm

private theorem positiveRatDist_prob_le_one {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) : P.prob i ≤ 1 := by
  have hnum : P.num i ≤ P.den := by
    rw [← P.sum_num]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (P.num j)) (Finset.mem_univ i)
  have hden : (0 : ℚ) < (P.den : ℚ) := by exact_mod_cast P.den_pos
  simp only [RatDist.prob]
  rw [div_le_one hden]
  exact_mod_cast hnum

private theorem positiveJointFloor_le {w n : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (u : Shape w) :
    (n * g.joint.prob (r, u)).floor.toNat ≤ n := by
  let a : ℚ := (n : ℚ) * g.joint.prob (r, u)
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg n) (g.joint.prob_nonneg _)
  have ha : a ≤ (n : ℚ) := by
    dsimp [a]
    nlinarith [positiveRatDist_prob_le_one g.joint (r, u), g.joint.prob_nonneg (r, u)]
  have hf : ((⌊a⌋₊ : ℕ) : ℚ) ≤ a := Nat.floor_le ha0
  change ⌊a⌋₊ ≤ n
  exact_mod_cast hf.trans ha

private abbrev PositiveGridCode {w : ℕ} (n : ℕ) :=
  Side × (Fin 6 × (Shape w × Chunk w)) → Fin (n + 1)

private noncomputable def positiveFullGridCode {w n : ℕ} {g : GlobalSpec w} {ε : ℚ}
    (ξ : FullGrid g n ε) : PositiveGridCode (w := w) n := fun a =>
  ⟨ξ.val.count a.1 a.2.1 a.2.2.1 a.2.2.2, Nat.lt_succ_of_le <|
    calc
      ξ.val.count a.1 a.2.1 a.2.2.1 a.2.2.2 ≤
          ∑ σ, ξ.val.count a.1 a.2.1 a.2.2.1 σ :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a.2.2.2)
      _ = (n * g.joint.prob (a.2.1, a.2.2.1)).floor.toNat :=
        ξ.val.total a.1 a.2.1 a.2.2.1
      _ ≤ n := positiveJointFloor_le g a.2.1 a.2.2.1⟩

private theorem positiveFullGridCode_injective {w n : ℕ}
    {g : GlobalSpec w} {ε : ℚ} : Function.Injective
      (positiveFullGridCode (n := n) (g := g) (ε := ε)) := by
  intro ξ η h
  apply Subtype.ext
  apply positiveExactGrid_ext
  funext W r u σ
  exact congrArg Fin.val (congrFun h (W, (r, (u, σ))))

/-- Every physical side/region/shape/chunk histogram coordinate has at most `n+1` values. -/
theorem fullGrid_card_le {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ε : ℚ) :
    Fintype.card (FullGrid g n ε) ≤ (n + 1) ^ gridDimension g := by
  calc
    Fintype.card (FullGrid g n ε) ≤ Fintype.card (PositiveGridCode (w := w) n) :=
      Fintype.card_le_of_injective positiveFullGridCode positiveFullGridCode_injective
    _ = (n + 1) ^ gridDimension g := by
      simp [PositiveGridCode, gridDimension]
      congr 1
      have hside : Fintype.card Side = 3 := by decide +kernel
      rw [hside]
      ring

private noncomputable def positiveCentreJointCount {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (r : Fin 6) (u : Shape w) : ℕ :=
  Classical.choose (((hb.2 r).2 u).1)

private theorem positiveCentreJointCount_spec {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (r : Fin 6) (u : Shape w) :
    (b : ℚ) * g.joint.prob (r, u) = (positiveCentreJointCount g hb r u : ℚ) :=
  Classical.choose_spec (((hb.2 r).2 u).1)

private noncomputable def positiveCentreSplitCount {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w)
    (σ : Chunk w) : ℕ :=
  Classical.choose (((hb.2 r).2 u).2 W σ)

private theorem positiveCentreSplitCount_spec {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w)
    (σ : Chunk w) :
    (b : ℚ) * g.joint.prob (r, u) * (g.beta W r u).prob σ =
      (positiveCentreSplitCount g hb W r u σ : ℚ) :=
  Classical.choose_spec (((hb.2 r).2 u).2 W σ)

private theorem positiveCentreSplitCount_sum {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w) :
    ∑ σ, positiveCentreSplitCount g hb W r u σ =
      positiveCentreJointCount g hb r u := by
  apply Nat.cast_injective (R := ℚ)
  push_cast
  calc
    ∑ σ, (positiveCentreSplitCount g hb W r u σ : ℚ) =
        ∑ σ, (b : ℚ) * g.joint.prob (r, u) * (g.beta W r u).prob σ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (positiveCentreSplitCount_spec g hb W r u σ).symm
    _ = (b : ℚ) * g.joint.prob (r, u) * ∑ σ, (g.beta W r u).prob σ := by
      rw [Finset.mul_sum]
    _ = (b : ℚ) * g.joint.prob (r, u) := by rw [RatDist.sum_prob, mul_one]
    _ = (positiveCentreJointCount g hb r u : ℚ) :=
      positiveCentreJointCount_spec g hb r u

private theorem positiveScaledCentreCount (b m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * a = (k : ℚ)) :
    (((b * m : ℕ) : ℚ) * a).floor.toNat = k * m := by
  have hq : (((b * m : ℕ) : ℚ) * a) = ((k * m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k * m : ℕ) : ℚ).floor) = (k * m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k * m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k * m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

private noncomputable def positiveCentreExactGrid {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ) : ExactGrid g (b * m) where
  count W r u σ := positiveCentreSplitCount g hb W r u σ * m
  total W r u := by
    rw [← Finset.sum_mul, positiveCentreSplitCount_sum]
    exact (positiveScaledCentreCount b m (positiveCentreJointCount g hb r u)
      (g.joint.prob (r, u)) (positiveCentreJointCount_spec g hb r u)).symm
  graded W r u σ hgrade := by
    have hnum : (g.beta W r u).num σ = 0 := by
      by_contra hne
      exact hgrade (hg.support W r u σ hne)
    have hprob : (g.beta W r u).prob σ = 0 := by simp [RatDist.prob, hnum]
    have hspec := positiveCentreSplitCount_spec g hb W r u σ
    rw [hprob, mul_zero] at hspec
    have hcount : positiveCentreSplitCount g hb W r u σ = 0 := by
      exact_mod_cast hspec.symm
    simp [hcount]

private theorem positiveCentre_normalized_prob {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) (σ : Chunk w)
    (hk : 0 < (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) :
    ((positiveCentreExactGrid g hg hb m).count W r u σ : ℚ) /
        (((b * m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat =
      (g.beta W r u).prob σ := by
  have hscale := positiveScaledCentreCount b m (positiveCentreJointCount g hb r u)
    (g.joint.prob (r, u)) (positiveCentreJointCount_spec g hb r u)
  have hpos : 0 < positiveCentreJointCount g hb r u * m := by
    rw [← hscale]
    exact hk
  rw [hscale]
  change ((positiveCentreSplitCount g hb W r u σ * m : ℕ) : ℚ) /
      ((positiveCentreJointCount g hb r u * m : ℕ) : ℚ) = _
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hpos.ne')).2
  push_cast
  rw [← positiveCentreSplitCount_spec g hb W r u σ,
    ← positiveCentreJointCount_spec g hb r u]
  ring

/-- The integral centre supplies a full grid at every nonnegative tolerance, including the
all-zero-cell branches. -/
noncomputable def globalCentreFullGrid {w : ℕ} (g : GlobalSpec w) (hg : GlobalAdmissible g)
    {b : ℕ} (hb : GlobalIntegral g b) (m : ℕ) (ε : ℚ) (hε : 0 ≤ ε) :
    FullGrid g (b * m) ε := by
  refine ⟨positiveCentreExactGrid g hg hb m, ?_⟩
  intro W r u
  dsimp
  intro hk σ
  rw [positiveCentre_normalized_prob g hg hb m W r u σ hk, sub_self, abs_zero]
  exact hε

/-- Consequently the full-grid pool is nonempty at every nonnegative tolerance. -/
theorem fullGridPool27_pos {w : ℕ} (g : GlobalSpec w) (hg : GlobalAdmissible g)
    {b : ℕ} (hb : GlobalIntegral g b) (m : ℕ) (ε : ℚ) (hε : 0 ≤ ε) :
    0 < fullGridPool27 g (b * m) ε := by
  rw [fullGridPool27, Fintype.card_pos_iff]
  exact ⟨globalCentreFullGrid g hg hb m ε hε⟩

/-- The logarithm of the full physical-grid pool is sublinear in the supplied integral scale. -/
theorem fullGridPool27_log_sublinear {w : ℕ} (g : GlobalSpec w) (hg : GlobalAdmissible g)
    {b : ℕ} (hb : GlobalIntegral g b) (ε : ℚ) (hε : 0 ≤ ε) :
    Sublinear (fun m => b * m)
      (fun m => Real.log (fullGridPool27 g (b * m) ε : ℝ)) := by
  intro δ hδ
  let d := gridDimension g
  let c : ℝ := δ / (2 * ((d : ℝ) + 1))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htend : Tendsto (fun m : ℕ => ((b * m + 1 : ℕ) : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro A
    obtain ⟨M, hM⟩ := exists_nat_ge A
    refine eventually_atTop.2 ⟨M, fun m hm => ?_⟩
    have hnat : M ≤ b * m + 1 := by
      have hmb : m ≤ b * m := Nat.le_mul_of_pos_left m hb.1
      omega
    exact hM.trans (by exact_mod_cast hnat)
  have hlo := Real.isLittleO_log_id_atTop.comp_tendsto htend
  have hev := hlo.bound hc
  rw [eventually_atTop] at hev
  obtain ⟨M₀, hM₀⟩ := hev
  refine ⟨max M₀ 1, fun m hm => ?_⟩
  have hm₀ : M₀ ≤ m := (Nat.le_max_left M₀ 1).trans hm
  have hm1 : 1 ≤ m := (Nat.le_max_right M₀ 1).trans hm
  have hbm : 0 < b * m := Nat.mul_pos hb.1 (Nat.pos_of_ne_zero (by omega))
  have hxpos : (0 : ℝ) < ((b * m + 1 : ℕ) : ℝ) := by positivity
  have hxone : (1 : ℝ) ≤ ((b * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (b * m))
  have hlogx : Real.log ((b * m + 1 : ℕ) : ℝ) ≤
      c * ((b * m + 1 : ℕ) : ℝ) := by
    have hs := hM₀ m hm₀
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at hs
    rw [abs_of_nonneg (Real.log_nonneg hxone), abs_of_nonneg hxpos.le] at hs
    exact hs
  have hQpos : 0 < fullGridPool27 g (b * m) ε :=
    fullGridPool27_pos g hg hb m ε hε
  have hQone : (1 : ℝ) ≤ (fullGridPool27 g (b * m) ε : ℝ) := by
    exact_mod_cast hQpos
  have hcard : fullGridPool27 g (b * m) ε ≤
      (b * m + 1) ^ gridDimension g := by
    simpa only [fullGridPool27] using fullGrid_card_le g (b * m) ε
  have hQposR : (0 : ℝ) < (fullGridPool27 g (b * m) ε : ℝ) := by
    exact_mod_cast hQpos
  have hcardR : (fullGridPool27 g (b * m) ε : ℝ) ≤
      (((b * m + 1) ^ gridDimension g : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hlogcard := Real.log_le_log hQposR hcardR
  have hcastpow : (((b * m + 1) ^ gridDimension g : ℕ) : ℝ) =
      (((b * m + 1 : ℕ) : ℝ) ^ gridDimension g) := by norm_num
  rw [hcastpow, Real.log_pow] at hlogcard
  have hden : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  have hcoef : 2 * (d : ℝ) * c ≤ δ := by
    calc
      2 * (d : ℝ) * c =
          (2 * (d : ℝ) * δ) / (2 * ((d : ℝ) + 1)) := by
            dsimp [c]
            ring
      _ ≤ δ := (div_le_iff₀ hden).2 (by
        have hd0 : (0 : ℝ) ≤ d := by positivity
        nlinarith)
  have hxle : (((b * m + 1 : ℕ) : ℝ)) ≤ 2 * ((b * m : ℕ) : ℝ) := by
    exact_mod_cast (show b * m + 1 ≤ 2 * (b * m) by omega)
  rw [abs_of_nonneg (Real.log_nonneg hQone)]
  calc
    Real.log (fullGridPool27 g (b * m) ε : ℝ) ≤
        (gridDimension g : ℝ) * Real.log ((b * m + 1 : ℕ) : ℝ) := hlogcard
    _ ≤ (d : ℝ) * (c * ((b * m + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlogx (by positivity)
    _ ≤ (d : ℝ) * (c * (2 * ((b * m : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxle hc.le) (by positivity)
    _ = (2 * (d : ℝ) * c) * ((b * m : ℕ) : ℝ) := by ring
    _ ≤ δ * ((b * m : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

end
end OmegaBound.ADVXXZGeneral
end
