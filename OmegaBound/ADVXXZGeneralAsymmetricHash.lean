import OmegaBound.ADVXXZGeneralPopulationFiniteAPI

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def getZero {P : RawPopulation} {M : ℕ}
    (omega : HashOutcome P M) : ZMod M :=
  omega ⟨0, by omega⟩

private def getOne {P : RawPopulation} {M : ℕ}
    (omega : HashOutcome P M) : ZMod M :=
  omega ⟨1, by omega⟩

private def getWeight {P : RawPopulation} {M : ℕ}
    (omega : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  omega ⟨i.val + 2, by omega⟩

private def localHashX (P : RawPopulation) (M : ℕ) (omega : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  getZero omega + ∑ i, (P.coarse j .X i).val * getWeight omega i

private def localHashY (P : RawPopulation) (M : ℕ) (omega : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  getZero omega + getOne omega +
    ∑ i, (P.coarse j .Y i).val * getWeight omega i

private noncomputable def localHashZ (P : RawPopulation) (M : ℕ)
    (omega : HashOutcome P M) (j : P.Label) : ZMod M :=
  getZero omega + Ring.inverse 2 *
    (getOne omega +
      ∑ i, (P.grade - (P.coarse j .Z i).val) * getWeight omega i)

private theorem mem_bucket_iff (P : RawPopulation) (M : ℕ) [NeZero M]
    (j : P.Label) (b : ZMod M) (omega : HashOutcome P M) :
    omega ∈ bucket P M j b ↔
      localHashX P M omega j = b ∧ localHashY P M omega j = b ∧
        localHashZ P M omega j = b := by
  simp only [bucket, Finset.mem_filter, Finset.mem_univ, true_and]
  with_unfolding_all rfl

private theorem side_univ :
    (Finset.univ : Finset Side) = {.X, .Y, .Z} := by
  decide +kernel

private theorem tight_xyz (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (j : P.Label) (i : Fin P.n) :
    (P.coarse j .X i).val + (P.coarse j .Y i).val +
        (P.coarse j .Z i).val = P.grade := by
  have h := htight j i
  rw [side_univ] at h
  simpa [add_assoc] using h

private def sideSum (P : RawPopulation) (M : ℕ) (j : P.Label) (W : Side)
    (v : Fin P.n → ZMod M) : ZMod M :=
  ∑ i, (P.coarse j W i).val * v i

private def complementSum (P : RawPopulation) (M : ℕ) (j : P.Label)
    (v : Fin P.n → ZMod M) : ZMod M :=
  ∑ i, (P.grade - (P.coarse j .Z i).val) * v i

private theorem complementSum_eq (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) (j : P.Label) (v : Fin P.n → ZMod M) :
    complementSum P M j v = sideSum P M j .X v + sideSum P M j .Y v := by
  unfold complementSum sideSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hnat : P.grade - (P.coarse j .Z i).val =
      (P.coarse j .X i).val + (P.coarse j .Y i).val := by
    have := tight_xyz P htight j i
    omega
  have hzle : (P.coarse j .Z i).val ≤ P.grade := by
    have := tight_xyz P htight j i
    omega
  rw [← Nat.cast_sub hzle, hnat, Nat.cast_add]
  ring

private theorem inverse_two_mul (M : ℕ) (hprime : Nat.Prime M) (hodd : 2 < M) :
    Ring.inverse (2 : ZMod M) * 2 = 1 := by
  apply Ring.inverse_mul_cancel
  have hnot : ¬ M ∣ 2 := by
    exact Nat.not_dvd_of_pos_of_lt (by omega) hodd
  have hcop : Nat.Coprime 2 M := by
    rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd]
    exact hnot
  exact (ZMod.unitOfCoprime 2 hcop).isUnit

private def outcomeOf {P : RawPopulation} {M : ℕ} (a0 a1 : ZMod M)
    (v : Fin P.n → ZMod M) : HashOutcome P M :=
  Fin.cases a0 (Fin.cases a1 v)

private def bucketOutcome (P : RawPopulation) (M : ℕ) (j : P.Label) (b : ZMod M)
    (v : Fin P.n → ZMod M) : HashOutcome P M :=
  outcomeOf (b - sideSum P M j .X v)
    (sideSum P M j .X v - sideSum P M j .Y v) v

private theorem getZero_bucketOutcome (P : RawPopulation) (M : ℕ) (j : P.Label)
    (b : ZMod M) (v : Fin P.n → ZMod M) :
    getZero (bucketOutcome P M j b v) = b - sideSum P M j .X v := by
  rfl

private theorem getOne_bucketOutcome (P : RawPopulation) (M : ℕ) (j : P.Label)
    (b : ZMod M) (v : Fin P.n → ZMod M) :
    getOne (bucketOutcome P M j b v) =
      sideSum P M j .X v - sideSum P M j .Y v := by
  rfl

private theorem getWeight_bucketOutcome (P : RawPopulation) (M : ℕ) (j : P.Label)
    (b : ZMod M) (v : Fin P.n → ZMod M) (i : Fin P.n) :
    getWeight (bucketOutcome P M j b v) i = v i := by
  rfl

private theorem rawHashX_formula (P : RawPopulation) (M : ℕ)
    (omega : HashOutcome P M) (j : P.Label) :
    localHashX P M omega j = getZero omega + sideSum P M j .X (getWeight omega) := by
  rfl

private theorem rawHashY_formula (P : RawPopulation) (M : ℕ)
    (omega : HashOutcome P M) (j : P.Label) :
    localHashY P M omega j = getZero omega + getOne omega +
      sideSum P M j .Y (getWeight omega) := by
  rfl

private theorem rawHashZ_formula (P : RawPopulation) (M : ℕ)
    (omega : HashOutcome P M) (j : P.Label) :
    localHashZ P M omega j = getZero omega + Ring.inverse 2 *
      (getOne omega + complementSum P M j (getWeight omega)) := by
  rfl

private theorem bucketOutcome_mem (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j : P.Label) (b : ZMod M) (v : Fin P.n → ZMod M) :
    bucketOutcome P M j b v ∈ bucket P M j b := by
  rw [mem_bucket_iff]
  rw [rawHashX_formula, rawHashY_formula, rawHashZ_formula]
  have hweights : getWeight (bucketOutcome P M j b v) = v := by
    funext i
    exact getWeight_bucketOutcome P M j b v i
  rw [hweights, getZero_bucketOutcome, getOne_bucketOutcome]
  have hcomp := complementSum_eq P htight M j v
  have hinv := inverse_two_mul M hprime hodd
  constructor
  · ring
  constructor
  · ring
  · rw [hcomp]
    calc
      b - sideSum P M j .X v + Ring.inverse 2 *
          (sideSum P M j .X v - sideSum P M j .Y v +
            (sideSum P M j .X v + sideSum P M j .Y v)) =
          b - sideSum P M j .X v + Ring.inverse 2 *
            (2 * sideSum P M j .X v) := by ring
      _ = b := by rw [← mul_assoc, hinv, one_mul]; ring

private theorem outcome_ext {P : RawPopulation} {M : ℕ}
    {omega tau : HashOutcome P M}
    (hzero : getZero omega = getZero tau)
    (hone : getOne omega = getOne tau)
    (hweight : getWeight omega = getWeight tau) : omega = tau := by
  funext q
  refine Fin.cases ?_ (fun q' => Fin.cases ?_ (fun i => ?_) q') q
  · simpa [getZero] using hzero
  · simpa [getOne] using hone
  · simpa [getWeight] using congrFun hweight i

private noncomputable def bucketEquiv (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j : P.Label) (b : ZMod M) :
    (bucket P M j b : Type) ≃ (Fin P.n → ZMod M) where
  toFun omega := getWeight omega.1
  invFun v := ⟨bucketOutcome P M j b v,
    bucketOutcome_mem P htight M hprime hodd j b v⟩
  left_inv omega := by
    refine Subtype.ext ?_
    have hmem := (mem_bucket_iff P M j b omega.1).mp omega.2
    rw [rawHashX_formula, rawHashY_formula] at hmem
    rcases hmem with ⟨hx, hy, _⟩
    apply outcome_ext
    · rw [getZero_bucketOutcome]
      linear_combination -hx
    · rw [getOne_bucketOutcome]
      linear_combination hx - hy
    · funext i
      exact getWeight_bucketOutcome P M j b (getWeight omega.1) i
  right_inv v := by
    funext i
    exact getWeight_bucketOutcome P M j b v i

private theorem card_bucket (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j : P.Label) (b : ZMod M) :
    (bucket P M j b).card = M ^ P.n := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (bucketEquiv P htight M hprime hodd j b)]
  simp [ZMod.card]

private theorem mem_bucket_xy_iff (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j : P.Label) (b : ZMod M) (omega : HashOutcome P M) :
    omega ∈ bucket P M j b ↔
      getZero omega + sideSum P M j .X (getWeight omega) = b ∧
      getZero omega + getOne omega + sideSum P M j .Y (getWeight omega) = b := by
  rw [mem_bucket_iff, rawHashX_formula, rawHashY_formula, rawHashZ_formula]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hx, hy⟩
    refine ⟨hx, hy, ?_⟩
    rw [complementSum_eq P htight M j (getWeight omega)]
    have hinv := inverse_two_mul M hprime hodd
    have hinner : getOne omega +
        (sideSum P M j .X (getWeight omega) +
          sideSum P M j .Y (getWeight omega)) =
        2 * sideSum P M j .X (getWeight omega) := by
      linear_combination hy - hx
    calc
      getZero omega + Ring.inverse 2 *
          (getOne omega +
            (sideSum P M j .X (getWeight omega) +
              sideSum P M j .Y (getWeight omega))) =
          getZero omega + Ring.inverse 2 *
            (2 * sideSum P M j .X (getWeight omega)) := by rw [hinner]
      _ = getZero omega + sideSum P M j .X (getWeight omega) := by
        rw [← mul_assoc, hinv, one_mul]
      _ = b := hx

private def pivotSide : Side → Side
  | .X => .Y
  | .Y => .X
  | .Z => .X

private theorem sideSum_eq_of_coarse_eq (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (h : P.coarse j W = P.coarse k W)
    (v : Fin P.n → ZMod M) :
    sideSum P M j W v = sideSum P M k W v := by
  unfold sideSum
  rw [h]

private theorem pivotSide_ne (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse) (j k : P.Label) (hne : j ≠ k)
    (W : Side) (hsame : P.coarse j W = P.coarse k W) :
    P.coarse j (pivotSide W) ≠ P.coarse k (pivotSide W) := by
  cases W with
  | X =>
      intro hY
      change P.coarse j .X = P.coarse k .X at hsame
      change P.coarse j .Y = P.coarse k .Y at hY
      have hZ : P.coarse j .Z = P.coarse k .Z := by
        funext i
        apply Fin.ext
        have hj := tight_xyz P htight j i
        have hk := tight_xyz P htight k i
        have hx : (P.coarse j .X i).val = (P.coarse k .X i).val :=
          congrArg (fun f => (f i).val) hsame
        have hy : (P.coarse j .Y i).val = (P.coarse k .Y i).val :=
          congrArg (fun f => (f i).val) hY
        omega
      apply hne
      apply hinj
      funext V
      cases V with
      | X => exact hsame
      | Y => exact hY
      | Z => exact hZ
  | Y =>
      intro hX
      change P.coarse j .Y = P.coarse k .Y at hsame
      change P.coarse j .X = P.coarse k .X at hX
      have hZ : P.coarse j .Z = P.coarse k .Z := by
        funext i
        apply Fin.ext
        have hj := tight_xyz P htight j i
        have hk := tight_xyz P htight k i
        have hx : (P.coarse j .X i).val = (P.coarse k .X i).val :=
          congrArg (fun f => (f i).val) hX
        have hy : (P.coarse j .Y i).val = (P.coarse k .Y i).val :=
          congrArg (fun f => (f i).val) hsame
        omega
      apply hne
      apply hinj
      funext V
      cases V with
      | X => exact hX
      | Y => exact hsame
      | Z => exact hZ
  | Z =>
      intro hX
      change P.coarse j .Z = P.coarse k .Z at hsame
      change P.coarse j .X = P.coarse k .X at hX
      have hY : P.coarse j .Y = P.coarse k .Y := by
        funext i
        apply Fin.ext
        have hj := tight_xyz P htight j i
        have hk := tight_xyz P htight k i
        have hx : (P.coarse j .X i).val = (P.coarse k .X i).val :=
          congrArg (fun f => (f i).val) hX
        have hz : (P.coarse j .Z i).val = (P.coarse k .Z i).val :=
          congrArg (fun f => (f i).val) hsame
        omega
      apply hne
      apply hinj
      funext V
      cases V with
      | X => exact hX
      | Y => exact hY
      | Z => exact hsame

private theorem collision_constraint (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j k : P.Label) (W : Side) (b : ZMod M) (omega : HashOutcome P M)
    (hboth : omega ∈ bucket P M j b ∩ bucket P M k b) :
    sideSum P M j (pivotSide W) (getWeight omega) =
      sideSum P M k (pivotSide W) (getWeight omega) := by
  rcases Finset.mem_inter.mp hboth with ⟨hj, hk⟩
  have hj' := (mem_bucket_xy_iff P htight M hprime hodd j b omega).mp hj
  have hk' := (mem_bucket_xy_iff P htight M hprime hodd k b omega).mp hk
  cases W with
  | X =>
      change sideSum P M j .Y (getWeight omega) =
        sideSum P M k .Y (getWeight omega)
      linear_combination hj'.2 - hk'.2
  | Y =>
      change sideSum P M j .X (getWeight omega) =
        sideSum P M k .X (getWeight omega)
      linear_combination hj'.1 - hk'.1
  | Z =>
      change sideSum P M j .X (getWeight omega) =
        sideSum P M k .X (getWeight omega)
      linear_combination hj'.1 - hk'.1

private theorem bucketOutcome_mem_other (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j k : P.Label) (W : Side) (hsame : P.coarse j W = P.coarse k W)
    (b : ZMod M) (v : Fin P.n → ZMod M)
    (hconstraint : sideSum P M j (pivotSide W) v =
      sideSum P M k (pivotSide W) v) :
    bucketOutcome P M j b v ∈ bucket P M k b := by
  apply (mem_bucket_xy_iff P htight M hprime hodd k b _).mpr
  have hj := (mem_bucket_xy_iff P htight M hprime hodd j b _).mp
    (bucketOutcome_mem P htight M hprime hodd j b v)
  have hweights : getWeight (bucketOutcome P M j b v) = v := by
    funext i
    exact getWeight_bucketOutcome P M j b v i
  rw [hweights] at hj ⊢
  cases W with
  | X =>
      change P.coarse j .X = P.coarse k .X at hsame
      change sideSum P M j .Y v = sideSum P M k .Y v at hconstraint
      have hX := sideSum_eq_of_coarse_eq P M j k .X hsame v
      constructor
      · rw [← hX]
        exact hj.1
      · rw [← hconstraint]
        exact hj.2
  | Y =>
      change P.coarse j .Y = P.coarse k .Y at hsame
      change sideSum P M j .X v = sideSum P M k .X v at hconstraint
      have hY := sideSum_eq_of_coarse_eq P M j k .Y hsame v
      constructor
      · rw [← hconstraint]
        exact hj.1
      · rw [← hY]
        exact hj.2
  | Z =>
      change P.coarse j .Z = P.coarse k .Z at hsame
      change sideSum P M j .X v = sideSum P M k .X v at hconstraint
      have hxy : sideSum P M j .X v + sideSum P M j .Y v =
          sideSum P M k .X v + sideSum P M k .Y v := by
        calc
          sideSum P M j .X v + sideSum P M j .Y v =
              complementSum P M j v := (complementSum_eq P htight M j v).symm
          _ = complementSum P M k v := by
            unfold complementSum
            rw [hsame]
          _ = sideSum P M k .X v + sideSum P M k .Y v :=
            complementSum_eq P htight M k v
      have hY : sideSum P M j .Y v = sideSum P M k .Y v := by
        linear_combination hxy - hconstraint
      constructor
      · rw [← hconstraint]
        exact hj.1
      · rw [← hY]
        exact hj.2

private abbrev CollisionWeights (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) :=
  {v : Fin P.n → ZMod M //
    sideSum P M j (pivotSide W) v = sideSum P M k (pivotSide W) v}

private noncomputable def collisionEquiv (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (j k : P.Label) (W : Side) (hsame : P.coarse j W = P.coarse k W)
    (b : ZMod M) :
    {omega : HashOutcome P M // omega ∈ bucket P M j b ∩ bucket P M k b} ≃
      CollisionWeights P M j k W where
  toFun omega := ⟨getWeight omega.1,
    collision_constraint P htight M hprime hodd j k W b omega.1 omega.2⟩
  invFun v := ⟨bucketOutcome P M j b v.1, Finset.mem_inter.mpr
    ⟨bucketOutcome_mem P htight M hprime hodd j b v.1,
      bucketOutcome_mem_other P htight M hprime hodd j k W hsame b v.1 v.2⟩⟩
  left_inv omega := by
    apply Subtype.ext
    have hleft := (bucketEquiv P htight M hprime hodd j b).left_inv
      ⟨omega.1, (Finset.mem_inter.mp omega.2).1⟩
    have hout := congrArg
      (fun x : {omega : HashOutcome P M // omega ∈ bucket P M j b} => x.1) hleft
    exact hout
  right_inv v := by
    refine Subtype.ext ?_
    funext i
    exact getWeight_bucketOutcome P M j b v.1 i

private theorem exists_pivot (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse) (j k : P.Label) (hne : j ≠ k)
    (W : Side) (hsame : P.coarse j W = P.coarse k W) :
    ∃ i : Fin P.n,
      P.coarse j (pivotSide W) i ≠ P.coarse k (pivotSide W) i := by
  have hfun := pivotSide_ne P htight hinj j k hne W hsame
  by_contra h
  push_neg at h
  exact hfun (funext h)

private def collisionCoefficient (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (i : Fin P.n) : ZMod M :=
  (P.coarse j (pivotSide W) i).val - (P.coarse k (pivotSide W) i).val

private theorem collisionCoefficient_ne_zero (P : RawPopulation) (M : ℕ)
    (hfloor : P.grade < M) (j k : P.Label) (W : Side) (i : Fin P.n)
    (hi : P.coarse j (pivotSide W) i ≠ P.coarse k (pivotSide W) i) :
    collisionCoefficient P M j k W i ≠ 0 := by
  intro hzero
  have hcast : ((P.coarse j (pivotSide W) i).val : ZMod M) =
      (P.coarse k (pivotSide W) i).val := sub_eq_zero.mp hzero
  have hjlt : (P.coarse j (pivotSide W) i).val < M := by
    have := (P.coarse j (pivotSide W) i).isLt
    omega
  have hklt : (P.coarse k (pivotSide W) i).val < M := by
    have := (P.coarse k (pivotSide W) i).isLt
    omega
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hjlt, ZMod.val_natCast_of_lt hklt] at hval
  exact hi (Fin.ext hval)

private theorem prime_isUnit_of_ne_zero (M : ℕ) [NeZero M]
    (hprime : Nat.Prime M) (c : ZMod M) (hc : c ≠ 0) : IsUnit c := by
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime, Nat.coprime_comm,
    hprime.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (ZMod.val_pos.mpr hc) c.val_lt

private def collisionForm (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (v : Fin P.n → ZMod M) : ZMod M :=
  ∑ i, collisionCoefficient P M j k W i * v i

private theorem collisionForm_eq (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (v : Fin P.n → ZMod M) :
    collisionForm P M j k W v =
      sideSum P M j (pivotSide W) v - sideSum P M k (pivotSide W) v := by
  unfold collisionForm collisionCoefficient sideSum
  calc
    ∑ i, (↑(P.coarse j (pivotSide W) i).val -
        ↑(P.coarse k (pivotSide W) i).val) * v i =
        ∑ i, (↑(P.coarse j (pivotSide W) i).val * v i -
          ↑(P.coarse k (pivotSide W) i).val * v i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i, ↑(P.coarse j (pivotSide W) i).val * v i) -
        ∑ i, ↑(P.coarse k (pivotSide W) i).val * v i :=
          by rw [Finset.sum_sub_distrib]

private theorem collisionForm_update (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (i0 : Fin P.n) (v : Fin P.n → ZMod M)
    (x : ZMod M) :
    collisionForm P M j k W (Function.update v i0 x) =
      collisionForm P M j k W v +
        collisionCoefficient P M j k W i0 * (x - v i0) := by
  classical
  unfold collisionForm
  have hfun :
      (fun i => collisionCoefficient P M j k W i * Function.update v i0 x i) =
        Function.update (fun i => collisionCoefficient P M j k W i * v i) i0
          (collisionCoefficient P M j k W i0 * x) := by
    funext i
    by_cases hi : i = i0
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  rw [hfun]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i0)]
  rw [← Finset.sum_erase_add (a := i0) Finset.univ
    (fun i => collisionCoefficient P M j k W i * v i) (Finset.mem_univ i0)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

private def perturb {P : RawPopulation} {M : ℕ}
    (v : Fin P.n → ZMod M) (i0 : Fin P.n) (t : ZMod M) : Fin P.n → ZMod M :=
  Function.update v i0 (v i0 + t)

private noncomputable def residual (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (v : Fin P.n → ZMod M) : ZMod M :=
  Ring.inverse (collisionCoefficient P M j k W i0) * collisionForm P M j k W v

private noncomputable def projectToCollision (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (v : Fin P.n → ZMod M) : Fin P.n → ZMod M :=
  Function.update v i0 (v i0 - residual P M j k W i0 v)

private theorem residual_perturb (P : RawPopulation) (M : ℕ) [NeZero M]
    (hprime : Nat.Prime M) (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (hc : collisionCoefficient P M j k W i0 ≠ 0)
    (v : CollisionWeights P M j k W) (t : ZMod M) :
    residual P M j k W i0 (perturb v.1 i0 t) = t := by
  have hunit := prime_isUnit_of_ne_zero M hprime
    (collisionCoefficient P M j k W i0) hc
  have hinv : Ring.inverse (collisionCoefficient P M j k W i0) *
      collisionCoefficient P M j k W i0 = 1 :=
    Ring.inverse_mul_cancel _ hunit
  have hvform : collisionForm P M j k W v.1 = 0 := by
    rw [collisionForm_eq, v.2, sub_self]
  unfold residual perturb
  rw [collisionForm_update, hvform]
  calc
    Ring.inverse (collisionCoefficient P M j k W i0) *
        (0 + collisionCoefficient P M j k W i0 *
          (v.1 i0 + t - v.1 i0)) =
        (Ring.inverse (collisionCoefficient P M j k W i0) *
          collisionCoefficient P M j k W i0) * t := by ring
    _ = t := by rw [hinv, one_mul]

private theorem projectToCollision_form (P : RawPopulation) (M : ℕ) [NeZero M]
    (hprime : Nat.Prime M) (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (hc : collisionCoefficient P M j k W i0 ≠ 0)
    (v : Fin P.n → ZMod M) :
    collisionForm P M j k W (projectToCollision P M j k W i0 v) = 0 := by
  have hunit := prime_isUnit_of_ne_zero M hprime
    (collisionCoefficient P M j k W i0) hc
  have hinv : Ring.inverse (collisionCoefficient P M j k W i0) *
      collisionCoefficient P M j k W i0 = 1 :=
    Ring.inverse_mul_cancel _ hunit
  unfold projectToCollision residual
  rw [collisionForm_update]
  calc
    collisionForm P M j k W v + collisionCoefficient P M j k W i0 *
        (v i0 - Ring.inverse (collisionCoefficient P M j k W i0) *
          collisionForm P M j k W v - v i0) =
        collisionForm P M j k W v -
          (Ring.inverse (collisionCoefficient P M j k W i0) *
            collisionCoefficient P M j k W i0) *
              collisionForm P M j k W v := by ring
    _ = 0 := by rw [hinv]; ring

private theorem project_perturb (P : RawPopulation) (M : ℕ) [NeZero M]
    (hprime : Nat.Prime M) (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (hc : collisionCoefficient P M j k W i0 ≠ 0)
    (v : CollisionWeights P M j k W) (t : ZMod M) :
    projectToCollision P M j k W i0 (perturb v.1 i0 t) = v.1 := by
  have hr := residual_perturb P M hprime j k W i0 hc v t
  unfold projectToCollision
  rw [hr]
  unfold perturb
  funext i
  by_cases hi : i = i0
  · subst i
    simp
  · simp [Function.update_of_ne hi]

private theorem perturb_project (P : RawPopulation) (M : ℕ)
    (j k : P.Label) (W : Side) (i0 : Fin P.n)
    (v : Fin P.n → ZMod M) :
    perturb (projectToCollision P M j k W i0 v) i0
      (residual P M j k W i0 v) = v := by
  unfold perturb projectToCollision
  funext i
  by_cases hi : i = i0
  · subst i
    simp
  · simp [Function.update_of_ne hi]

private noncomputable def collisionWeightsTimesEquiv (P : RawPopulation)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (j k : P.Label) (W : Side)
    (i0 : Fin P.n) (hc : collisionCoefficient P M j k W i0 ≠ 0) :
    CollisionWeights P M j k W × ZMod M ≃ (Fin P.n → ZMod M) where
  toFun z := perturb z.1.1 i0 z.2
  invFun v :=
    (⟨projectToCollision P M j k W i0 v, by
      have hform := projectToCollision_form P M hprime j k W i0 hc v
      rw [collisionForm_eq] at hform
      exact sub_eq_zero.mp hform⟩,
      residual P M j k W i0 v)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      exact project_perturb P M hprime j k W i0 hc z.1 z.2
    · exact residual_perturb P M hprime j k W i0 hc z.1 z.2
  right_inv v := perturb_project P M j k W i0 v

private theorem card_collision_mul (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : P.grade < M) (j k : P.Label) (hne : j ≠ k)
    (W : Side) (hsame : P.coarse j W = P.coarse k W) (b : ZMod M) :
    ((bucket P M j b) ∩ (bucket P M k b)).card * M = (bucket P M j b).card := by
  obtain ⟨i0, hi0⟩ := exists_pivot P htight hinj j k hne W hsame
  have hc := collisionCoefficient_ne_zero P M hfloor j k W i0 hi0
  calc
    ((bucket P M j b) ∩ (bucket P M k b)).card * M =
        Fintype.card {omega : HashOutcome P M //
          omega ∈ (bucket P M j b) ∩ (bucket P M k b)} * M := by
            rw [Fintype.card_coe]
    _ = Fintype.card (CollisionWeights P M j k W) * M := by
      rw [Fintype.card_congr
        (collisionEquiv P htight M hprime hodd j k W hsame b)]
    _ = Fintype.card (CollisionWeights P M j k W × ZMod M) := by
      simp [ZMod.card]
    _ = Fintype.card (Fin P.n → ZMod M) :=
      Fintype.card_congr (collisionWeightsTimesEquiv P M hprime j k W i0 hc)
    _ = M ^ P.n := by simp [ZMod.card]
    _ = (bucket P M j b).card := (card_bucket P htight M hprime hodd j b).symm

theorem asymmetric_hash (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M) (hfloor : P.grade < M) :
  (∀ j b, (bucket P M j b).card*M^2 = Fintype.card (HashOutcome P M)) ∧
  (∀ j k, j ≠ k → ∀ W, P.coarse j W = P.coarse k W → ∀ b,
    ((bucket P M j b) ∩ (bucket P M k b)).card*M = (bucket P M j b).card) := by
  constructor
  · intro j b
    rw [card_bucket P htight M hprime hodd j b]
    simp [HashOutcome, ZMod.card, pow_add]
  · intro j k hne W hsame b
    exact card_collision_mul P htight hinj M hprime hodd hfloor j k hne W hsame b

end OmegaBound.ADVXXZGeneral
end
