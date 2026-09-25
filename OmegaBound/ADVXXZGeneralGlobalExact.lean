import OmegaBound.ADVXXZGeneralAmend27GExactNear
import OmegaBound.ADVXXZGeneralGlobalPQFiniteQ
import OmegaBound.ADVXXZGeneralAmend25GlobalBridge
import OmegaBound.ADVXXZGeneralGlobalOrderedDeletions
import OmegaBound.ADVXXZGeneralPQExponentsParent25
import OmegaBound.ADVXXZGeneralGood
import OmegaBound.ADVXXZGeneralRepairFibresFinal
import OmegaBound.ADVXXZGeneralHRepair
import OmegaBound.ADVXXZGeneralMap

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

private noncomputable def globalCentreJointCount {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (r : Fin 6) (u : Shape w) : ℕ :=
  Classical.choose (((hb.2 r).2 u).1)

private theorem globalCentreJointCount_spec {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (r : Fin 6) (u : Shape w) :
    (b : ℚ) * g.joint.prob (r, u) = (globalCentreJointCount g hb r u : ℚ) :=
  Classical.choose_spec (((hb.2 r).2 u).1)

private noncomputable def globalCentreSplitCount {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w)
    (sigma : Chunk w) : ℕ :=
  Classical.choose (((hb.2 r).2 u).2 W sigma)

private theorem globalCentreSplitCount_spec {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w)
    (sigma : Chunk w) :
    (b : ℚ) * g.joint.prob (r, u) * (g.beta W r u).prob sigma =
      (globalCentreSplitCount g hb W r u sigma : ℚ) :=
  Classical.choose_spec (((hb.2 r).2 u).2 W sigma)

private theorem globalCentreSplitCount_sum {w b : ℕ} (g : GlobalSpec w)
    (hb : GlobalIntegral g b) (W : Side) (r : Fin 6) (u : Shape w) :
    ∑ sigma, globalCentreSplitCount g hb W r u sigma = globalCentreJointCount g hb r u := by
  apply Nat.cast_injective (R := ℚ)
  push_cast
  calc
    ∑ sigma, (globalCentreSplitCount g hb W r u sigma : ℚ) =
        ∑ sigma, (b : ℚ) * g.joint.prob (r, u) * (g.beta W r u).prob sigma := by
      apply Finset.sum_congr rfl
      intro sigma _
      exact (globalCentreSplitCount_spec g hb W r u sigma).symm
    _ = (b : ℚ) * g.joint.prob (r, u) * ∑ sigma, (g.beta W r u).prob sigma := by
      rw [Finset.mul_sum]
    _ = (b : ℚ) * g.joint.prob (r, u) := by
      rw [RatDist.sum_prob, mul_one]
    _ = (globalCentreJointCount g hb r u : ℚ) :=
      globalCentreJointCount_spec g hb r u

private theorem scaledGlobalCentreCount (b m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * a = (k : ℚ)) :
    (((b*m : ℕ) : ℚ) * a).floor.toNat = k*m := by
  have hq : (((b*m : ℕ) : ℚ) * a) = ((k*m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k*m : ℕ) : ℚ).floor) = (k*m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k*m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k*m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

/-- The exact grid at the rational centre supplied by `GlobalIntegral`, at multiplier `m`. -/
noncomputable def globalCentreExactGrid {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ) : ExactGrid g (b*m) where
  count W r u sigma := globalCentreSplitCount g hb W r u sigma * m
  total W r u := by
    rw [← Finset.sum_mul, globalCentreSplitCount_sum]
    exact (scaledGlobalCentreCount b m (globalCentreJointCount g hb r u)
      (g.joint.prob (r, u)) (globalCentreJointCount_spec g hb r u)).symm
  graded W r u sigma hgrade := by
    have hnum : (g.beta W r u).num sigma = 0 := by
      by_contra hne
      exact hgrade (hg.support W r u sigma hne)
    have hprob : (g.beta W r u).prob sigma = 0 := by
      simp [RatDist.prob, hnum]
    have hspec := globalCentreSplitCount_spec g hb W r u sigma
    rw [hprob, mul_zero] at hspec
    have hcount : globalCentreSplitCount g hb W r u sigma = 0 := by
      exact_mod_cast hspec.symm
    simp [hcount]

private theorem globalCentreExactGrid_normalized_prob {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) (sigma : Chunk w)
    (hk : 0 < (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) :
    ((globalCentreExactGrid g hg hb m).count W r u sigma : ℚ) /
        (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat =
      (g.beta W r u).prob sigma := by
  have hscale := scaledGlobalCentreCount b m (globalCentreJointCount g hb r u)
    (g.joint.prob (r, u)) (globalCentreJointCount_spec g hb r u)
  have hpos : 0 < globalCentreJointCount g hb r u * m := by
    rw [← hscale]
    exact hk
  rw [hscale]
  change ((globalCentreSplitCount g hb W r u sigma * m : ℕ) : ℚ) /
      ((globalCentreJointCount g hb r u * m : ℕ) : ℚ) = _
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hpos.ne')).2
  push_cast
  rw [← globalCentreSplitCount_spec g hb W r u sigma,
    ← globalCentreJointCount_spec g hb r u]
  ring

private theorem globalCentreExactGrid_normalized_probR {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) (sigma : Chunk w)
    (hk : 0 < (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) :
    ((globalCentreExactGrid g hg hb m).count W r u sigma : ℝ) /
        (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat =
      (g.beta W r u).probR sigma := by
  have h := globalCentreExactGrid_normalized_prob g hg hb m W r u sigma hk
  have hr := congrArg (fun x : ℚ => (x : ℝ)) h
  simpa [RatDist.prob, RatDist.probR, Rat.cast_div] using hr

private noncomputable def globalCentreGridBeta {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) : SplitDist w :=
  let k := (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat
  if hk : 0 < k then
    { num := (globalCentreExactGrid g hg hb m).count W r u
      den := k
      den_pos := hk
      sum_num := (globalCentreExactGrid g hg hb m).total W r u }
  else
    g.beta W r u

private theorem globalCentreGridBeta_probR {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) (sigma : Chunk w) :
    (globalCentreGridBeta g hg hb m W r u).probR sigma =
      (g.beta W r u).probR sigma := by
  unfold globalCentreGridBeta
  dsimp only
  by_cases hk : 0 < (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat
  · rw [dif_pos hk]
    exact globalCentreExactGrid_normalized_probR g hg hb m W r u sigma hk
  · rw [dif_neg hk]

private theorem splitEntropy_eq_of_probR_eq {w : ℕ} (P Q : SplitDist w)
    (h : ∀ sigma, P.probR sigma = Q.probR sigma) :
    splitEntropy P = splitEntropy Q := by
  unfold splitEntropy
  congr 1
  funext sigma
  exact h sigma

private theorem weightedSplit_eq_of_probR_eq {iota : Type*} [Fintype iota] {w : ℕ}
    (mass : iota → ℝ) (P Q : iota → SplitDist w) (selected : iota → Prop)
    [DecidablePred selected]
    (h : ∀ i sigma, (P i).probR sigma = (Q i).probR sigma) :
    weightedSplit mass P selected = weightedSplit mass Q selected := by
  funext sigma
  unfold weightedSplit
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [h i sigma]
  · rfl

private theorem globalRegionRate_update_beta {w : ℕ} (d : GlobalData w)
    (beta : Side → Fin 6 → Shape w → SplitDist w)
    (hbeta : ∀ W r u sigma, (beta W r u).probR sigma = (d.beta W r u).probR sigma)
    (r : Fin 6) :
    globalRegionRate {d with beta := beta} r = globalRegionRate d r := by
  have havg (W : Side) :
      globalAverage {d with beta := beta} r W = globalAverage d r W := by
    unfold globalAverage
    funext sigma
    apply Finset.sum_congr rfl
    intro u _
    rw [hbeta W r u]
  have hsplit (W : Side) (u : Shape w) :
      splitEntropy (beta W r u) = splitEntropy (d.beta W r u) :=
    splitEntropy_eq_of_probR_eq _ _ (hbeta W r u)
  have hweighted (W : Side) (selected : Shape w → Prop) [DecidablePred selected] :
      weightedSplit (d.alpha r) (beta W r) selected =
        weightedSplit (d.alpha r) (d.beta W r) selected :=
    weightedSplit_eq_of_probR_eq _ _ _ _ (hbeta W r)
  have heta (X Y Z : Side) :
      globalEta {d with beta := beta} r X Y Z = globalEta d r X Y Z := by
    unfold globalEta
    simp only [hsplit, hweighted]
  have hlambda (X Y Z : Side) :
      globalLambda {d with beta := beta} r X Y Z = globalLambda d r X Y Z := by
    unfold globalLambda
    simp only [hsplit, hweighted]
  unfold globalRegionRate
  simp only [havg, heta, hlambda]

/-- On the integral centre grid, the finite histogram rate is the specified global rate. -/
theorem gridRate_globalCentreExactGrid {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ) :
    gridRate g (b*m) (globalCentreExactGrid g hg hb m) = gRate g := by
  unfold gridRate gRate
  change Real.log 2 * ∑ r, g.A.probR r *
      globalRegionRate {g.toPaper with beta := globalCentreGridBeta g hg hb m} r = _
  apply congrArg (fun x : ℝ => Real.log 2 * x)
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun x : ℝ => g.A.probR r * x)
  exact globalRegionRate_update_beta g.toPaper (globalCentreGridBeta g hg hb m)
    (globalCentreGridBeta_probR g hg hb m) r

private def globalExactSideWord {A : Type} (x y z : A) : Side → A
  | .X => x
  | .Y => y
  | .Z => z

private theorem globalExactSideWord_apply {A : Type} {B : A → Type}
    (x y z : (a : A) → B a) (W : Side) (a : A) :
    globalExactSideWord x y z W a = globalExactSideWord (x a) (y a) (z a) W := by
  cases W <;> rfl

private theorem globalExact_lvl7_eq_zero {q w : ℕ}
    (a : Fin w → CW90.Idx7 q) (h : chunkLvl (chunkOf a) = 0) (c : Fin w) :
    (CW90.lvl7 (a c)).val = 0 := by
  have hle : (chunkOf a c).val ≤ chunkLvl (chunkOf a) := by
    unfold chunkLvl
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun p => (chunkOf a p).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simpa only [chunkOf] using (show (chunkOf a c).val = 0 by omega)

private theorem globalExact_cwZ_ne_permutations {q : ℕ} (x y z : CW90.Idx7 q)
    (h : cwZ q x y z ≠ 0) :
    cwZ q y x z ≠ 0 ∧ cwZ q x z y ≠ 0 ∧ cwZ q y z x ≠ 0 ∧
      cwZ q z x y ≠ 0 ∧ cwZ q z y x ≠ 0 := by
  rcases x with (_ | x0) | x0 <;>
    rcases y with (_ | y0) | y0 <;>
      rcases z with (_ | z0) | z0 <;> simp_all [cwZ]

set_option maxHeartbeats 1000000 in
private theorem globalExact_chunk_reflect_last {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf z) = 0) :
    chunkOf y = reflect (chunkOf x) := by
  funext c
  apply Fin.ext
  have hz := globalExact_lvl7_eq_zero z hzero c
  have hc := hcw c
  rcases hx : x c with (_ | x0) | x0 <;>
    rcases hy : y c with (_ | y0) | y0 <;>
      rcases hz' : z c with (_ | z0) | z0 <;>
        simp_all [cwZ, chunkOf, reflect, CW90.lvl7]

private theorem globalExact_chunk_reflect {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf (globalExactSideWord x y z C)) = 0) :
    chunkOf (globalExactSideWord x y z B) =
      reflect (chunkOf (globalExactSideWord x y z A)) := by
  cases A <;> cases B <;> cases C <;> simp_all [globalExactSideWord]
  · exact globalExact_chunk_reflect_last x y z hcw hzero
  · exact globalExact_chunk_reflect_last x z y
      (fun c => (globalExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.1) hzero
  · exact globalExact_chunk_reflect_last y x z
      (fun c => (globalExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).1) hzero
  · exact globalExact_chunk_reflect_last y z x
      (fun c => (globalExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.1) hzero
  · exact globalExact_chunk_reflect_last z x y
      (fun c => (globalExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.1) hzero
  · exact globalExact_chunk_reflect_last z y x
      (fun c => (globalExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.2) hzero

private theorem globalExact_reflect_reflect {w : ℕ} (sigma : Chunk w) :
    reflect (reflect sigma) = sigma := by
  funext c
  apply Fin.ext
  simp only [reflect]
  have hc := (sigma c).isLt
  omega

private theorem globalExact_conZ_ne_data {q w i j k : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (h : conZ q w i j k x y z ≠ 0) :
    levOf x = i ∧ levOf y = j ∧ levOf z = k ∧
      ∀ c, cwZ q (x c) (y c) (z c) ≠ 0 := by
  unfold conZ zoP at h
  split at h
  · rename_i hlevels
    refine ⟨hlevels.1, hlevels.2.1, hlevels.2.2, ?_⟩
    intro c hc
    apply h
    unfold tensorPower
    exact Finset.prod_eq_zero (Finset.mem_univ c) hc
  · simp at h

/-- A nonzero coefficient of the raw exact-grid tensor forces the reflected boundary equalities.
This is the zero-output dispatch required before the live boundary-compatible global branch. -/
theorem gridBoundaryCompatible_of_exactGridTensor_coeff_ne_zero {q w n : ℕ}
    (g : GlobalSpec w) (xi : ExactGrid g n)
    (x : (exactGridTensor q g n xi).X) (y : (exactGridTensor q g n xi).Y)
    (z : (exactGridTensor q g n xi).Z)
    (hcoeff : (exactGridTensor q g n xi).tensor x y z ≠ 0) :
    GridBoundaryCompatible xi := by
  classical
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  let k := fun t : Fin (Fintype.card (Fin 6 × Shape w)) =>
    ((n : ℚ) * g.joint.prob (e t)).floor.toNat
  let L := (t : Fin (Fintype.card (Fin 6 × Shape w))) →
    Fin (k t) → Fin w → CW90.Idx7 q
  let keep := fun (W : Side) (v : L) => ∀ t sigma,
    typeCnt (chunkSeq (v t)) sigma = xi.count W (e t).1 (e t).2 sigma
  let core := fun t : Fin (Fintype.card (Fin 6 × Shape w)) =>
    tensorPower (conZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2))
      (k t) (x t) (y t) (z t)
  change (if keep .X x ∧ keep .Y y ∧ keep .Z z then ∏ t, core t else 0) ≠ 0 at hcoeff
  have hall : keep .X x ∧ keep .Y y ∧ keep .Z z := by
    by_contra hnot
    rw [if_neg hnot] at hcoeff
    exact hcoeff rfl
  have hprod : ∏ t, core t ≠ 0 := by
    rw [if_pos hall] at hcoeff
    exact hcoeff
  have hkeep (W : Side) : keep W (globalExactSideWord x y z W) := by
    cases W with
    | X => simpa only [globalExactSideWord] using hall.1
    | Y => simpa only [globalExactSideWord] using hall.2.1
    | Z => simpa only [globalExactSideWord] using hall.2.2
  intro r u S0 S1 S2 h12 h10 h20 hzero sigma
  let t := Fintype.equivFin (Fin 6 × Shape w) (r, u)
  have het : e t = (r, u) := by simp [e, t]
  have hcore : core t ≠ 0 := by
    intro ht
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ t) ht)
  have hcon (i : Fin (k t)) :
      conZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2)
        (x t i) (y t i) (z t i) ≠ 0 := by
    intro hi
    apply hcore
    unfold core tensorPower
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hdata (i : Fin (k t)) := globalExact_conZ_ne_data
    (x t i) (y t i) (z t i) (hcon i)
  have hlevel (i : Fin (k t)) :
      chunkLvl (chunkOf (globalExactSideWord (x t i) (y t i) (z t i) S0)) =
        coord S0 u := by
    cases S0 with
    | X => simpa only [globalExactSideWord, levOf, het] using (hdata i).1
    | Y => simpa only [globalExactSideWord, levOf, het] using (hdata i).2.1
    | Z => simpa only [globalExactSideWord, levOf, het] using (hdata i).2.2.1
  have hreflect (i : Fin (k t)) :
      chunkOf (globalExactSideWord (x t i) (y t i) (z t i) S2) =
        reflect (chunkOf (globalExactSideWord (x t i) (y t i) (z t i) S1)) := by
    apply globalExact_chunk_reflect (x t i) (y t i) (z t i) S1 S2 S0
      h12 h10 h20
    · exact (hdata i).2.2.2
    · rw [hlevel i, hzero]
  have hreflect' (i : Fin (k t)) :
      chunkOf (globalExactSideWord x y z S2 t i) =
        reflect (chunkOf (globalExactSideWord x y z S1 t i)) := by
    cases S1 <;> cases S2 <;> simpa only [globalExactSideWord] using hreflect i
  have hcount :
      typeCnt (chunkSeq (globalExactSideWord x y z S1 t)) sigma =
        typeCnt (chunkSeq (globalExactSideWord x y z S2 t)) (reflect sigma) := by
    unfold typeCnt
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, chunkSeq,
      globalExactSideWord_apply]
    rw [hreflect' i]
    constructor
    · intro hi
      rw [hi]
    · intro hi
      have hr := congrArg reflect hi
      simpa only [globalExact_reflect_reflect] using hr
  calc
    xi.count S1 r u sigma =
        typeCnt (chunkSeq (globalExactSideWord x y z S1 t)) sigma := by
      have ht := hkeep S1 t sigma
      rw [het] at ht
      exact ht.symm
    _ = typeCnt (chunkSeq (globalExactSideWord x y z S2 t)) (reflect sigma) := hcount
    _ = xi.count S2 r u (reflect sigma) := by
      have ht := hkeep S2 t (reflect sigma)
      rw [het] at ht
      exact ht

/-- Boundary-incompatible grids have the identically zero raw tensor. -/
theorem exactGridTensor_eq_zero_of_not_boundaryCompatible {q w n : ℕ}
    (g : GlobalSpec w) (xi : ExactGrid g n) (hxi : ¬ GridBoundaryCompatible xi) :
    (exactGridTensor q g n xi).tensor = 0 := by
  funext x y z
  apply Classical.byContradiction
  intro hcoeff
  exact hxi (gridBoundaryCompatible_of_exactGridTensor_coeff_ne_zero g xi x y z hcoeff)

private theorem globalCentre_approxConsistent_iff {q w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w)
    (x : Fin ((((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) →
      Fin w → CW90.Idx7 q)
    (hk : 0 < (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) :
    ApproxConsistent 0 (g.beta W r u) (chunkSeq x) ↔
      ∀ sigma, typeCnt (chunkSeq x) sigma =
        (globalCentreExactGrid g hg hb m).count W r u sigma := by
  rw [approxConsistent_zero_iff _ _ hk, consistent_iff_prob _ _ hk]
  constructor
  · intro h sigma
    have hrat : (typeCnt (chunkSeq x) sigma : ℚ) /
        ((((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℚ) =
          ((globalCentreExactGrid g hg hb m).count W r u sigma : ℚ) /
            (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat := by
      calc
        _ = (g.beta W r u).prob sigma := by simpa [emp] using h sigma
        _ = _ := (globalCentreExactGrid_normalized_prob g hg hb m W r u sigma hk).symm
    have hkq :
        ((((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hk.ne'
    field_simp [hkq] at hrat
    exact_mod_cast hrat
  · intro h sigma
    unfold emp
    rw [h sigma]
    exact globalCentreExactGrid_normalized_prob g hg hb m W r u sigma hk

private theorem globalCentreExactGrid_count_eq_zero_of_cell_eq_zero {w b : ℕ}
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w) (sigma : Chunk w)
    (hk : (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0) :
    (globalCentreExactGrid g hg hb m).count W r u sigma = 0 := by
  have hle : (globalCentreExactGrid g hg hb m).count W r u sigma ≤
      ∑ tau, (globalCentreExactGrid g hg hb m).count W r u tau :=
    Finset.single_le_sum (fun tau _ => Nat.zero_le _) (Finset.mem_univ sigma)
  rw [(globalCentreExactGrid g hg hb m).total W r u, hk] at hle
  omega

private theorem globalCentre_keep_at_of_cell_eq_zero {q w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (W : Side) (r : Fin 6) (u : Shape w)
    (x : Fin ((((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat) →
      Fin w → CW90.Idx7 q)
    (hk : (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = 0) :
    ∀ sigma, typeCnt (chunkSeq x) sigma =
      (globalCentreExactGrid g hg hb m).count W r u sigma := by
  intro sigma
  rw [globalCentreExactGrid_count_eq_zero_of_cell_eq_zero g hg hb m W r u sigma hk]
  unfold typeCnt
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies]
  intro i
  have hi := i.isLt
  omega

/-- The exact histogram zero-out at the integral centre is the literal zero-tolerance global
output tensor, on their common physical legs. -/
theorem exactGridTensor_globalCentre {q w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ) :
    (exactGridTensor q g (b*m) (globalCentreExactGrid g hg hb m)).tensor =
      (globalOutputZ q g (b*m) 0).tensor := by
  classical
  funext x y z
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  let k := fun t : Fin (Fintype.card (Fin 6 × Shape w)) =>
    (((b*m : ℕ) : ℚ) * g.joint.prob (e t)).floor.toNat
  let L := (t : Fin (Fintype.card (Fin 6 × Shape w))) →
    Fin (k t) → Fin w → CW90.Idx7 q
  let keep := fun (W : Side) (v : L) => ∀ t sigma,
    typeCnt (chunkSeq (v t)) sigma =
      (globalCentreExactGrid g hg hb m).count W (e t).1 (e t).2 sigma
  let core := fun t : Fin (Fintype.card (Fin 6 × Shape w)) =>
    tensorPower (conZ q w (coord .X (e t).2) (coord .Y (e t).2) (coord .Z (e t).2))
      (k t) (x t) (y t) (z t)
  change (if keep .X x ∧ keep .Y y ∧ keep .Z z then ∏ t, core t else 0) =
    ∏ t, if k t = 0 then 1 else if
      ApproxConsistent 0 (g.beta .X (e t).1 (e t).2) (chunkSeq (x t)) ∧
      ApproxConsistent 0 (g.beta .Y (e t).1 (e t).2) (chunkSeq (y t)) ∧
      ApproxConsistent 0 (g.beta .Z (e t).1 (e t).2) (chunkSeq (z t))
      then core t else 0
  have hzero (W : Side) (v : L) (t : Fin (Fintype.card (Fin 6 × Shape w)))
      (hk : k t = 0) : ∀ sigma, typeCnt (chunkSeq (v t)) sigma =
        (globalCentreExactGrid g hg hb m).count W (e t).1 (e t).2 sigma := by
    simpa only [k, e] using
      globalCentre_keep_at_of_cell_eq_zero g hg hb m W (e t).1 (e t).2 (v t) hk
  have happ (W : Side) (v : L) (t : Fin (Fintype.card (Fin 6 × Shape w)))
      (hk : 0 < k t) :
      ApproxConsistent 0 (g.beta W (e t).1 (e t).2) (chunkSeq (v t)) ↔
        ∀ sigma, typeCnt (chunkSeq (v t)) sigma =
          (globalCentreExactGrid g hg hb m).count W (e t).1 (e t).2 sigma := by
    simpa only [k, e] using
      globalCentre_approxConsistent_iff g hg hb m W (e t).1 (e t).2 (v t) hk
  by_cases hX : keep .X x
  · by_cases hY : keep .Y y
    · by_cases hZ : keep .Z z
      · rw [if_pos ⟨hX, hY, hZ⟩]
        apply Finset.prod_congr rfl
        intro t _
        by_cases hk : k t = 0
        · rw [if_pos hk]
          unfold core tensorPower
          apply Finset.prod_eq_one
          intro i _
          have hi := i.isLt
          omega
        · rw [if_neg hk, if_pos]
          exact ⟨(happ .X x t (Nat.pos_of_ne_zero hk)).2 (hX t),
            (happ .Y y t (Nat.pos_of_ne_zero hk)).2 (hY t),
            (happ .Z z t (Nat.pos_of_ne_zero hk)).2 (hZ t)⟩
      · rw [if_neg (fun h => hZ h.2.2)]
        symm
        simp only [keep, not_forall] at hZ
        obtain ⟨t, sigma, hne⟩ := hZ
        apply Finset.prod_eq_zero (Finset.mem_univ t)
        have hk : k t ≠ 0 := fun hk => hne (hzero .Z z t hk sigma)
        rw [if_neg hk, if_neg]
        intro ha
        exact hne ((happ .Z z t (Nat.pos_of_ne_zero hk)).1 ha.2.2 sigma)
    · rw [if_neg (fun h => hY h.2.1)]
      symm
      simp only [keep, not_forall] at hY
      obtain ⟨t, sigma, hne⟩ := hY
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      have hk : k t ≠ 0 := fun hk => hne (hzero .Y y t hk sigma)
      rw [if_neg hk, if_neg]
      intro ha
      exact hne ((happ .Y y t (Nat.pos_of_ne_zero hk)).1 ha.2.1 sigma)
  · rw [if_neg (fun h => hX h.1)]
    symm
    simp only [keep, not_forall] at hX
    obtain ⟨t, sigma, hne⟩ := hX
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    have hk : k t ≠ 0 := fun hk => hne (hzero .X x t hk sigma)
    rw [if_neg hk, if_neg]
    intro ha
    exact hne ((happ .X x t (Nat.pos_of_ne_zero hk)).1 ha.1 sigma)

/-- The exact-global corollary follows formally from the uniform exact-grid producer, which is
proved as `global_exact_uniform` (`ADVXXZGeneralGlobalExactConsumer37`). -/
theorem global_exact_of_uniform (q w b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (huniform :
      ∃ ell : ℕ → ℝ, (∀ m, 0 ≤ ell m) ∧ Sublinear (fun m => b*m) ell ∧
        ∃ M : ℕ, ∀ m, M ≤ m → ∀ xi : ExactGrid g (b*m),
          ∃ V N : ℕ,
            Real.exp (gridRate g (b*m) xi*(b*m:ℝ)-ell m) ≤ (V:ℝ) ∧
            PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
              (copiesZ V (exactGridTensor q g (b*m) xi)).tensor) :
  ∃ (V : ℕ → ℕ) (ell : ℕ → ℝ),
    (∀ m, 0 ≤ ell m) ∧ Sublinear (fun m => b*m) ell ∧
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      Real.exp (gRate g * (b*m:ℝ) - ell m) ≤ (V m:ℝ) ∧
      ∀ (F : Type u) [Field F],
        Degenerates F ((topZ q w (b*m)).over F)
          ((copiesZ (V m) (globalOutputZ q g (b*m) 0)).over F) := by
  classical
  obtain ⟨ell, hell, hsub, M, hproducer⟩ := huniform
  let centre := fun m => globalCentreExactGrid g hg hb m
  let V : ℕ → ℕ := fun m =>
    if hm : M ≤ m then Classical.choose (hproducer m hm (centre m)) else 0
  refine ⟨V, ell, hell, hsub, M, ?_⟩
  intro m hm
  let hex := hproducer m hm (centre m)
  let v := Classical.choose hex
  let n := Classical.choose (Classical.choose_spec hex)
  have hvn := Classical.choose_spec (Classical.choose_spec hex)
  have hVm : V m = v := by simp only [V, hm, dite_true, v, hex]
  rw [hVm]
  constructor
  · rw [← gridRate_globalCentreExactGrid g hg hb m]
    exact hvn.1
  · intro F _
    apply integral_degenerates F (topZ q w (b*m))
      (copiesZ v (globalOutputZ q g (b*m) 0))
    refine ⟨n, ?_⟩
    have hcopy :
        (copiesZ v (exactGridTensor q g (b*m) (centre m))).tensor =
          (copiesZ v (globalOutputZ q g (b*m) 0)).tensor := by
      unfold copiesZ
      rw [exactGridTensor_globalCentre g hg hb m]
    rw [← hcopy]
    exact hvn.2

end
end OmegaBound.ADVXXZGeneral
end
