import OmegaBound.ADVXXZGeneralReleasedOrdinaryCertificate
import OmegaBound.ADVXXZT2Paired

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace OmegaBound.ADVXXZGeneral

private theorem prob_cast {ι : Type*} [Fintype ι] (P : RatDist ι) (i : ι) :
    ((P.prob i : ℚ) : ℝ) = P.probR i := by
  simp [RatDist.prob, RatDist.probR]

private theorem prob_eq_of_cross {ι : Type*} [Fintype ι]
    (P Q : RatDist ι) (i j : ι)
    (h : P.num i * Q.den = Q.num j * P.den) : P.prob i = Q.prob j := by
  apply (div_eq_div_iff P.den_ne_zero Q.den_ne_zero).2
  exact_mod_cast h

theorem released_global_joint_eq (r : Fin 6) (u : Shape 4) :
    releasedGlobalSpec.joint.prob (r, u) =
      releasedGlobalSpec.A.prob r * (releasedGlobalSpec.alpha r).prob u := by
  apply (Rat.cast_injective : Function.Injective ((↑·) : ℚ → ℝ))
  simp only [Rat.cast_mul, prob_cast]
  exact OmegaBound.ADVXXZCertificateGlobalData.certificateJoint_probR r u


theorem released_global_boundary (r : Fin 6) (u : Shape 4) :
    BoundaryCompatible u (fun W => releasedGlobalSpec.beta W r u) := by
  intro Z X Y hXY hXZ hYZ hZ σ
  have hm := OmegaBound.ADVXXZG1.g1_mirror r u σ
  have hmr := OmegaBound.ADVXXZG1.g1_mirror r u (reflect σ)
  unfold OmegaBound.ADVXXZG1.MirrorOK at hm hmr
  have hcbar : OmegaBound.ADVXXZG1.cbar (reflect σ) = σ := by
    change OmegaBound.ADVXXZG1.cbar (OmegaBound.ADVXXZG1.cbar σ) = σ
    exact OmegaBound.ADVXXZG1.cbar_cbar σ
  have h_xz (h : coord .Y u = 0) :
      (releasedGlobalSpec.beta .X r u).prob σ =
        (releasedGlobalSpec.beta .Z r u).prob (reflect σ) := by
    apply prob_eq_of_cross
    exact hm.1 (by simpa [coord] using h)
  have h_zx (h : coord .Y u = 0) :
      (releasedGlobalSpec.beta .Z r u).prob σ =
        (releasedGlobalSpec.beta .X r u).prob (reflect σ) := by
    have hcross := hmr.1 (by simpa [coord] using h)
    rw [hcbar] at hcross
    exact (prob_eq_of_cross _ _ _ _ hcross).symm
  have h_zy (h : coord .X u = 0) :
      (releasedGlobalSpec.beta .Z r u).prob σ =
        (releasedGlobalSpec.beta .Y r u).prob (reflect σ) := by
    apply prob_eq_of_cross
    exact hm.2.1 (by simpa [coord] using h)
  have h_yz (h : coord .X u = 0) :
      (releasedGlobalSpec.beta .Y r u).prob σ =
        (releasedGlobalSpec.beta .Z r u).prob (reflect σ) := by
    have hcross := hmr.2.1 (by simpa [coord] using h)
    rw [hcbar] at hcross
    exact (prob_eq_of_cross _ _ _ _ hcross).symm
  have h_yx (h : coord .Z u = 0) :
      (releasedGlobalSpec.beta .Y r u).prob σ =
        (releasedGlobalSpec.beta .X r u).prob (reflect σ) := by
    apply prob_eq_of_cross
    exact hm.2.2 (by simpa [coord] using h)
  have h_xy (h : coord .Z u = 0) :
      (releasedGlobalSpec.beta .X r u).prob σ =
        (releasedGlobalSpec.beta .Y r u).prob (reflect σ) := by
    have hcross := hmr.2.2 (by simpa [coord] using h)
    rw [hcbar] at hcross
    exact (prob_eq_of_cross _ _ _ _ hcross).symm
  fin_cases Z <;> fin_cases X <;> fin_cases Y <;> simp_all


set_option maxRecDepth 100000 in
theorem ordinary_mixture (W : Side)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (σ : Chunk 2) :
    (releasedOrdinaryParent.beta W t).prob σ =
      ∑ r, (releasedOrdinaryData2.A t).prob r *
        (releasedOrdinaryData2.betaRegion W t r).prob σ := by
  change (releasedOrdinaryParent.beta W t).prob σ =
    ∑ r, ordinaryRegionDist.prob r * (releasedOrdinaryParent.beta W t).prob σ
  simp [ordinaryRegionDist, RatDist.prob, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
theorem ordinary_regional_support (W : Side)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) :
    Supported (releasedOrdinaryData2.betaRegion W t r)
      (match W with
        | .X => releasedOrdinaryParent.i t
        | .Y => releasedOrdinaryParent.j t
        | .Z => releasedOrdinaryParent.k t) := by
  intro σ hσ
  have hs := releasedOrdinaryParent.beta_supported W t σ
  apply hs
  change (releasedOrdinaryParent.beta W t).num σ ≠ 0 at hσ
  exact div_ne_zero (Nat.cast_ne_zero.mpr hσ)
    (releasedOrdinaryParent.beta W t).denR_ne_zero

theorem ordinary_child_support (W : Side)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (u : ChildShape releasedOrdinaryParent t) :
    Supported (releasedOrdinaryData2.betaChild W t r u) (coord W u.1) := by
  intro σ hσ
  simp only [releasedOrdinaryData2, ordinaryChildBeta, RatDist.prob] at hσ ⊢
  split at hσ
  · assumption
  · simp at hσ

private theorem ordinary_dirac_reflect {x a b : ℕ} (hx : x < 3) (hab : a + b = 2) :
    (if x = a then (1 : ℚ) else 0) = (if 2 - x = b then 1 else 0) := by
  have hiff : x = a ↔ 2 - x = b := by omega
  exact if_congr hiff rfl rfl

theorem ordinary_child_boundary (u : Shape 1) :
    BoundaryCompatible u (fun W => ordinaryChildBeta W u) := by
  intro Z X Y hXY hXZ hYZ hZ σ
  have hu := u.property
  change (u.1.1 : ℕ) + (u.1.2.1 : ℕ) + (u.1.2.2 : ℕ) = 2 at hu
  have hσ := (σ 0).isLt
  fin_cases Z <;> fin_cases X <;> fin_cases Y
  all_goals simp_all [ordinaryChildBeta, RatDist.prob, reflect, coord]
  all_goals apply ordinary_dirac_reflect <;> omega

theorem ordinary_complement_coord (W : Side)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence))
    (u : ChildShape releasedOrdinaryParent t) :
    coord W (complement releasedOrdinaryParent t u).1 =
      coord W (ordinaryOccurrence t).1.2.2.1 - coord W u.1 := by
  cases W <;> rfl

theorem ordinary_large_coord
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :
    coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1)
      (ordinaryOccurrence t).1.2.2.1 = 2 := by
  have hx := (ordinaryOccurrence t).2.2.1
  have hy := (ordinaryOccurrence t).2.2.2.1
  have hz := (ordinaryOccurrence t).2.2.2.2
  have hs := (ordinaryOccurrence t).1.2.2.1.property
  change coord .X (ordinaryOccurrence t).1.2.2.1 +
    coord .Y (ordinaryOccurrence t).1.2.2.1 +
    coord .Z (ordinaryOccurrence t).1.2.2.1 = 4 at hs
  simp only [ordinaryLargeSide]
  split
  · assumption
  · split
    · assumption
    · omega

theorem ordinary_complement_large
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence))
    (u : ChildShape releasedOrdinaryParent t) :
    coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1)
        (complement releasedOrdinaryParent t u).1 = 1 ↔
      coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) u.1 = 1 := by
  rw [ordinary_complement_coord, ordinary_large_coord]
  omega

theorem ordinary_alpha_num_complement
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence))
    (u : ChildShape releasedOrdinaryParent t) :
    (if coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1)
          (complement releasedOrdinaryParent t u).1 = 1
      then ordinaryD / 2 - (ordinaryTarget t).muNum
      else (ordinaryTarget t).muNum) =
    (if coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) u.1 = 1
      then ordinaryD / 2 - (ordinaryTarget t).muNum
      else (ordinaryTarget t).muNum) := by
  exact if_congr (ordinary_complement_large t u) rfl rfl

set_option maxRecDepth 100000 in
theorem ordinary_out_eq
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (u : ChildShape releasedOrdinaryParent t) :
    (releasedOrdinaryData2.outBase ⟨t, r, u⟩ : ℚ) =
      (ordinaryD ^ 4 : ℚ) * releasedOrdinaryParent.baseN t *
        (releasedOrdinaryData2.A t).prob r *
        ((releasedOrdinaryData2.alpha t r).prob u +
          (releasedOrdinaryData2.alpha t r).prob
            (complement releasedOrdinaryParent t u)) := by
  have hDnat : ordinaryD ≠ 0 := Nat.ne_of_gt (by decide +kernel)
  have hD : (ordinaryD : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDnat
  by_cases hr : r = 0
  · subst r
    simp only [releasedOrdinaryData2, ordinaryRegionDist, ordinaryAlphaDist,
      RatDist.prob, if_true, Nat.cast_one, div_one]
    rw [ordinary_alpha_num_complement]
    push_cast
    field_simp [hD]
    ring
  · simp [releasedOrdinaryData2, ordinaryRegionDist, RatDist.prob, hr]

def OrdinaryPairNumeratorOK : Prop :=
  ∀ x : ConstituentTerm releasedParent,
    0 < coord .X x.2.2.1 → 0 < coord .Y x.2.2.1 → 0 < coord .Z x.2.2.1 →
    ∀ (W : Side) (sigma : Chunk 2),
      (releasedConstituentSpec.betaChild W x.1 x.2.1 x.2.2).num sigma =
        ∑ u : OrdinaryChild x.2.2.1,
          (if coord (ordinaryLargeSide x.2.2.1) u.1 = 1
            then ordinaryD / 2 -
              (OmegaBound.ADVXXZT6SplitTargetData.targetNode
                (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
                  x.2.1 x.1 x.2.2.1)).muNum
            else (OmegaBound.ADVXXZT6SplitTargetData.targetNode
              (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
                x.2.1 x.1 x.2.2.1)).muNum) *
          (if (@leftHalf 1 sigma 0).val = coord W u.1 then 1 else 0) *
          (if (@rightHalf 1 sigma 0).val = coord W x.2.2.1 - coord W u.1 then 1 else 0)

end OmegaBound.ADVXXZGeneral
