import OmegaBound.ADVXXZGeneralReleasedOrdinaryPair
import OmegaBound.ADVXXZT6Round82Clauses

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
namespace OmegaBound.ADVXXZGeneral

private theorem stage3_prob_cast {ι : Type*} [Fintype ι] (P : RatDist ι) (i : ι) :
    ((P.prob i : ℚ) : ℝ) = P.probR i := by
  simp [RatDist.prob, RatDist.probR]

private theorem stage3_probR_ne_zero {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) (h : P.num i ≠ 0) : P.probR i ≠ 0 := by
  unfold RatDist.probR
  apply div_ne_zero
  · exact_mod_cast h
  · exact P.denR_ne_zero

private theorem childRowEquiv_apply (t : Fin 126) (u : ChildShape releasedParent t) :
    OmegaBound.ADVXXZT6Round78.childRowEquiv t u =
      OmegaBound.ADVXXZT6Round78.childIndex t u := rfl

theorem released_ordinary_stage3_roles :
    EnumeratesPermutations releasedConstituentSpec.perm :=
  releasedPerm_enumerates

theorem released_ordinary_stage3_pair_mixture (W : Side) (t : Fin 126)
    (r : Fin 6) (sigma : Chunk 4) :
    (releasedConstituentSpec.betaRegion W t r).prob sigma =
      ∑ u, (releasedConstituentSpec.alpha t r).prob u *
        (releasedConstituentSpec.betaChild W t r u).prob (leftHalf sigma) *
        (releasedConstituentSpec.betaChild W t r
          (complement releasedParent t u)).prob (rightHalf sigma) := by
  apply (Rat.cast_injective : Function.Injective ((↑·) : ℚ → ℝ))
  simp only [Rat.cast_sum, Rat.cast_mul, stage3_prob_cast]
  simpa only [releasedConstituentSpec, releasedParent,
    OmegaBound.ADVXXZCertificateGlobalData.RatDist.reindex_probR,
    OmegaBound.ADVXXZT6Round78.childRowEquiv,
    OmegaBound.ADVXXZPaper.pairProb, mul_assoc] using
      OmegaBound.ADVXXZT6Round82.certificatePairedDisintegration W t r sigma

theorem released_ordinary_stage3_child_support (W : Side) (t : Fin 126)
    (r : Fin 6) (u : ChildShape releasedParent t) :
    Supported (releasedConstituentSpec.betaChild W t r u) (coord W u.1) := by
  change Supported (OmegaBound.ADVXXZT6Round82.certificateBetaChild W t r u)
    (coord W u.1)
  intro sigma hsigma
  apply OmegaBound.ADVXXZT6Round82.certificateBetaChild_supported W t r u sigma
  apply stage3_probR_ne_zero
  exact hsigma

private theorem num_ne_zero_of_prob_ne_zero {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) (h : P.prob i ≠ 0) : P.num i ≠ 0 := by
  intro hzero
  apply h
  simp [RatDist.prob, hzero]

theorem released_ordinary_stage3_regional_support (W : Side) (t : Fin 126)
    (r : Fin 6) :
    Supported (releasedConstituentSpec.betaRegion W t r)
      (match W with
       | .X => releasedParent.i t
       | .Y => releasedParent.j t
       | .Z => releasedParent.k t) := by
  intro sigma hnum
  have hprob : (releasedConstituentSpec.betaRegion W t r).prob sigma ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hnum)
      (releasedConstituentSpec.betaRegion W t r).den_ne_zero
  have hsum : (∑ u, (releasedConstituentSpec.alpha t r).prob u *
      (releasedConstituentSpec.betaChild W t r u).prob (leftHalf sigma) *
      (releasedConstituentSpec.betaChild W t r
        (complement releasedParent t u)).prob (rightHalf sigma)) ≠ 0 := by
    rw [← released_ordinary_stage3_pair_mixture]
    exact hprob
  have hex : ∃ u : ChildShape releasedParent t,
      (releasedConstituentSpec.alpha t r).prob u *
        (releasedConstituentSpec.betaChild W t r u).prob (leftHalf sigma) *
        (releasedConstituentSpec.betaChild W t r
          (complement releasedParent t u)).prob (rightHalf sigma) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hsum
    exact Finset.sum_eq_zero fun u _ => hall u
  obtain ⟨u, hu⟩ := hex
  have hleftProb :
      (releasedConstituentSpec.betaChild W t r u).prob (leftHalf sigma) ≠ 0 := by
    intro hz
    apply hu
    rw [hz]
    ring
  have hrightProb :
      (releasedConstituentSpec.betaChild W t r
        (complement releasedParent t u)).prob (rightHalf sigma) ≠ 0 := by
    intro hz
    apply hu
    rw [hz]
    ring
  have hleft := released_ordinary_stage3_child_support W t r u (leftHalf sigma)
    (num_ne_zero_of_prob_ne_zero _ _ hleftProb)
  have hright := released_ordinary_stage3_child_support W t r
    (complement releasedParent t u) (rightHalf sigma)
    (num_ne_zero_of_prob_ne_zero _ _ hrightProb)
  have hsplit : chunkLvl sigma = chunkLvl (leftHalf sigma) + chunkLvl (rightHalf sigma) := by
    simpa [leftHalf, rightHalf] using (OmegaBound.ADVXXZ.chunkLvl_eq_add sigma)
  rw [hsplit, hleft, hright]
  cases W
  · change coord .X u.1 + (releasedParent.i t - coord .X u.1) = releasedParent.i t
    exact Nat.add_sub_of_le u.2.1
  · change coord .Y u.1 + (releasedParent.j t - coord .Y u.1) = releasedParent.j t
    exact Nat.add_sub_of_le u.2.2.1
  · change coord .Z u.1 + (releasedParent.k t - coord .Z u.1) = releasedParent.k t
    exact Nat.add_sub_of_le u.2.2.2

theorem released_ordinary_stage3_out_eq (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedParent t) :
    (releasedConstituentSpec.outBase ⟨t, r, u⟩ : ℚ) =
      ((ordinaryD ^ 2 : ℕ) : ℚ) * releasedParent.baseN t *
        (releasedConstituentSpec.A t).prob r *
        ((releasedConstituentSpec.alpha t r).prob u +
          (releasedConstituentSpec.alpha t r).prob (complement releasedParent t u)) := by
  apply (Rat.cast_injective : Function.Injective ((↑·) : ℚ → ℝ))
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, stage3_prob_cast]
  have h := OmegaBound.ADVXXZT6Round82.released_output_parameters
    (show ConstituentTerm OmegaBound.ADVXXZT9R16PositiveParents.releasedPositiveInput from
      ⟨t, r, u⟩)
  rw [show OmegaBound.ADVXXZCertificateConstituentClosure.correctedWeightDen =
    ordinaryD ^ 2 by rfl] at h
  rw [OmegaBound.ADVXXZPaper.symWeight_eq_add_complement] at h
  simp only [releasedConstituentSpec, releasedParent,
    OmegaBound.ADVXXZCertificateGlobalData.RatDist.reindex_probR,
    childRowEquiv_apply]
  simp only [OmegaBound.ADVXXZT6Round82.releasedCorrectedData] at h
  push_cast at h ⊢
  ring_nf at h ⊢
  simpa only [
    OmegaBound.ADVXXZT6Round82.releasedCorrectedData,
    OmegaBound.ADVXXZT6Round78.childRowEquiv, childRowEquiv_apply] using h

end OmegaBound.ADVXXZGeneral
