import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalGlobal
import OmegaBound.ADVXXZGeneralInventoryEnum
import OmegaBound.ADVXXZG2Mix

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

noncomputable def physicalTopPair (p : Fin 126) : Fin 6 × Shape 4 :=
  (OmegaBound.ADVXXZT2.parRegion p.val, parentShape releasedParent p)

/-- The released positive parent address is its physical region and physical row. -/
def physicalTopAddress (p : Fin 126) : Fin 6 × Fin 45 :=
  (OmegaBound.ADVXXZT2.parRegion p.val, OmegaBound.ADVXXZT2.parRow p.val)

theorem physical_top_address_injective : Function.Injective physicalTopAddress := by
  decide +kernel

theorem physical_top_parent_row (p : Fin 126) :
    OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex (parentShape releasedParent p) =
      OmegaBound.ADVXXZT2.parRow p.val := by
  revert p
  decide +kernel

theorem physical_top_pair_injective : Function.Injective physicalTopPair := by
  intro p q h
  apply physical_top_address_injective
  apply Prod.ext
  · change OmegaBound.ADVXXZT2.parRegion p.val =
      OmegaBound.ADVXXZT2.parRegion q.val
    exact congrArg Prod.fst h
  · change OmegaBound.ADVXXZT2.parRow p.val = OmegaBound.ADVXXZT2.parRow q.val
    rw [← physical_top_parent_row p, ← physical_top_parent_row q]
    exact congrArg
      (fun ru : Fin 6 × Shape 4 =>
        OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex ru.2) h

def PhysicalTopInterior (ru : Fin 6 × Shape 4) : Prop :=
  0 < coord .X ru.2 ∧ 0 < coord .Y ru.2 ∧ 0 < coord .Z ru.2

instance instDecidablePhysicalTopInterior (ru : Fin 6 × Shape 4) :
    Decidable (PhysicalTopInterior ru) := by
  unfold PhysicalTopInterior
  infer_instance

theorem physical_top_pair_interior (p : Fin 126) :
    PhysicalTopInterior (physicalTopPair p) := by
  exact ⟨releasedParent.i_pos p, releasedParent.j_pos p, releasedParent.k_pos p⟩

noncomputable def physicalTopInteriorMap (p : Fin 126) :
    {ru : Fin 6 × Shape 4 // PhysicalTopInterior ru} :=
  ⟨physicalTopPair p, physical_top_pair_interior p⟩

theorem physical_top_interior_card :
    Fintype.card {ru : Fin 6 × Shape 4 // PhysicalTopInterior ru} = 126 := by
  decide +kernel

theorem physical_top_interior_bijective : Function.Bijective physicalTopInteriorMap := by
  apply (Fintype.bijective_iff_injective_and_card physicalTopInteriorMap).2
  refine ⟨?_, by simpa using physical_top_interior_card.symm⟩
  intro p q h
  apply physical_top_pair_injective
  exact congrArg Subtype.val h


theorem physical_top_beta_parent (W : Side) (p : Fin 126) :
    physicalGlobalSpec.beta W (OmegaBound.ADVXXZT2.parRegion p.val)
      (parentShape releasedParent p) = releasedParent.beta W p := by
  simp only [physicalGlobalSpec, physicalGlobalBeta, physical_top_parent_row]
  cases W <;> rfl

theorem physical_top_joint_num (p : Fin 126) :
    physicalGlobalSpec.joint.num (physicalTopPair p) = releasedParent.baseN p := by
  change
    OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist.num
        (OmegaBound.ADVXXZT2.parRegion p.val) *
      (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist
        (OmegaBound.ADVXXZT2.parRegion p.val)).num (parentShape releasedParent p) =
    OmegaBound.ADVXXZT6Selection.parentMass p
  rw [← OmegaBound.ADVXXZG1.alphaIdx_eq_shapeDist]
  rw [physical_top_parent_row]
  unfold OmegaBound.ADVXXZT6Selection.parentMass OmegaBound.ADVXXZG1.aw
  rw [OmegaBound.ADVXXZT2.physRow_logRow]

theorem physical_top_joint_prob_pos (p : Fin 126) :
    0 < physicalGlobalSpec.joint.prob (physicalTopPair p) := by
  rw [RatDist.prob]
  exact div_pos (by
    rw [physical_top_joint_num]
    exact_mod_cast releasedParent.baseN_pos p) (by
      exact_mod_cast physicalGlobalSpec.joint.den_pos)

def PhysicalTopActive (ru : Fin 6 × Shape 4) : Prop :=
  0 < ((releasedOrdinaryCertificatePhysical.D : ℚ) ^ 4) *
      physicalGlobalSpec.joint.prob ru ∧ PhysicalTopInterior ru

noncomputable instance instDecidablePhysicalTopActive (ru : Fin 6 × Shape 4) :
    Decidable (PhysicalTopActive ru) := by
  classical
  unfold PhysicalTopActive
  infer_instance

theorem physical_top_pair_active (p : Fin 126) : PhysicalTopActive (physicalTopPair p) := by
  refine ⟨mul_pos ?_ (physical_top_joint_prob_pos p), physical_top_pair_interior p⟩
  exact pow_pos (by exact_mod_cast (show 0 < releasedOrdinaryCertificatePhysical.D by
    change 0 < ordinaryD ^ 2
    decide +kernel)) _

noncomputable def physicalTopActiveMap (p : Fin 126) :
    {ru : Fin 6 × Shape 4 // PhysicalTopActive ru} :=
  ⟨physicalTopPair p, physical_top_pair_active p⟩

theorem physical_top_active_bijective : Function.Bijective physicalTopActiveMap := by
  refine ⟨?_, ?_⟩
  · intro p q h
    apply physical_top_pair_injective
    exact congrArg Subtype.val h
  · intro ru
    obtain ⟨p, hp⟩ := physical_top_interior_bijective.2 ⟨ru.1, ru.2.2⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    change physicalTopPair p = ru.1
    exact congrArg Subtype.val hp

noncomputable def physicalTopActiveEquiv :
    Fin 126 ≃ {ru : Fin 6 × Shape 4 // PhysicalTopActive ru} :=
  Equiv.ofBijective physicalTopActiveMap physical_top_active_bijective

noncomputable def physicalGlobalScaledEntry (ru : Fin 6 × Shape 4) : ℚ × AtomKey :=
  (((releasedOrdinaryCertificatePhysical.D : ℚ) ^ 4) *
      physicalGlobalSpec.joint.prob ru,
    ⟨4, ru.2, fun W sigma => (physicalGlobalSpec.beta W ru.1 ru.2).prob sigma⟩)

noncomputable def physicalTopParentEntry (p : Fin 126) : ℚ × AtomKey :=
  (((releasedOrdinaryCertificatePhysical.D : ℚ) ^ 2) *
      releasedOrdinaryStep3.input.baseN p,
    ⟨4, parentShape releasedOrdinaryStep3.input p,
      fun W sigma => (releasedOrdinaryStep3.input.beta W p).prob sigma⟩)

theorem physical_top_entry_eq (p : Fin 126) :
    physicalGlobalScaledEntry (physicalTopPair p) = physicalTopParentEntry p := by
  apply Prod.ext
  · rw [physicalGlobalScaledEntry, physicalTopParentEntry, RatDist.prob,
      physical_top_joint_num]
    change
      (((ordinaryD ^ 2 : ℕ) : ℚ) ^ 4) *
          ((releasedParent.baseN p : ℚ) / ((ordinaryD ^ 2 : ℕ) : ℚ)) =
        (((ordinaryD ^ 2 : ℕ) : ℚ) ^ 2) *
          ((ordinaryD ^ 2 * releasedParent.baseN p : ℕ) : ℚ)
    have hD : (ordinaryD : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0 < ordinaryD by decide +kernel))
    push_cast
    field_simp [hD]
  · change
      (⟨4, parentShape releasedParent p,
        fun W sigma =>
          (physicalGlobalSpec.beta W (OmegaBound.ADVXXZT2.parRegion p.val)
            (parentShape releasedParent p)).prob sigma⟩ : AtomKey) =
      ⟨4, parentShape releasedParent p,
        fun W sigma => (releasedParent.beta W p).prob sigma⟩
    congr 1
    apply Prod.ext
    · rfl
    · funext W sigma
      change
        (physicalGlobalSpec.beta W (OmegaBound.ADVXXZT2.parRegion p.val)
          (parentShape releasedParent p)).prob sigma =
        (releasedParent.beta W p).prob sigma
      rw [physical_top_beta_parent]

end OmegaBound.ADVXXZGeneral
