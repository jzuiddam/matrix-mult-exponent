import OmegaBound.ADVXXZGeneralCExact36Boundary

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem goodBrokenFamily_restricts_input36 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (hε : 0 ≤ ε)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q p d b m r) (M r))
    (J : (r : Fin 6) → Finset (stagePopulationAt q p d b m r).Label)
    (hJ : ∀ r j, j ∈ J r →
      stageGood25 q p d b ε m r (M r) (B r) (ω r) j) :
    Restricts (goodBrokenFamilyZ25 q p d b ε m M B ω J).tensor
      (constituentInputZ q p (b*m) ε).tensor := by
  classical
  have hmono : Restricts (goodBrokenFamilyZ25 q p d b ε m M B ω J).tensor
      (brokenFamilyTensorZ25 q p d b ε m M B ω).tensor :=
    goodBrokenFamily_mono33 q p d b ε m M B ω J
      (fun r => selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
        (M r) (B r) (ω r))
      (fun r j hj => (hJ r j hj).1)
  obtain ⟨eX, eY, eZ, _, _, _, hcoef⟩ :=
    active_embeddings_integral36 q m p d hd hb ε M B ω
  have hemb : Restricts (brokenFamilyTensorZ25 q p d b ε m M B ω).tensor
      (regionalInputZ q p d (b*m) ε).tensor :=
    ADVXXZ.restricts_of_sub eX eY eZ (fun x y z => (hcoef x y z).symm)
  exact Tensor3.Restricts.trans hmono
    (Tensor3.Restricts.trans hemb
      (constituent_partition_integral36 q w s b m p d hd hb ε hε))

theorem constituent_grid_production_of_selection36
    (q : ℕ) {w s b : ℕ} (hq : 0 < q) {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (ε : ℚ) (hε : 0 ≤ ε)
    (m : ℕ) (h : ConstituentFullGrid27 d m ε)
    (hboundary : ConstituentGridBoundary28 h.val)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q
      (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m r) (M r))
    (hvalid : ValidStageHashes (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m M B)
    (J : (r : Fin 6) → Finset (stagePopulationAt q
      (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m r).Label)
    (hJ : ∀ r j, j ∈ J r →
      stageGood25 q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b ε m r (M r) (B r) (ω r) j) :
    ∃ P : ConstituentGridProduction29 q d hd ε m h.val, P.selected = J := by
  classical
  let pg := constituentGridParent27 d hd m h.val
  let dg := constituentGridSpec27 d hd m h.val
  have hdg : ConstituentAdmissibleAt dg b :=
    constituent_grid_admissible28 d b m hd h.val hboundary
  have hbg : ConstituentIntegral36 dg b m :=
    constituent_grid_integral36 d hd hb m h.val
  have hsource : Restricts
      (goodBrokenFamilyZ25 q pg dg b ε m M B ω J).tensor
      (constituentInputZ q pg (b*m) ε).tensor :=
    goodBrokenFamily_restricts_input36 q m pg dg hdg hbg ε hε M B ω J hJ
  have hrep : Restricts
      (copiesZ (stageRepairedCount q pg dg b ε m M B ω J)
        (constituentOutputZ q dg m 0)).tensor
      (goodBrokenFamilyZ25 q pg dg b ε m M B ω J).tensor :=
    repair_fibres_integral36 q m hq pg dg hdg hbg ε M B ω J hJ hvalid
  have hcop : Restricts
      (copiesZ (stageRepairedCount q pg dg b ε m M B ω J)
        (constituentGridTensorZ27 q d m h.val)).tensor
      (copiesZ (stageRepairedCount q pg dg b ε m M B ω J)
        (constituentOutputZ q dg m 0)).tensor :=
    copiesZ_restricts33 _ _ _
      (constituent_grid_output_restricts36 q d hd m h.val)
  have hrepair : Restricts
      (copiesZ (stageRepairedCount q pg dg b ε m M B ω J)
        (constituentGridTensorZ27 q d m h.val)).tensor
      (goodBrokenFamilyZ25 q pg dg b ε m M B ω J).tensor :=
    Tensor3.Restricts.trans hcop hrep
  have hpoly : Restricts
      (copiesZ (stageRepairedCount q pg dg b ε m M B ω J)
        (constituentGridTensorZ27 q d m h.val)).tensor
      (constituentPlainInputZ q p (b*m) (3*ε)).tensor :=
    Tensor3.Restricts.trans hrepair
      (Tensor3.Restricts.trans hsource
        (constituent_grid_input_window36 q d hd ε hε m h))
  refine ⟨{ modulus := M
            bucketSet := B
            outcome := ω
            selected := J
            valid := hvalid
            good := hJ
            regionalCopies := fun r =>
              if (stagePopulationAt q pg dg b m r).n = 0 then 1 else
                (J r).card / repairReserve (stagePopulationAt q pg dg b m r).n
                  (fun W => (J r).sup
                    (fun j => (exactPartsAt q b m pg dg r j W).card))
            regionalCopies_eq := fun r => rfl
            copies := stageRepairedCount q pg dg b ε m M B ω J
            copies_eq := rfl
            source_to_broken := hsource
            repair := hrepair
            degree := 0
            polynomial := polyDegeneratesAt_of_restricts hpoly }, rfl⟩

/-- The reassembly: the boundary-incompatible case remains in the pool as
an identically-zero grid tensor; every compatible grid with a supplied valid good
selection produces the production record `ConstituentGridProduction29`. -/
theorem constituent_grid_production_or_zero36
    (q : ℕ) {w s b : ℕ} (hq : 0 < q) {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (ε : ℚ) (hε : 0 ≤ ε)
    (m : ℕ) (h : ConstituentFullGrid27 d m ε)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r)))
    (ω : (r : Fin 6) → HashOutcome (stagePopulationAt q
      (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m r) (M r))
    (hvalid : ValidStageHashes (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m M B)
    (J : (r : Fin 6) → Finset (stagePopulationAt q
      (constituentGridParent27 d hd m h.val)
      (constituentGridSpec27 d hd m h.val) b m r).Label)
    (hJ : ∀ r j, j ∈ J r →
      stageGood25 q (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) b ε m r (M r) (B r) (ω r) j) :
    (constituentGridTensorZ27 q d m h.val).tensor = 0 ∨
      ∃ P : ConstituentGridProduction29 q d hd ε m h.val, P.selected = J := by
  rcases constituent_grid_boundary_or_zero28 q d m h.val with hboundary | hzero
  · exact Or.inr (constituent_grid_production_of_selection36 q hq d hd hb ε hε
      m h hboundary M B ω hvalid J hJ)
  · exact Or.inl hzero

#print axioms goodBrokenFamily_restricts_input36
#print axioms constituent_grid_production_of_selection36
#print axioms constituent_grid_production_or_zero36

end OmegaBound.ADVXXZGeneral
