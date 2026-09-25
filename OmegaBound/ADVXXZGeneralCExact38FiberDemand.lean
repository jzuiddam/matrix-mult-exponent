import OmegaBound.ADVXXZGeneralCExact38TargetOrbitCount

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Parent25 incident target labels are exactly the owner's physical-side target fibre. -/
theorem stageIncidentLabels_card_eq_fiber38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which)) :
    (pqIncidentLabels38 p d r which a.val).card =
      (stageRoleTargetFiber38 q p d r (Parent25.side d r which) j.val).card := by
  classical
  have hinc : (stagePopulationAt q p d b m r).incidence
      (Parent25.side d r which) j.val a.val := by
    simpa only [exactPartsAt, Finset.mem_filter, Finset.mem_univ, true_and] using a.property
  have howner : Parent25.contains p d b m r which j.val a.val := by
    simpa only [Parent25.contains, Parent25.side] using hinc.1
  unfold pqIncidentLabels38 stageRoleTargetFiber38
  refine Finset.card_bij' (fun J _ => J.val) (fun k hk =>
    ⟨k, (Finset.mem_filter.mp hk).1⟩) ?_ ?_ ?_ ?_
  · intro J hJ
    have hcontains := (Finset.mem_filter.mp hJ).2
    have hcoarseRole := stageRoleCoarse_eq_of_contains38 q p d r which
      J.val j.val a.val hcontains howner
    have hcoarse : (stagePopulationAt q p d b m r).coarse J.val
        (Parent25.side d r which) =
      (stagePopulationAt q p d b m r).coarse j.val
        (Parent25.side d r which) := by
      simpa only [rolePopulation, Parent25.side] using hcoarseRole
    exact Finset.mem_filter.mpr ⟨J.property, hcoarse⟩
  · intro k hk
    have hktarget := (Finset.mem_filter.mp hk).1
    have hkcoarse := (Finset.mem_filter.mp hk).2
    have hkrole :
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse k
            (if which = 0 then .Y else .Z) =
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j.val
            (if which = 0 then .Y else .Z) := by
      simpa only [rolePopulation, Parent25.side] using hkcoarse
    have hkcoords := (stage_role_coarse_eq_iff_coords38 q p d r k j.val
      (if which = 0 then .Y else .Z)).1 hkrole
    have hkcontains : Parent25.contains p d b m r which k a.val := by
      intro z
      exact (howner z).trans (hkcoords z).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkcontains⟩
  · intro J _
    rfl
  · intro k hk
    apply Subtype.ext
    rfl

/-- The literal Y/Z term of constituent `natural_demand` dominates its stage quotient. -/
theorem stageDemand_role_ceiling_le38 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (floor : ℕ) (epsilon : ℚ) (r : Fin 6) (which : Fin 2) :
    Nat.ceil ((((cLength p b m) ^ 2 : ℕ) : ℝ) *
      (stagePopulationAt 0 p d b m r).target.card *
      Parent25.pcompMax p d b epsilon m r which /
      (stageRoleCoarseImage38 (b := b) (m := m) 0 p d r
        (Parent25.side d r which)).card) ≤
      stageDemand25 p d b floor epsilon m r := by
  classical
  let P := stagePopulationAt 0 p d b m r
  let NX := ((Finset.univ : Finset P.Label).image fun k =>
    P.coarse k (d.perm r .X)).card
  let NY := ((Finset.univ : Finset P.Label).image fun k =>
    P.coarse k (d.perm r .Y)).card
  let NZ := ((Finset.univ : Finset P.Label).image fun k =>
    P.coarse k (d.perm r .Z)).card
  fin_cases which
  · unfold stageDemand25 natural_demand
    dsimp only
    change Nat.ceil ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
      Parent25.pcompMax p d b epsilon m r 0 / NY) ≤
        max (max floor (2 * (w + w) + 3))
          (max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX))
            (max (if NY = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 0 / NY))
              (if NZ = 0 then 0 else Nat.ceil
                ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                  Parent25.pcompMax p d b epsilon m r 1 / NZ))))
    by_cases hNY : NY = 0
    · simp [hNY]
    · calc
        _ = if NY = 0 then 0 else Nat.ceil
            ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
              Parent25.pcompMax p d b epsilon m r 0 / NY) := by simp [hNY]
        _ ≤ max (if NY = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 0 / NY))
            (if NZ = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 1 / NZ)) := le_max_left _ _
        _ ≤ max (if NX = 0 then 0 else Nat.ceil
            (8 * (Fintype.card P.Label : ℝ) / NX)) _ := le_max_right _ _
        _ ≤ max (max floor (2 * (w + w) + 3)) _ := le_max_right _ _
  · unfold stageDemand25 natural_demand
    dsimp only
    change Nat.ceil ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
      Parent25.pcompMax p d b epsilon m r 1 / NZ) ≤
        max (max floor (2 * (w + w) + 3))
          (max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX))
            (max (if NY = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 0 / NY))
              (if NZ = 0 then 0 else Nat.ceil
                ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                  Parent25.pcompMax p d b epsilon m r 1 / NZ))))
    by_cases hNZ : NZ = 0
    · simp [hNZ]
    · calc
        _ = if NZ = 0 then 0 else Nat.ceil
            ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
              Parent25.pcompMax p d b epsilon m r 1 / NZ) := by simp [hNZ]
        _ ≤ max (if NY = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 0 / NY))
            (if NZ = 0 then 0 else Nat.ceil
              ((((cLength p b m) ^ 2 : ℕ) : ℝ) * P.target.card *
                Parent25.pcompMax p d b epsilon m r 1 / NZ)) := le_max_right _ _
        _ ≤ max (if NX = 0 then 0 else Nat.ceil
            (8 * (Fintype.card P.Label : ℝ) / NX)) _ := le_max_right _ _
        _ ≤ max (max floor (2 * (w + w) + 3)) _ := le_max_right _ _

end
end OmegaBound.ADVXXZGeneral
