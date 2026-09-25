import OmegaBound.ADVXXZGeneralPopulationFiniteAPI
import OmegaBound.ADVXXZGeneralPopulationConstructorsV21
import OmegaBound.ADVXXZGeneralAmend25Tensor

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/--
The role-transported raw population.
Paper clauses: `P/constituent.tex:173-221` and `P/global.tex:131-184`.
-/
def rolePopulation (P : RawPopulation) (roles : Side → Side) : RawPopulation :=
  { P with coarse := fun j W => P.coarse j (roles W)
           Part := fun W => P.Part (roles W)
           partFinite := fun W => P.partFinite (roles W)
           fine := fun W => P.fine (roles W)
           incidence := fun W => P.incidence (roles W) }

/--
The three-term-progression-free hash guard.
Paper clauses: `P/constituent.tex:195-205` and `P/global.tex:158-184`.
-/
def HashAPFree {M : ℕ} (B : Finset (ZMod M)) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a + c = 2*b → a = b ∧ c = b

/--
The constituent hash-validity predicate.
Paper clause: `P/constituent.tex:195-205`.
-/
def ValidStageHashes {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (M : Fin 6 → ℕ)
    (B : (r : Fin 6) → Finset (ZMod (M r))) : Prop :=
  ∀ r, Nat.Prime (M r) ∧ 2 < M r ∧
    (stagePopulationAt 0 p d b m r).grade < M r ∧ HashAPFree (B r)

/--
The global hash-validity predicate.
Paper clause: `P/global.tex:158-184`.
-/
def ValidGlobalHashes {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n)
    (M : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (M r))) : Prop :=
  ∀ r, Nat.Prime (M r) ∧ 2 < M r ∧
    (globalPopulation g n ξ r).grade < M r ∧ HashAPFree (B r)

/--
The physical containment test.
Paper clause: `P/global.tex:381-397`.
-/
noncomputable def globalCoarseContains {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Side)
    (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W) : Prop :=
  ∀ i, chunkLvl (a i) = coord W (j.val i)

/--
The actual global cell count.
Paper clause: `P/global.tex:202-206`.
-/
noncomputable def globalCellCount {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Side)
    (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part W)
    (cell : Shape w → Prop) (σ : Chunk w) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => cell (j.val i) ∧ a i = σ).card

/--
The global Y/Z actual-cell compatibility predicate. Paper clauses: `P/global.tex:220-227,329-334`.
-/
noncomputable def globalCompatible {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : (globalPopulation g n ξ r).Label)
    (a : (globalPopulation g n ξ r).Part
      (g.perm r (if which = 0 then .Y else .Z))) : Prop :=
  let X := g.perm r .X
  let Y := g.perm r .Y
  let Z := g.perm r .Z
  let W := if which = 0 then Y else Z
  (∀ u : Shape w,
    (if which = 0 then coord Z u = 0 else coord X u = 0 ∨ coord Y u = 0) →
      ∀ σ, globalCellCount g n ξ r W j a (fun v => v = u) σ = ξ.count W r u σ) ∧
  ∀ k : Fin (2*w+1), ∀ σ,
    globalCellCount g n ξ r W j a (fun u => coord W u = k.val) σ =
      ∑ u : Shape w, if coord W u = k.val then ξ.count W r u σ else 0

/--
The global raw label/fine-word sample space.
Paper clause: `P/global.tex:381-397`.
-/
noncomputable def GlobalLawSample {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) :=
  {j : (globalPopulation g n ξ r).Label // j ∈ (globalPopulation g n ξ r).target} ×
    (globalPopulation g n ξ r).Part (g.perm r (if which = 0 then .Y else .Z))

/--
The finite instance for the sample space.
Paper clause: `P/global.tex:381-397`.
-/
noncomputable instance globalLawSampleFintype {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    Fintype (GlobalLawSample g n ξ r which) := by
  classical
  unfold GlobalLawSample
  infer_instance

/--
The raw empirical global split law.
Paper clause: `P/global.tex:381-397`.
-/
noncomputable def globalEmpiricalLaw {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (W : Side)
    (a : (globalPopulation g n ξ r).Part W) : Chunk w → ℕ :=
  fun σ => typeCnt a σ

/--
The containing global samples.
Paper clause: `P/global.tex:394-397`.
-/
noncomputable def globalContainingSamples {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    Finset (GlobalLawSample g n ξ r which) := by
  classical
  exact Finset.univ.filter fun z =>
    globalCoarseContains g n ξ r (g.perm r (if which = 0 then .Y else .Z)) z.1.val z.2

/--
The represented empirical-law image.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalLawFinset {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) : Finset (Chunk w → ℕ) := by
  classical
  let W := g.perm r (if which = 0 then .Y else .Z)
  exact ((globalContainingSamples g n ξ r which).image fun z =>
    globalEmpiricalLaw g n ξ r W z.2).filter fun law =>
      ∀ σ, law σ = ∑ u : Shape w, ξ.count W r u σ

/--
The global represented-law subtype.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable def GlobalRepresentedLaw {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) :=
  {law : Chunk w → ℕ // law ∈ globalLawFinset g n ξ r which}

/--
The finite represented-law instance.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable instance globalRepresentedLawFintype {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    Fintype (GlobalRepresentedLaw g n ξ r which) := by
  classical
  unfold GlobalRepresentedLaw
  infer_instance

/--
The fibre of samples representing a law.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalLawSamples {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r which) :
    Finset (GlobalLawSample g n ξ r which) := by
  classical
  exact (globalContainingSamples g n ξ r which).filter fun z =>
    globalEmpiricalLaw g n ξ r (g.perm r (if which = 0 then .Y else .Z)) z.2 = β.val

/--
The global raw joint-P sample fraction.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalJointP {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r which) : ℝ :=
  ((globalLawSamples g n ξ r which β).card : ℝ) /
    (Fintype.card (GlobalLawSample g n ξ r which) : ℝ)

/--
The compatible global raw joint-Q sample fraction. Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalJointQ {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r which) : ℝ := by
  classical
  exact (((globalLawSamples g n ξ r which β).filter fun z =>
    globalCompatible g n ξ r which z.1.val z.2).card : ℝ) /
      (Fintype.card (GlobalLawSample g n ξ r which) : ℝ)

/--
The first representative of a represented law.
Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalFirstLawSample {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r which) : GlobalLawSample g n ξ r which := by
  classical
  let candidates := globalLawSamples g n ξ r which β
  have hcandidates : candidates.Nonempty := by
    have hmem := (Finset.mem_filter.mp β.property).1
    rcases Finset.mem_image.mp hmem with ⟨z, hz, heq⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩
  let e := Fintype.equivFin (GlobalLawSample g n ξ r which)
  letI := LinearOrder.lift' e e.injective
  exact candidates.min' hcandidates

/--
The representative-based global conditional compatibility ratio. Paper clause: `P/global.tex:394-400`.
-/
noncomputable def globalPcomp {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (β : GlobalRepresentedLaw g n ξ r which) : ℝ := by
  classical
  let a := (globalFirstLawSample g n ξ r which β).2
  let W := g.perm r (if which = 0 then .Y else .Z)
  let containing := (globalPopulation g n ξ r).target.filter fun j =>
    globalCoarseContains g n ξ r W j a
  exact ((containing.filter fun j => globalCompatible g n ξ r which j a).card : ℝ) /
    (containing.card : ℝ)

end OmegaBound.ADVXXZGeneral
end

