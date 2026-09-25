import OmegaBound.ADVXXZGeneralGlobalExactGoodFamily

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

/-- Public names for the affine coordinates hidden inside the finite hashing API. -/
def hashZero27 {P : RawPopulation} {M : ℕ} (omega : HashOutcome P M) : ZMod M :=
  omega ⟨0, by omega⟩

def hashOne27 {P : RawPopulation} {M : ℕ} (omega : HashOutcome P M) : ZMod M :=
  omega ⟨1, by omega⟩

def hashWeight27 {P : RawPopulation} {M : ℕ}
    (omega : HashOutcome P M) (i : Fin P.n) : ZMod M :=
  omega ⟨i.val + 2, by omega⟩

def hashX27 (P : RawPopulation) (M : ℕ) (omega : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  hashZero27 omega + ∑ i, (P.coarse j .X i).val * hashWeight27 omega i

def hashY27 (P : RawPopulation) (M : ℕ) (omega : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  hashZero27 omega + hashOne27 omega +
    ∑ i, (P.coarse j .Y i).val * hashWeight27 omega i

noncomputable def hashZ27 (P : RawPopulation) (M : ℕ) (omega : HashOutcome P M)
    (j : P.Label) : ZMod M :=
  hashZero27 omega + Ring.inverse 2 *
    (hashOne27 omega +
      ∑ i, (P.grade - (P.coarse j .Z i).val) * hashWeight27 omega i)

/-- A public presentation of the private survival predicate used by `selected`. -/
def hashSurvives27 (P : RawPopulation) (M : ℕ)
    (B : Finset (ZMod M)) (omega : HashOutcome P M) (j : P.Label) : Prop :=
  hashX27 P M omega j = hashY27 P M omega j ∧
    hashY27 P M omega j = hashZ27 P M omega j ∧ hashX27 P M omega j ∈ B

theorem mem_bucket_iff_hash27 (P : RawPopulation) (M : ℕ) [NeZero M]
    (j : P.Label) (b : ZMod M) (omega : HashOutcome P M) :
    omega ∈ bucket P M j b ↔
      hashX27 P M omega j = b ∧ hashY27 P M omega j = b ∧
        hashZ27 P M omega j = b := by
  simp only [bucket, Finset.mem_filter, Finset.mem_univ, true_and]
  with_unfolding_all rfl

theorem mem_selected_iff_hashSurvives27 (P : RawPopulation) (M : ℕ) [NeZero M]
    (B : Finset (ZMod M)) (omega : HashOutcome P M) (j : P.Label) :
    j ∈ selected P M B omega ↔
      j ∈ P.target ∧ hashSurvives27 P M B omega j ∧
        ∀ k, hashSurvives27 P M B omega k → P.coarse k .X = P.coarse j .X → k = j := by
  classical
  unfold selected
  dsimp only
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hjtarget, hunique⟩
    have hjhash := (Finset.mem_filter.mp hj).2
    change hashSurvives27 P M B omega j at hjhash
    refine ⟨hjtarget, hjhash, ?_⟩
    intro k hk hcoarse
    apply hunique k
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change hashSurvives27 P M B omega k
      exact hk
    · exact hcoarse
  · rintro ⟨hjtarget, hjhash, hunique⟩
    refine ⟨?_, hjtarget, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change hashSurvives27 P M B omega j
      exact hjhash
    · intro k hk hcoarse
      apply hunique k
      · have hkhash := (Finset.mem_filter.mp hk).2
        change hashSurvives27 P M B omega k at hkhash
        exact hkhash
      · exact hcoarse

private theorem filter_card_eq_of_perm27 {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ => e i) (fun i _ => e.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (h (e.symm i)).mpr (by simpa using (Finset.mem_filter.mp hi).2)
  · intro i _
    exact e.symm_apply_apply i
  · intro i _
    exact e.apply_symm_apply i

private theorem exists_perm_of_typeCnt27
    {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (x y : Fin n → A) (h : ∀ a, typeCnt x a = typeCnt y a) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, y (e i) = x i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // x i = a} ≃ {i // y i = a}) :=
    ⟨fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), fun i => ?_⟩
  exact (e (x i) ⟨i, rfl⟩).2

set_option maxHeartbeats 1000000 in
-- The physical global-label subtype is unfolded through its dependent marginal laws.
private noncomputable def globalLabelReindex27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n)) :
    (globalPopulation g n xi r).Label ≃ (globalPopulation g n xi r).Label := by
  classical
  unfold globalPopulation at e ⊢
  dsimp only
  refine
    { toFun := fun j => ⟨fun i => j.val (e.symm i), ?_⟩
      invFun := fun j => ⟨fun i => j.val (e i), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro W a
    cases W with
    | X =>
      exact (filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.property .X a)
    | Y =>
      exact (filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.property .Y a)
    | Z =>
      exact (filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.property .Z a)
  · intro W a
    cases W with
    | X =>
      exact (filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans
        (j.property .X a)
    | Y =>
      exact (filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans
        (j.property .Y a)
    | Z =>
      exact (filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans
        (j.property .Z a)
  · intro j
    apply Subtype.ext
    funext i
    simp
  · intro j
    apply Subtype.ext
    funext i
    simp

set_option maxHeartbeats 1000000 in
-- The computation rule unfolds the preceding dependent equivalence once.
private theorem globalLabelReindex27_coarse {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (j : (globalPopulation g n xi r).Label) (W : Side) (i : Fin _) :
    (globalPopulation g n xi r).coarse (globalLabelReindex27 g xi r e j) W i =
      (globalPopulation g n xi r).coarse j W (e.symm i) := by
  classical
  unfold globalPopulation globalLabelReindex27
  rfl

private theorem globalLabel_coarse_typeCnt_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label) (W : Side)
    (a : Fin ((globalPopulation g n xi r).grade + 1)) :
    typeCnt ((globalPopulation g n xi r).coarse j W) a =
      typeCnt ((globalPopulation g n xi r).coarse k W) a := by
  classical
  unfold globalPopulation at j k ⊢
  dsimp only at j k ⊢
  exact (j.property W a).trans (k.property W a).symm

/-- Labels other than `j` which compete for its X-coarse word. -/
def hashXRivals27 (P : RawPopulation) (j : P.Label) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun k => k ≠ j ∧ P.coarse k .X = P.coarse j .X

def hashXFiber27 (P : RawPopulation) (j : P.Label) : Finset P.Label := by
  classical
  exact Finset.univ.filter fun k => P.coarse k .X = P.coarse j .X

def hashXImage27 (P : RawPopulation) : Finset (Fin P.n → Fin (P.grade + 1)) := by
  classical
  exact Finset.univ.image fun j => P.coarse j .X

/-- Uniform X fibres after transporting the global population through the region's roles. -/
theorem global_role_hashXFiber_card_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label) :
    (hashXFiber27
        (rolePopulation (globalPopulation g n xi r) (g.perm r)) j).card =
      (hashXFiber27
        (rolePopulation (globalPopulation g n xi r) (g.perm r)) k).card := by
  classical
  let P := globalPopulation g n xi r
  let W := g.perm r .X
  let RP := rolePopulation P (g.perm r)
  obtain ⟨e, he⟩ := exists_perm_of_typeCnt27 (P.coarse j W) (P.coarse k W)
    (fun a => globalLabel_coarse_typeCnt_eq27 g xi r j k W a)
  let phi : P.Label ≃ P.Label := globalLabelReindex27 g xi r e
  have hmem (l : P.Label) :
      l ∈ hashXFiber27 RP j ↔ phi l ∈ hashXFiber27 RP k := by
    simp only [hashXFiber27, Finset.mem_filter, Finset.mem_univ, true_and]
    change P.coarse l W = P.coarse j W ↔ P.coarse (phi l) W = P.coarse k W
    constructor
    · intro hl
      funext i
      rw [globalLabelReindex27_coarse g xi r e l W i, congrFun hl (e.symm i)]
      simpa using (he (e.symm i)).symm
    · intro hl
      funext i
      have hi := congrFun hl (e i)
      rw [globalLabelReindex27_coarse g xi r e l W (e i)] at hi
      have hi' := hi.trans (he i)
      rw [e.symm_apply_apply] at hi'
      exact hi'
  refine Finset.card_bij' (fun l _ => phi l) (fun l _ => phi.symm l) ?_ ?_ ?_ ?_
  · intro l hl
    exact (hmem l).1 hl
  · intro l hl
    apply (hmem (phi.symm l)).2
    simpa using hl
  · intro l _
    exact phi.symm_apply_apply l
  · intro l _
    exact phi.apply_symm_apply l

/-- The uniform role-transported X fibres partition the full raw global label space. -/
theorem global_role_hashXFiber_mul_image27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label) :
    (hashXFiber27
        (rolePopulation (globalPopulation g n xi r) (g.perm r)) j).card *
      (hashXImage27
        (rolePopulation (globalPopulation g n xi r) (g.perm r))).card =
      Fintype.card (globalPopulation g n xi r).Label := by
  classical
  let P := globalPopulation g n xi r
  let RP := rolePopulation P (g.perm r)
  have hpartition : Fintype.card RP.Label =
      ∑ x ∈ hashXImage27 RP,
        ((Finset.univ : Finset RP.Label).filter fun k => RP.coarse k .X = x).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset RP.Label))
        (t := hashXImage27 RP) (f := fun k => RP.coarse k .X)
        (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  calc
    (hashXFiber27 RP j).card * (hashXImage27 RP).card =
        ∑ _x ∈ hashXImage27 RP, (hashXFiber27 RP j).card := by simp [Nat.mul_comm]
    _ = ∑ x ∈ hashXImage27 RP,
        ((Finset.univ : Finset RP.Label).filter fun k => RP.coarse k .X = x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx
      subst x
      exact global_role_hashXFiber_card_eq27 g xi r j k
    _ = Fintype.card RP.Label := hpartition.symm

theorem hashXRivals_card_lt_fiber27 (P : RawPopulation) (j : P.Label) :
    (hashXRivals27 P j).card < (hashXFiber27 P j).card := by
  classical
  apply Finset.card_lt_card
  have hsub : hashXRivals27 P j ⊆ hashXFiber27 P j := by
    intro k hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.2⟩
  apply (Finset.ssubset_iff_of_subset hsub).2
  refine ⟨j, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · simp [hashXRivals27]

/-- The X term of `natural_demand` dominates every X-coarse rival fibre of uniform size. -/
theorem hashXRivals_le_naturalDemand27 (P : RawPopulation)
    (floor NY NZ Nalpha H : ℕ) (pY pZ : ℝ) (j : P.Label)
    (huniform : (hashXFiber27 P j).card * (hashXImage27 P).card =
      Fintype.card P.Label) :
    4 * (hashXRivals27 P j).card ≤
      natural_demand floor (Fintype.card P.Label) (hashXImage27 P).card
        NY NZ Nalpha H pY pZ := by
  classical
  let R := (hashXRivals27 P j).card
  let K := (hashXFiber27 P j).card
  let NX := (hashXImage27 P).card
  have hRlt : R < K := hashXRivals_card_lt_fiber27 P j
  have hjimage : P.coarse j .X ∈ hashXImage27 P := by
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hNX : 0 < NX := Finset.card_pos.mpr ⟨P.coarse j .X, hjimage⟩
  have hNXreal : (NX : ℝ) ≠ 0 := by exact_mod_cast hNX.ne'
  have hcardReal : (Fintype.card P.Label : ℝ) = (K : ℝ) * NX := by
    exact_mod_cast huniform.symm
  have hraw : (8 * (Fintype.card P.Label : ℝ)) / NX = (8 : ℝ) * K := by
    rw [hcardReal]
    field_simp
  have hceilReal := Nat.le_ceil ((8 * (Fintype.card P.Label : ℝ)) / NX)
  rw [hraw] at hceilReal
  have hceil : 8 * K ≤ Nat.ceil ((8 * (Fintype.card P.Label : ℝ)) / NX) := by
    rw [hraw]
    exact_mod_cast hceilReal
  calc
    4 * R ≤ 8 * K := by omega
    _ ≤ Nat.ceil ((8 * (Fintype.card P.Label : ℝ)) / NX) := hceil
    _ = if NX = 0 then 0 else
        Nat.ceil ((8 * (Fintype.card P.Label : ℝ)) / NX) := by simp [hNX.ne']
    _ ≤ max (if NX = 0 then 0 else
          Nat.ceil ((8 * (Fintype.card P.Label : ℝ)) / NX))
        (max (if NY = 0 then 0 else Nat.ceil ((H : ℝ) * Nalpha * pY / NY))
          (if NZ = 0 then 0 else Nat.ceil ((H : ℝ) * Nalpha * pZ / NZ))) :=
      le_max_left _ _
    _ ≤ natural_demand floor (Fintype.card P.Label) NX NY NZ Nalpha H pY pZ := by
      unfold natural_demand
      exact le_max_right _ _

/--
The exact affine-hash survival estimate before inserting the global fibre cardinality bound.
This is the paper's collision-union calculation, with no asymptotics or stored conclusion.
-/
theorem selected_cond_lower_of_hashXRivals27 (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : P.grade < M) (B : Finset (ZMod M))
    (j : P.Label) (hj : j ∈ P.target) (b : ZMod M) (hb : b ∈ B) :
    1 - ((hashXRivals27 P j).card : ℝ) / M ≤
      cond (bucket P M j b)
        (Finset.univ.filter fun omega => j ∈ selected P M B omega) := by
  classical
  let E := bucket P M j b
  let R := hashXRivals27 P j
  let hits : P.Label → Finset (HashOutcome P M) := fun k => bucket P M k b
  let Bad := R.biUnion hits
  let S : Finset (HashOutcome P M) :=
    Finset.univ.filter fun omega => j ∈ selected P M B omega
  have hhash := asymmetric_hash P htight hinj M hprime hodd hfloor
  have hEposNat : 0 < E.card := by
    have hout : 0 < Fintype.card (HashOutcome P M) := Fintype.card_pos
    have hprod : 0 < E.card * M ^ 2 := by
      rw [hhash.1 j b]
      exact hout
    exact Nat.pos_of_ne_zero fun hzero => by simp [hzero] at hprod
  have hE : E.Nonempty := Finset.card_pos.mp hEposNat
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
  have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast hEposNat
  have hpair : ∀ k ∈ R, cond E (hits k) ≤ 1 / (M : ℝ) := by
    intro k hk
    have hkdata := (Finset.mem_filter.mp hk).2
    have hcardNat := hhash.2 j k hkdata.1.symm .X hkdata.2.symm b
    have hcardReal : (((E ∩ hits k).card : ℕ) : ℝ) * (M : ℝ) = E.card := by
      exact_mod_cast hcardNat
    unfold cond
    apply (div_le_iff₀ hEreal).2
    rw [← hcardReal]
    field_simp
    exact le_rfl
  have hbad : cond E Bad ≤ ((R.card : ℝ) / M) :=
    conditional_collision_union E hE R hits M hprime.pos hpair
  have hselected : ∀ omega ∈ E, omega ∉ Bad → omega ∈ S := by
    intro omega homega hnotbad
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (mem_selected_iff_hashSurvives27 P M B omega j).2
    refine ⟨hj, ?_, ?_⟩
    · have hjbucket := (mem_bucket_iff_hash27 P M j b omega).1 homega
      exact ⟨hjbucket.1.trans hjbucket.2.1.symm,
        hjbucket.2.1.trans hjbucket.2.2.symm, hjbucket.1.symm ▸ hb⟩
    · intro k hks hcoarse
      by_contra hne
      have hkR : k ∈ R := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hne, hcoarse⟩
      have hx : hashX27 P M omega k = hashX27 P M omega j := by
        unfold hashX27
        rw [hcoarse]
      have hjbucket := (mem_bucket_iff_hash27 P M j b omega).1 homega
      have hxk : hashX27 P M omega k = b := hx.trans hjbucket.1
      have hkbucket : omega ∈ hits k := by
        apply (mem_bucket_iff_hash27 P M k b omega).2
        exact ⟨hxk, hks.1.symm.trans hxk, hks.2.1.symm.trans (hks.1.symm.trans hxk)⟩
      exact hnotbad (Finset.mem_biUnion.mpr ⟨k, hkR, hkbucket⟩)
  have hcover : E ⊆ (E ∩ S) ∪ (E ∩ Bad) := by
    intro omega hωE
    by_cases hωBad : omega ∈ Bad
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hωE, hωBad⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hωE, hselected omega hωE hωBad⟩)
  have hcardNat : E.card ≤ (E ∩ S).card + (E ∩ Bad).card := by
    calc
      E.card ≤ ((E ∩ S) ∪ (E ∩ Bad)).card := Finset.card_le_card hcover
      _ ≤ (E ∩ S).card + (E ∩ Bad).card := Finset.card_union_le _ _
  have hcardReal : (E.card : ℝ) ≤ ((E ∩ S).card : ℝ) + ((E ∩ Bad).card : ℝ) := by
    exact_mod_cast hcardNat
  have hbadCard : ((E ∩ Bad).card : ℝ) ≤
      ((R.card : ℝ) / M) * E.card := by
    apply (div_le_iff₀ hEreal).1
    simpa only [cond] using hbad
  apply (le_div_iff₀ hEreal).2
  change (1 - (R.card : ℝ) / M) * E.card ≤ ((E ∩ S).card : ℝ)
  calc
    (1 - (R.card : ℝ) / M) * E.card =
        (E.card : ℝ) - ((R.card : ℝ) / M) * E.card := by ring
    _ ≤ (E.card : ℝ) - ((E ∩ Bad).card : ℝ) := sub_le_sub_left hbadCard _
    _ ≤ ((E ∩ S).card : ℝ) := by linarith

theorem selected_cond_three_quarters_of_hashXRivals27 (P : RawPopulation)
    (htight : ∀ j i, ∑ W, ((P.coarse j W i).val) = P.grade)
    (hinj : Function.Injective P.coarse)
    (M : ℕ) [NeZero M] (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : P.grade < M) (B : Finset (ZMod M))
    (j : P.Label) (hj : j ∈ P.target) (b : ZMod M) (hb : b ∈ B)
    (hrivals : 4 * (hashXRivals27 P j).card ≤ M) :
    (3 : ℝ) / 4 ≤ cond (bucket P M j b)
      (Finset.univ.filter fun omega => j ∈ selected P M B omega) := by
  have hbase := selected_cond_lower_of_hashXRivals27 P htight hinj M hprime hodd
    hfloor B j hj b hb
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
  have hrivalsReal : (4 : ℝ) * (hashXRivals27 P j).card ≤ M := by
    exact_mod_cast hrivals
  have hratio : ((hashXRivals27 P j).card : ℝ) / M ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hMreal).2
    nlinarith
  linarith

/--
The exact `3/4` target-bucket survival premise for a compatible global population, reduced to
the finite X-coarse rival bound which the global natural demand is designed to dominate.
-/
theorem globalTargetBucket_survival_three_quarters27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (j : GlobalTargetLabel27 g xi r) (b : GlobalBucketLabel27 B)
    (hrivals : 4 * (hashXRivals27
      (rolePopulation (globalPopulation g n xi r) (g.perm r)) j.val).card ≤ M) :
    (3 : ℝ) / 4 ≤ cond (globalTargetBucket27 g xi r B j b)
      (Finset.univ.filter fun omega => j ∈ globalSelectedTargets27 g xi r B omega) := by
  have h := selected_cond_three_quarters_of_hashXRivals27
    (rolePopulation (globalPopulation g n xi r) (g.perm r))
    (global_role_tight27 g hg xi r)
    (global_role_coarse_injective27 g hg xi r)
    M hprime hodd hfloor B j.val j.property b.val b.property hrivals
  simpa only [globalTargetBucket27, globalSelectedTargets27,
    Finset.mem_filter, Finset.mem_attach, true_and] using h

/--
The target-bucket survival estimate at the modulus produced by `globalDemand`.  Its sole
remaining finite premise is the uniform X-projection fibre identity for the actual population.
-/
theorem globalTargetBucket_survival_of_demand27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (floor m : ℕ)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (j : GlobalTargetLabel27 g xi r) (bucketIndex : GlobalBucketLabel27 B)
    (huniform : (hashXFiber27
        (rolePopulation (globalPopulation g (b * m) xi r) (g.perm r)) j.val).card *
      (hashXImage27
        (rolePopulation (globalPopulation g (b * m) xi r) (g.perm r))).card =
      Fintype.card (globalPopulation g (b * m) xi r).Label) :
    (3 : ℝ) / 4 ≤ cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter fun omega => j ∈ globalSelectedTargets27 g xi r B omega) := by
  let P := globalPopulation g (b * m) xi r
  let RP := rolePopulation P (g.perm r)
  let NY := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Y)).card
  let NZ := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Z)).card
  have hnatural : 4 * (hashXRivals27 RP j.val).card ≤
      natural_demand (max floor (2 * w + 3)) (Fintype.card P.Label)
        (hashXImage27 RP).card NY NZ P.target.card (80 * (w * (b * m)))
        (globalPcompMax g (b * m) xi r 0) (globalPcompMax g (b * m) xi r 1) :=
    hashXRivals_le_naturalDemand27 RP (max floor (2 * w + 3)) NY NZ
      P.target.card (80 * (w * (b * m)))
      (globalPcompMax g (b * m) xi r 0) (globalPcompMax g (b * m) xi r 1)
      j.val (by simpa only [P, RP] using huniform)
  have hglobal : 4 * (hashXRivals27 RP j.val).card ≤ globalDemand g b floor m xi r := by
    simpa only [globalDemand, P, RP, NY, NZ, hashXImage27, rolePopulation] using hnatural
  have hrivals : 4 * (hashXRivals27 RP j.val).card ≤ M := by omega
  exact globalTargetBucket_survival_three_quarters27 g hg xi r B hprime hodd hfloor
    j bucketIndex (by simpa only [P, RP] using hrivals)

/-- The paper's unconditional `3/4` target-bucket survival contribution. -/
theorem globalTargetBucket_survival27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (floor m : ℕ)
    (xi : ExactGrid g (b * m)) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (j : GlobalTargetLabel27 g xi r) (bucketIndex : GlobalBucketLabel27 B) :
    (3 : ℝ) / 4 ≤ cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter fun omega => j ∈ globalSelectedTargets27 g xi r B omega) := by
  exact globalTargetBucket_survival_of_demand27 g hg floor m xi r B hprime hodd hfloor
    hdemand j bucketIndex (global_role_hashXFiber_mul_image27 g xi r j.val)


/-- Finite conditional Markov inequality in the exact cardinal form used for hole counts. -/
theorem conditional_nat_markov27 {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (E : Finset Omega) (hE : E.Nonempty) (h : Omega → ℕ)
    (threshold debit : ℝ) (hthreshold : 0 < threshold)
    (hmoment : ∑ omega ∈ E, (h omega : ℝ) ≤ debit * threshold * E.card) :
    cond E (Finset.univ.filter fun omega => threshold < (h omega : ℝ)) ≤ debit := by
  classical
  let Bad := E ∩ (Finset.univ.filter fun omega => threshold < (h omega : ℝ))
  have hBadSub : Bad ⊆ E := Finset.inter_subset_left
  have hpoint : ∀ omega ∈ Bad, threshold ≤ (h omega : ℝ) := by
    intro omega homega
    exact ((Finset.mem_filter.mp (Finset.mem_inter.mp homega).2).2).le
  have hsumBad : (Bad.card : ℝ) * threshold ≤ ∑ omega ∈ E, (h omega : ℝ) := by
    calc
      (Bad.card : ℝ) * threshold = ∑ _omega ∈ Bad, threshold := by
        simp [mul_comm]
      _ ≤ ∑ omega ∈ Bad, (h omega : ℝ) := by
        exact Finset.sum_le_sum fun omega homega => hpoint omega homega
      _ ≤ ∑ omega ∈ E, (h omega : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hBadSub
          (fun omega _ _ => Nat.cast_nonneg (h omega))
  have hcard : (Bad.card : ℝ) ≤ debit * E.card := by
    nlinarith
  unfold cond
  have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
  apply (div_le_iff₀ hEreal).2
  simpa only [Bad, mul_comm] using hcard

theorem globalTargetBucket_nonempty27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (j : GlobalTargetLabel27 g xi r) (bucketIndex : GlobalBucketLabel27 B) :
    (globalTargetBucket27 g xi r B j bucketIndex).Nonempty := by
  have hcard := globalTargetBucket_card27 g hg xi r B hprime hodd hfloor j bucketIndex
  apply Finset.card_pos.mp
  have hout : 0 < Fintype.card (HashOutcome (globalPopulation g n xi r) M) :=
    Fintype.card_pos
  have hprod : 0 < (globalTargetBucket27 g xi r B j bucketIndex).card * M ^ 2 := by
    rw [hcard]
    exact hout
  exact Nat.pos_of_ne_zero fun hzero => by simp [hzero] at hprod


end
end OmegaBound.ADVXXZGeneral
end
