import OmegaBound.ADVXXZGeneralGlobalExactQExponents
import OmegaBound.ADVXXZEpsCnt

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem gmc_coordFin_val27 {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private def GlobalLabelCountTable27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :=
  Shape w → Fin ((globalPopulation g n xi r).n + 1)

private noncomputable def globalLabelCountTableOf27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (j : (globalPopulation g n xi r).Label) :
    GlobalLabelCountTable27 g xi r :=
  fun u => ⟨typeCnt j.val u, Nat.lt_succ_of_le (typeCnt_le j.val u)⟩

private theorem gmc_label_table_sum27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (j : (globalPopulation g n xi r).Label) :
    ∑ u, (globalLabelCountTableOf27 g xi r j u).val =
      (globalPopulation g n xi r).n := by
  exact sum_typeCnt j.val

private theorem gmc_label_table_marginal27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (j : (globalPopulation g n xi r).Label)
    (S : Side) (a : Fin (2 * w + 1)) :
    (∑ u : Shape w, if Parent25.coordFin S u = a then
        (globalLabelCountTableOf27 g xi r j u).val else 0) =
      (∑ u : Shape w, if Parent25.coordFin S u = a then
        ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0) := by
  classical
  have hcomp := ADVXXZEps.typeCnt_comp_fiber
    (fun u : Shape w => Parent25.coordFin S u) j.val a
  change typeCnt (fun i => Parent25.coordFin S (j.val i)) a =
      ∑ u ∈ Finset.univ.filter (fun u => Parent25.coordFin S u = a),
        typeCnt j.val u at hcomp
  have hj : typeCnt (fun i => Parent25.coordFin S (j.val i)) a =
      ∑ u : Shape w, if Parent25.coordFin S u = a then
        ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
    unfold globalPopulation at j
    dsimp only at j
    exact j.property S a
  calc
    (∑ u : Shape w, if Parent25.coordFin S u = a then
        (globalLabelCountTableOf27 g xi r j u).val else 0) =
        ∑ u : Shape w, if Parent25.coordFin S u = a then typeCnt j.val u else 0 := by
          rfl
    _ = ∑ u ∈ Finset.univ.filter (fun u => Parent25.coordFin S u = a),
        typeCnt j.val u := by rw [Finset.sum_filter]
    _ = typeCnt (fun i => Parent25.coordFin S (j.val i)) a := hcomp.symm
    _ = _ := hj

private theorem gmc_table_sameMarginals27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (j : (globalPopulation g (b * m) xi r).Label) :
    SameMarginals
      (fun u : Shape w =>
        ((globalLabelCountTableOf27 g xi r j u).val : ℝ) /
          (globalPopulation g (b * m) xi r).n)
      (g.alpha r).probR := by
  classical
  intro S a
  let N := (globalPopulation g (b * m) xi r).n
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold marginal
  have hcoord : ∀ u : Shape w,
      (coord S u = (a : ℕ)) ↔ Parent25.coordFin S u = a := by
    intro u
    constructor
    · intro h
      apply Fin.ext
      exact (gmc_coordFin_val27 S u).trans h
    · intro h
      exact (gmc_coordFin_val27 S u).symm.trans (congrArg Fin.val h)
  simp_rw [hcoord]
  have hite : ∀ u : Shape w,
      (if Parent25.coordFin S u = a then
          ((globalLabelCountTableOf27 g xi r j u).val : ℝ) /
            (globalPopulation g (b * m) xi r).n else 0) =
        (if Parent25.coordFin S u = a then
          ((globalLabelCountTableOf27 g xi r j u).val : ℝ) else 0) /
            (globalPopulation g (b * m) xi r).n := by
    intro u
    split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_div]
  have hcounts := gmc_label_table_marginal27 g xi r j S a
  have hcountsR := congrArg (fun x : ℕ => (x : ℝ)) hcounts
  push_cast at hcountsR
  rw [hcountsR, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hua : Parent25.coordFin S u = a
  · simp only [hua, if_pos]
    rw [show
      ((((b : ℚ) * (m : ℚ) * g.joint.prob (r, u)).floor.toNat : ℕ) : ℝ) =
        ((globalPopulation g (b * m) xi r).n : ℝ) * (g.alpha r).probR u by
          simpa only [Nat.cast_mul] using globalCellCount_cast27 g hg hb xi r u]
    change ((N : ℝ) * (g.alpha r).probR u) / N = (g.alpha r).probR u
    field_simp
  · simp [hua]

private theorem gmc_entropy_le_add_penalty27 {w : ℕ}
    (p alpha : Shape w → ℝ) (hp : IsProbability p)
    (halpha : IsProbability alpha) (hsame : SameMarginals p alpha) :
    entropy p ≤ entropy alpha + penalty alpha := by
  let S : Set ℝ := {h : ℝ | ∃ p' : Shape w → ℝ,
    IsProbability p' ∧ SameMarginals alpha p' ∧ h = entropy p'}
  have hmem : entropy p ∈ S := ⟨p, hp, fun W a => (hsame W a).symm, rfl⟩
  letI : Nonempty (Shape w) := by
    by_contra hempty
    letI : IsEmpty (Shape w) := not_nonempty_iff.mp hempty
    simpa using halpha.2
  have hbdd : BddAbove S := by
    refine ⟨Real.log (Fintype.card (Shape w) : ℝ) / Real.log 2, ?_⟩
    intro h hh
    rcases hh with ⟨p', hp', -, rfl⟩
    have hH := Entropy.H_le_log_card (s := (Finset.univ : Finset (Shape w)))
      Finset.univ_nonempty (fun u _ => hp'.1 u) (by simpa using hp'.2)
    have hHn : entropyNats p' ≤ Real.log (Fintype.card (Shape w) : ℝ) := by
      calc
        entropyNats p' = Entropy.H Finset.univ p' :=
          (Entropy.H_eq_neg_sum Finset.univ p').symm
        _ ≤ Real.log ((Finset.univ : Finset (Shape w)).card : ℝ) := hH
        _ = _ := by simp
    rw [entropyNats_eq_log_two_mul_entropy, mul_comm] at hHn
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).2 hHn
  have hsup : entropy p ≤ sSup S := le_csSup hbdd hmem
  unfold penalty
  change entropy p ≤ entropy alpha + (sSup S - entropy alpha)
  linarith

private theorem gmc_label_fiber_bound27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (k : GlobalLabelCountTable27 g xi r) :
    (Fintype.card {j : (globalPopulation g (b * m) xi r).Label //
        globalLabelCountTableOf27 g xi r j = k} : ℝ) ≤
      Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
  classical
  let Fiber := {j : (globalPopulation g (b * m) xi r).Label //
    globalLabelCountTableOf27 g xi r j = k}
  cases isEmpty_or_nonempty Fiber with
  | inl hempty =>
      letI := hempty
      simp only [Fintype.card_eq_zero, Nat.cast_zero]
      exact (Real.exp_pos _).le
  | inr hnonempty =>
      letI := hnonempty
      let j0 : Fiber := Classical.choice inferInstance
      let counts : Shape w → ℕ := fun u => (k u).val
      have hjcount (j : Fiber) (u : Shape w) : typeCnt j.val.val u = counts u := by
        have hu := congrArg Fin.val (congrFun j.property u)
        simpa only [globalLabelCountTableOf27, counts] using hu
      have hsum : ∑ u, counts u = (globalPopulation g (b * m) xi r).n := by
        calc
          ∑ u, counts u = ∑ u, (globalLabelCountTableOf27 g xi r j0.val u).val := by
            apply Finset.sum_congr rfl
            intro u _
            exact (congrArg Fin.val (congrFun j0.property u)).symm
          _ = _ := gmc_label_table_sum27 g xi r j0.val
      let p : Shape w → ℝ := fun u => (counts u : ℝ) /
        (globalPopulation g (b * m) xi r).n
      have hp : IsProbability p := by
        constructor
        · intro u
          exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · unfold p
          rw [← Finset.sum_div, ← Nat.cast_sum, hsum]
          exact div_self (Nat.cast_ne_zero.mpr hn)
      have hsame : SameMarginals p (g.alpha r).probR := by
        intro S a
        calc
          marginal p S a = marginal
              (fun u : Shape w =>
                ((globalLabelCountTableOf27 g xi r j0.val u).val : ℝ) /
                  (globalPopulation g (b * m) xi r).n) S a := by
            apply congrArg (fun f : Shape w → ℝ => marginal f S a)
            funext u
            have hu := congrArg Fin.val (congrFun j0.property u)
            exact congrArg
              (fun z : ℕ => (z : ℝ) / (globalPopulation g (b * m) xi r).n) hu.symm
          _ = marginal (g.alpha r).probR S a :=
            gmc_table_sameMarginals27 g hg hb xi r hn j0.val S a
      have halpha : IsProbability (g.alpha r).probR :=
        ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩
      have hentropy := gmc_entropy_le_add_penalty27 p (g.alpha r).probR hp halpha hsame
      have hclass := type_class_bounds
        (globalPopulation g (b * m) xi r).n counts hsum
      have hinj : Function.Injective
          (fun j : Fiber =>
            (⟨j.val.val, hjcount j⟩ : {x : Fin (globalPopulation g (b * m) xi r).n →
              Shape w // ∀ u, typeCnt x u = counts u})) := by
        intro j l h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {x : Fin (globalPopulation g (b * m) xi r).n → Shape w //
            ∀ u, typeCnt x u = counts u} => z.val) h
      have hcard : Fintype.card Fiber ≤
          Fintype.card {x : Fin (globalPopulation g (b * m) xi r).n → Shape w //
            ∀ u, typeCnt x u = counts u} :=
        Fintype.card_le_of_injective _ hinj
      calc
        (Fintype.card Fiber : ℝ) ≤
            (Fintype.card {x : Fin (globalPopulation g (b * m) xi r).n → Shape w //
              ∀ u, typeCnt x u = counts u} : ℝ) := by exact_mod_cast hcard
        _ ≤ Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) *
            entropyNats p) := by simpa only [p] using hclass.2
        _ ≤ Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
            (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
          apply Real.exp_le_exp.mpr
          rw [entropyNats_eq_log_two_mul_entropy]
          calc
            ((globalPopulation g (b * m) xi r).n : ℝ) *
                (Real.log 2 * entropy p) =
              (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2) *
                entropy p := by ring
            _ ≤ (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2) *
                (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR)) :=
              mul_le_mul_of_nonneg_left hentropy
                (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le)
            _ = _ := by ring

/-- The marginal-only global label family has the paper `H(alpha)+P_alpha` exponent,
    with one uniform count-table polynomial. -/
theorem globalLabel_paper_entropy_upper27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    (Fintype.card (globalPopulation g (b * m) xi r).Label : ℝ) ≤
      (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          Fintype.card (Shape w) *
        Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
  classical
  let P := globalPopulation g (b * m) xi r
  let Table := GlobalLabelCountTable27 g xi r
  let tableOf := globalLabelCountTableOf27 g xi r
  letI : Fintype Table := by
    dsimp only [Table, GlobalLabelCountTable27]
    infer_instance
  have hcard : Fintype.card P.Label =
      ∑ k : Table, Fintype.card {j : P.Label // tableOf j = k} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv tableOf).symm
  rw [hcard, Nat.cast_sum]
  calc
    (∑ k : Table, (Fintype.card {j : P.Label // tableOf j = k} : ℝ)) ≤
        ∑ _k : Table, Real.exp ((P.n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
      apply Finset.sum_le_sum
      intro k _
      exact gmc_label_fiber_bound27 g hg hb xi r hn k
    _ = (Fintype.card Table : ℝ) * Real.exp ((P.n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
      simp
    _ = ((P.n : ℝ) + 1) ^ Fintype.card (Shape w) *
        Real.exp ((P.n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR))) := by
      congr 1
      simp [Table, GlobalLabelCountTable27, P]

private theorem gmc_filter_card_eq_of_perm27 {I : Type*} [Fintype I]
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

set_option maxHeartbeats 1000000 in
private noncomputable def globalLabelPermMarginal27 {w n : ℕ} (g : GlobalSpec w)
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
    | X => exact (gmc_filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans (j.property .X a)
    | Y => exact (gmc_filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans (j.property .Y a)
    | Z => exact (gmc_filter_card_eq_of_perm27 e.symm _ _ (fun _ => Iff.rfl)).trans (j.property .Z a)
  · intro W a
    cases W with
    | X => exact (gmc_filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans (j.property .X a)
    | Y => exact (gmc_filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans (j.property .Y a)
    | Z => exact (gmc_filter_card_eq_of_perm27 e _ _ (fun _ => Iff.rfl)).trans (j.property .Z a)
  · intro j
    apply Subtype.ext
    funext i
    simp
  · intro j
    apply Subtype.ext
    funext i
    simp

set_option maxHeartbeats 1000000 in
private theorem globalLabelPermMarginal27_coarse {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (j : (globalPopulation g n xi r).Label) (S : Side) (i : Fin _) :
    (globalPopulation g n xi r).coarse (globalLabelPermMarginal27 g xi r e j) S i =
      (globalPopulation g n xi r).coarse j S (e.symm i) := by
  classical
  unfold globalPopulation globalLabelPermMarginal27
  rfl

private def globalCoarseCount27 {w n : ℕ} (g : GlobalSpec w) (r : Fin 6)
    (S : Side) (a : Fin (2 * w + 1)) : ℕ :=
  ∑ u : Shape w, if Parent25.coordFin S u = a then
    ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0

private theorem gmc_coarseCount_sum27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (S : Side) :
    ∑ a, globalCoarseCount27 (n := n) g r S a = (globalPopulation g n xi r).n := by
  classical
  unfold globalCoarseCount27 globalPopulation
  dsimp only
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

private theorem gmc_coarseCount_normalized27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) (S : Side) :
    (fun a => (globalCoarseCount27 (n := b * m) g r S a : ℝ) /
      (globalPopulation g (b * m) xi r).n) =
      marginal (g.alpha r).probR S := by
  funext a
  let N := (globalPopulation g (b * m) xi r).n
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold globalCoarseCount27 marginal
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  have hcoord : (Parent25.coordFin S u = a) ↔ coord S u = (a : ℕ) := by
    constructor
    · intro h
      exact (gmc_coordFin_val27 S u).symm.trans (congrArg Fin.val h)
    · intro h
      apply Fin.ext
      exact (gmc_coordFin_val27 S u).trans h
  by_cases hua : Parent25.coordFin S u = a
  · rw [if_pos hua, if_pos (hcoord.mp hua), globalCellCount_cast27 g hg hb xi r u]
    change ((N : ℝ) * (g.alpha r).probR u) / N = (g.alpha r).probR u
    field_simp
  · rw [if_neg hua, if_neg (fun h => hua (hcoord.mpr h))]
    norm_num

set_option maxHeartbeats 1000000 in
/-- Every role-side coarse image contains the whole marginal type class; hence its size has
    the paper marginal-entropy lower bound with the standard type polynomial. -/
theorem globalCoarseImage_paper_entropy_lower27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) (S : Side) :
    Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        entropy (marginal (g.alpha r).probR S)) /
        (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          Fintype.card (Fin (2 * w + 1)) ≤
      (((Finset.univ : Finset (globalPopulation g (b * m) xi r).Label).image
        (fun j => (globalPopulation g (b * m) xi r).coarse j S)).card : ℝ) := by
  classical
  let P := globalPopulation g (b * m) xi r
  let counts : Fin (2 * w + 1) → ℕ := globalCoarseCount27 (n := b * m) g r S
  letI : DecidablePred (fun x : Fin P.n → Fin (2 * w + 1) =>
      ∀ a, typeCnt x a = counts a) := fun _ => Fintype.decidableForallFintype
  let TC := {x : Fin P.n → Fin (2 * w + 1) // ∀ a, typeCnt x a = counts a}
  let image := (Finset.univ : Finset P.Label).image (fun j => P.coarse j S)
  let j0 : GlobalTargetLabel27 g xi r := Classical.choice (globalTargetLabel_nonempty27 g xi r)
  have hj0 (a : Fin (2 * w + 1)) : typeCnt (P.coarse j0.val S) a = counts a := by
    simpa only [P, counts, globalCoarseCount27, globalPopulation, typeCnt] using
      j0.val.property S a
  have hmem (x : TC) : x.val ∈ image := by
    have hhist : ∀ a, histogram27 (P.coarse j0.val S) a = histogram27 x.val a := by
      intro a
      simpa only [histogram27, typeCnt] using (hj0 a).trans (x.property a).symm
    let e := histogramEquiv27 (P.coarse j0.val S) x.val hhist
    let j := globalLabelPermMarginal27 g xi r e j0.val
    have hj : P.coarse j S = x.val := by
      funext i
      rw [globalLabelPermMarginal27_coarse g xi r e j0.val S i]
      have hs := histogramEquiv27_spec
        (P.coarse j0.val S) x.val hhist (e.symm i)
      change x.val (e (e.symm i)) = P.coarse j0.val S (e.symm i) at hs
      rw [e.apply_symm_apply] at hs
      exact hs.symm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  let phi : TC → {x // x ∈ image} := fun x => ⟨x.val, hmem x⟩
  have hphi : Function.Injective phi := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x // x ∈ image} => z.val) h
  have hcard : Fintype.card TC ≤ image.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective phi hphi
  have htype := type_class_bounds P.n counts (gmc_coarseCount_sum27 g xi r S)
  have hnorm := gmc_coarseCount_normalized27 g hg hb xi r hn S
  calc
    Real.exp ((P.n : ℝ) * Real.log 2 * entropy (marginal (g.alpha r).probR S)) /
          ((P.n : ℝ) + 1) ^ Fintype.card (Fin (2 * w + 1)) =
        Real.exp ((P.n : ℝ) * entropyNats (fun a => (counts a : ℝ) / P.n)) /
          ((P.n : ℝ) + 1) ^ Fintype.card (Fin (2 * w + 1)) := by
      rw [hnorm, entropyNats_eq_log_two_mul_entropy]
      ring_nf
    _ ≤ (Fintype.card TC : ℝ) := by simpa only [TC] using htype.1
    _ ≤ (image.card : ℝ) := by exact_mod_cast hcard

end
end OmegaBound.ADVXXZGeneral
end
