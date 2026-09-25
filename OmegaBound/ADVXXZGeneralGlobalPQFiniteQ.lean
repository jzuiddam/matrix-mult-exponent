import OmegaBound.ADVXXZGeneralGlobalPQ
import OmegaBound.ADVXXZGeneralPQExponentsParent25
import OmegaBound.ADVXXZGeneralPQPartitionProduct

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem global_key_eq_inl_iff {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (W : Fin 2) (v u : Shape w) :
    GlobalBridge25.key g r W v = Sum.inl u ↔
      GlobalBridge25.boundary g r W v ∧ v = u := by
  classical
  unfold GlobalBridge25.key
  split <;> simp_all

private theorem global_key_eq_inr_iff {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (W : Fin 2) (v : Shape w) (k : Fin (2*w+1)) :
    GlobalBridge25.key g r W v = Sum.inr k ↔
      ¬ GlobalBridge25.boundary g r W v ∧
        Parent25.coordFin (GlobalBridge25.side g r W) v = k := by
  classical
  unfold GlobalBridge25.key
  split <;> simp_all

private theorem card_filter_by_fibers
    {I U A : Type*} [Fintype I] [Fintype U]
    [DecidableEq I] [DecidableEq U] [DecidableEq A]
    (f : I → U) (a : I → A) (P : U → Prop) [DecidablePred P] (x : A) :
    (Finset.univ.filter (fun i ↦ P (f i) ∧ a i = x)).card =
      ∑ u : U, if P u then
        (Finset.univ.filter (fun i ↦ f i = u ∧ a i = x)).card else 0 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f)
    (s := (Finset.univ : Finset I).filter (fun i ↦ P (f i) ∧ a i = x))
    (t := (Finset.univ : Finset U).filter P)]
  · simp only [Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro u _
    split
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      aesop
    · simp_all
  · intro i hi
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2.1⟩)

private theorem global_coordFin_val {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem global_coordFin_eq_iff {w : ℕ} (S : Side) (u : Shape w)
    (k : Fin (2*w+1)) :
    Parent25.coordFin S u = k ↔ coord S u = k.val := by
  constructor
  · intro h
    exact (global_coordFin_val S u).symm.trans (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact (global_coordFin_val S u).trans h

private theorem global_side_eq {w : ℕ} (g : GlobalSpec w) (r : Fin 6) (W : Fin 2) :
    GlobalBridge25.side g r W =
      if W = 0 then g.perm r .Y else g.perm r .Z := by
  unfold GlobalBridge25.side
  split <;> rfl

private theorem global_compatible_cell_count {w : ℕ} (g : GlobalSpec w)
    (n : ℕ) (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (j : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W))
    (ha : globalCompatible g n xi r W j a)
    (c : GlobalBridge25.Cell w) (sigma : Chunk w) :
    (Finset.univ.filter (fun i ↦
      GlobalBridge25.key g r W (j.val i) = c ∧ a i = sigma)).card =
        GlobalBridge25.histogram g n xi r W c sigma := by
  classical
  have hc := ha
  unfold globalCompatible at hc
  dsimp only at hc
  cases c with
  | inl u =>
      by_cases hu : GlobalBridge25.boundary g r W u
      · calc
          (Finset.univ.filter (fun i ↦
              GlobalBridge25.key g r W (j.val i) = Sum.inl u ∧
                a i = sigma)).card =
              globalCellCount g n xi r (GlobalBridge25.side g r W) j a
                (fun v ↦ v = u) sigma := by
                unfold globalCellCount
                congr 1
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                  global_key_eq_inl_iff]
                aesop
          _ = xi.count (GlobalBridge25.side g r W) r u sigma := by
                simpa only [GlobalBridge25.boundary, global_side_eq] using
                  hc.1 u (by simpa only [GlobalBridge25.boundary] using hu) sigma
          _ = GlobalBridge25.histogram g n xi r W (Sum.inl u) sigma := by
                unfold GlobalBridge25.histogram
                symm
                calc
                  (∑ v : Shape w, if GlobalBridge25.key g r W v = Sum.inl u
                    then xi.count (GlobalBridge25.side g r W) r v sigma else 0) =
                      ∑ v : Shape w, if v = u
                        then xi.count (GlobalBridge25.side g r W) r v sigma else 0 := by
                          apply Finset.sum_congr rfl
                          intro v _
                          by_cases hv : v = u <;>
                            simp [global_key_eq_inl_iff, hv, hu]
                  _ = _ := by simp
      · have hleft : (Finset.univ.filter (fun i ↦
            GlobalBridge25.key g r W (j.val i) = Sum.inl u ∧
              a i = sigma)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro i _ hi
              have hk := (global_key_eq_inl_iff g r W (j.val i) u).mp hi.1
              exact hu (hk.2 ▸ hk.1)
        rw [hleft]
        unfold GlobalBridge25.histogram
        symm
        apply Finset.sum_eq_zero
        intro v _
        by_cases hv : v = u <;> simp [global_key_eq_inl_iff, hv, hu]
  | inr k =>
      let S := GlobalBridge25.side g r W
      let all := (Finset.univ : Finset (Fin (globalPopulation g n xi r).n)).filter
        (fun i ↦ Parent25.coordFin S (j.val i) = k ∧ a i = sigma)
      let bnd := (Finset.univ : Finset (Fin (globalPopulation g n xi r).n)).filter
        (fun i ↦ GlobalBridge25.boundary g r W (j.val i) ∧
          Parent25.coordFin S (j.val i) = k ∧ a i = sigma)
      let res := (Finset.univ : Finset (Fin (globalPopulation g n xi r).n)).filter
        (fun i ↦ GlobalBridge25.key g r W (j.val i) = Sum.inr k ∧ a i = sigma)
      let B := ∑ u : Shape w,
        if GlobalBridge25.boundary g r W u ∧ Parent25.coordFin S u = k
        then xi.count S r u sigma else 0
      have hall : all.card = ∑ u : Shape w,
          if Parent25.coordFin S u = k then xi.count S r u sigma else 0 := by
        calc
          all.card = globalCellCount g n xi r S j a
              (fun u ↦ coord S u = k.val) sigma := by
                unfold all globalCellCount
                congr 1
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [global_coordFin_eq_iff]
          _ = ∑ u : Shape w, if coord S u = k.val
                then xi.count S r u sigma else 0 := by
                simpa only [S, global_side_eq] using hc.2 k sigma
          _ = ∑ u : Shape w, if Parent25.coordFin S u = k
                then xi.count S r u sigma else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                simp only [global_coordFin_eq_iff]
      have hbnd : bnd.card = B := by
        calc
          bnd.card = ∑ u : Shape w,
              if GlobalBridge25.boundary g r W u ∧ Parent25.coordFin S u = k
              then (Finset.univ.filter (fun i ↦ j.val i = u ∧ a i = sigma)).card
              else 0 := by
                simpa only [bnd, and_assoc] using
                  (card_filter_by_fibers j.val a
                    (fun u ↦ GlobalBridge25.boundary g r W u ∧
                      Parent25.coordFin S u = k) sigma)
          _ = B := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases hbu : GlobalBridge25.boundary g r W u ∧
                  Parent25.coordFin S u = k
                · simp only [if_pos hbu, B]
                  have hdef :
                      (Finset.univ.filter (fun i ↦ j.val i = u ∧ a i = sigma)).card =
                        globalCellCount g n xi r S j a (fun v ↦ v = u) sigma := by
                    unfold globalCellCount
                    congr 1
                    ext i
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [hdef]
                  simpa only [S, global_side_eq] using
                    hc.1 u (by simpa only [GlobalBridge25.boundary] using hbu.1) sigma
                · simp [hbu]
      have hdisj : Disjoint bnd res := by
        rw [Finset.disjoint_left]
        intro i hib hir
        have hib' := (Finset.mem_filter.mp hib).2
        have hir' := (Finset.mem_filter.mp hir).2
        have hnot := (global_key_eq_inr_iff g r W (j.val i) k).mp hir'.1
        exact hnot.1 hib'.1
      have hunion : bnd ∪ res = all := by
        ext i
        simp only [bnd, res, all, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and, global_key_eq_inr_iff]
        tauto
      have hparts : bnd.card + res.card = all.card := by
        calc
          bnd.card + res.card = (bnd ∪ res).card :=
            (Finset.card_union_of_disjoint hdisj).symm
          _ = all.card := congrArg Finset.card hunion
      have hgrid : B + GlobalBridge25.histogram g n xi r W (Sum.inr k) sigma =
          ∑ u : Shape w, if Parent25.coordFin S u = k
            then xi.count S r u sigma else 0 := by
        unfold B GlobalBridge25.histogram
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        by_cases hbu : GlobalBridge25.boundary g r W u <;>
          by_cases hku : Parent25.coordFin S u = k <;>
            simp [global_key_eq_inr_iff, hbu, hku, S]
      change res.card = GlobalBridge25.histogram g n xi r W (Sum.inr k) sigma
      omega

private theorem typeCnt_comp_eq_sum_fibers
    {n : ℕ} {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V]
    (f : Fin n → U) (g : U → V) (c : V) :
    typeCnt (fun i ↦ g (f i)) c =
      ∑ u : U, if g u = c then typeCnt f u else 0 := by
  classical
  simpa only [typeCnt, and_true] using
    (card_filter_by_fibers (A := Unit) f (fun _ ↦ ()) (fun u ↦ g u = c) ())

private theorem global_target_shape_count {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) (u : Shape w) :
    typeCnt j.val.val u = ((n : ℚ) * g.joint.prob (r, u)).floor.toNat := by
  classical
  unfold globalPopulation at j
  dsimp only at j
  simpa only [typeCnt] using ((Finset.mem_filter.mp j.property).2 u)

private theorem global_histogram_total {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (j : {j // j ∈ (globalPopulation g n xi r).target})
    (c : GlobalBridge25.Cell w) :
    ∑ sigma, GlobalBridge25.histogram g n xi r W c sigma =
      Nat.card {i : Fin (globalPopulation g n xi r).n //
        GlobalBridge25.key g r W (j.val.val i) = c} := by
  classical
  calc
    ∑ sigma, GlobalBridge25.histogram g n xi r W c sigma =
        ∑ u : Shape w, ∑ sigma : Chunk w,
          if GlobalBridge25.key g r W u = c
          then xi.count (GlobalBridge25.side g r W) r u sigma else 0 := by
            unfold GlobalBridge25.histogram
            rw [Finset.sum_comm]
    _ = ∑ u : Shape w, if GlobalBridge25.key g r W u = c
          then ∑ sigma : Chunk w, xi.count (GlobalBridge25.side g r W) r u sigma
          else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : GlobalBridge25.key g r W u = c <;> simp [hu]
    _ = ∑ u : Shape w, if GlobalBridge25.key g r W u = c
          then ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : GlobalBridge25.key g r W u = c
            · simp only [if_pos hu]
              exact xi.total (GlobalBridge25.side g r W) r u
            · simp [hu]
    _ = ∑ u : Shape w, if GlobalBridge25.key g r W u = c
          then typeCnt j.val.val u else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : GlobalBridge25.key g r W u = c
            · simp only [if_pos hu]
              exact (global_target_shape_count g xi r j u).symm
            · simp [hu]
    _ = typeCnt (fun i ↦ GlobalBridge25.key g r W (j.val.val i)) c :=
      (typeCnt_comp_eq_sum_fibers j.val.val (GlobalBridge25.key g r W) c).symm
    _ = Nat.card {i : Fin (globalPopulation g n xi r).n //
          GlobalBridge25.key g r W (j.val.val i) = c} := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
            unfold typeCnt
            congr 1 <;> ext i <;>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private abbrev GlobalQFamily {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :=
  {x : Fin (globalPopulation g n xi r).n → Chunk w // ∀ c sigma,
    (Finset.univ.filter (fun i ↦
      GlobalBridge25.key g r W (j.val.val i) = c ∧ x i = sigma)).card =
        GlobalBridge25.histogram g n xi r W c sigma}

private noncomputable def globalQFamilyOfCompatible {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target})
    (a : {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val ∧
      globalCompatible g n xi r W j.val a}) : GlobalQFamily g xi r W j :=
  ⟨a.val, global_compatible_cell_count g n xi r W j.val a.val a.property.2.2⟩

private theorem globalQFamilyOfCompatible_injective {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    Function.Injective (globalQFamilyOfCompatible g xi r W beta j) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z : GlobalQFamily g xi r W j ↦ z.val) hab

private theorem global_qfamily_card {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    Nat.card (GlobalQFamily g xi r W j) =
      ∏ c : GlobalBridge25.Cell w,
        Nat.card {x : Fin (Nat.card {i : Fin (globalPopulation g n xi r).n //
            GlobalBridge25.key g r W (j.val.val i) = c}) → Chunk w //
          ∀ sigma, typeCnt x sigma = GlobalBridge25.histogram g n xi r W c sigma} := by
  simpa only [GlobalQFamily] using
    (partitionProductCardinality_parent25
      (g := fun i ↦ GlobalBridge25.key g r W (j.val.val i))
      (k := GlobalBridge25.histogram g n xi r W))

private theorem global_qfiber_upper {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val ∧
      globalCompatible g n xi r W j.val a} : ℝ) ≤
        Real.exp (GlobalBridge25.qExponent g n xi r W) := by
  classical
  have hfactor : ∀ c : GlobalBridge25.Cell w,
      (Nat.card {x : Fin (Nat.card {i : Fin (globalPopulation g n xi r).n //
          GlobalBridge25.key g r W (j.val.val i) = c}) → Chunk w //
        ∀ sigma, typeCnt x sigma = GlobalBridge25.histogram g n xi r W c sigma} : ℝ) ≤
        Real.exp (((∑ sigma, GlobalBridge25.histogram g n xi r W c sigma : ℕ) : ℝ) *
          entropyNats (fun sigma ↦
            (GlobalBridge25.histogram g n xi r W c sigma : ℝ) /
              ∑ sigma, GlobalBridge25.histogram g n xi r W c sigma)) := by
    intro c
    have h := type_class_bounds
      (Nat.card {i : Fin (globalPopulation g n xi r).n //
        GlobalBridge25.key g r W (j.val.val i) = c})
      (GlobalBridge25.histogram g n xi r W c)
      (global_histogram_total g xi r W j c)
    simpa only [Nat.card_eq_fintype_card, global_histogram_total g xi r W j c] using h.2
  calc
    (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val ∧
      globalCompatible g n xi r W j.val a} : ℝ) ≤
        (Nat.card (GlobalQFamily g xi r W j) : ℝ) := by
          exact_mod_cast Nat.card_le_card_of_injective
            (globalQFamilyOfCompatible g xi r W beta j)
            (globalQFamilyOfCompatible_injective g xi r W beta j)
    _ = ∏ c : GlobalBridge25.Cell w,
        (Nat.card {x : Fin (Nat.card {i : Fin (globalPopulation g n xi r).n //
            GlobalBridge25.key g r W (j.val.val i) = c}) → Chunk w //
          ∀ sigma, typeCnt x sigma = GlobalBridge25.histogram g n xi r W c sigma} : ℝ) := by
            rw [global_qfamily_card g xi r W j, Nat.cast_prod]
    _ ≤ ∏ c : GlobalBridge25.Cell w,
        Real.exp (((∑ sigma, GlobalBridge25.histogram g n xi r W c sigma : ℕ) : ℝ) *
          entropyNats (fun sigma ↦
            (GlobalBridge25.histogram g n xi r W c sigma : ℝ) /
              ∑ sigma, GlobalBridge25.histogram g n xi r W c sigma)) := by
            apply Finset.prod_le_prod
            · intro c _
              exact Nat.cast_nonneg _
            · intro c _
              exact hfactor c
    _ = Real.exp (GlobalBridge25.qExponent g n xi r W) := by
          unfold GlobalBridge25.qExponent
          simp_rw [Real.exp_sum]

private theorem q_card_filter_prod_sum {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (P : A × X → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ a : A, (Finset.univ.filter fun x ↦ P (a, x)).card := by
  classical
  let e : {z : A × X // P z} ≃ (a : A) × {x : X // P (a, x)} :=
    { toFun := fun z ↦ ⟨z.val.1, z.val.2, z.property⟩
      invFun := fun z ↦ ⟨(z.1, z.2.val), z.2.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (Finset.univ.filter P).card = Fintype.card {z : A × X // P z} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card ((a : A) × {x : X // P (a, x)}) := Fintype.card_congr e
    _ = ∑ a : A, Fintype.card {x : X // P (a, x)} := Fintype.card_sigma
    _ = ∑ a : A, (Finset.univ.filter fun x ↦ P (a, x)).card := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.card_subtype]

private theorem q_real_card_mul_div_cancel (C N : ℕ) (hC : (C : ℝ) ≠ 0) :
    (C : ℝ) * ((N : ℝ) / C) = N := by
  field_simp

private theorem q_finite_globalLawSamples_nonempty {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    (globalLawSamples g n xi r W beta).Nonempty := by
  have hmem := (Finset.mem_filter.mp beta.property).1
  rcases Finset.mem_image.mp hmem with ⟨z, hz, heq⟩
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩

private theorem q_global_joint_cardinality_identities {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    let P := globalPopulation g n xi r
    let C := (Fintype.card (GlobalLawSample g n xi r W) : ℝ)
    C * globalJointP g n xi r W beta =
      ∑ j : {j // j ∈ P.target}, (Nat.card {a : P.Part (GlobalBridge25.side g r W) //
        globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
        globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} : ℝ) ∧
    C * globalJointQ g n xi r W beta =
      ∑ j : {j // j ∈ P.target}, (Nat.card {a : P.Part (GlobalBridge25.side g r W) //
        globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
        globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val ∧
        globalCompatible g n xi r W j.val a} : ℝ) := by
  classical
  dsimp only
  let Cn := Fintype.card (GlobalLawSample g n xi r W)
  have hC : (Cn : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Fintype.card_pos_iff.mpr
      ⟨(q_finite_globalLawSamples_nonempty g xi r W beta).choose⟩)
  constructor
  · unfold globalJointP
    rw [q_real_card_mul_div_cancel Cn _ hC]
    norm_cast
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      GlobalBridge25.side, globalLawSamples, globalContainingSamples,
      Finset.filter_filter, and_assoc] using
      (q_card_filter_prod_sum
        (fun z : {j // j ∈ (globalPopulation g n xi r).target} ×
            (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) ↦
          globalCoarseContains g n xi r (GlobalBridge25.side g r W) z.1.val z.2 ∧
            globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) z.2 = beta.val))
  · unfold globalJointQ
    rw [q_real_card_mul_div_cancel Cn _ hC]
    norm_cast
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      GlobalBridge25.side, globalLawSamples, globalContainingSamples,
      Finset.filter_filter, and_assoc, and_left_comm] using
      (q_card_filter_prod_sum
        (fun z : {j // j ∈ (globalPopulation g n xi r).target} ×
            (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) ↦
          globalCoarseContains g n xi r (GlobalBridge25.side g r W) z.1.val z.2 ∧
            globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) z.2 = beta.val ∧
              globalCompatible g n xi r W z.1.val z.2))

private theorem global_Q_entropy_bound {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    let P := globalPopulation g n xi r
    let A := (P.target.card : ℝ)
    let C := (Fintype.card (GlobalLawSample g n xi r W) : ℝ)
    C * globalJointQ g n xi r W beta ≤
      A * Real.exp (GlobalBridge25.qExponent g n xi r W) := by
  classical
  dsimp only
  rw [(q_global_joint_cardinality_identities g xi r W beta).2]
  calc
    (∑ j : {j // j ∈ (globalPopulation g n xi r).target},
      (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
        globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
        globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val ∧
        globalCompatible g n xi r W j.val a} : ℝ)) ≤
      ∑ _j : {j // j ∈ (globalPopulation g n xi r).target},
        Real.exp (GlobalBridge25.qExponent g n xi r W) := by
          apply Finset.sum_le_sum
          intro j _
          exact global_qfiber_upper g xi r W beta j
    _ = ((globalPopulation g n xi r).target.card : ℝ) *
        Real.exp (GlobalBridge25.qExponent g n xi r W) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_subtype]
          simp

private theorem q_grid_grade_sum {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (S : Side) (u : Shape w)
    (c : Fin (2*w+1)) :
    ∑ sigma ∈ Finset.univ.filter (fun sigma : Chunk w ↦ Parent25.grade sigma = c),
        xi.count S r u sigma =
      if Parent25.coordFin S u = c then
        ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
  classical
  by_cases huc : Parent25.coordFin S u = c
  · rw [if_pos huc, ← xi.total S r u]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro sigma _ hsigma
    apply xi.graded
    intro hgrade
    apply hsigma
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hgc : Parent25.grade sigma = Parent25.coordFin S u := by
      apply Fin.ext
      exact hgrade.trans (global_coordFin_val S u).symm
    exact hgc.trans huc
  · rw [if_neg huc]
    apply Finset.sum_eq_zero
    intro sigma hsigma
    apply xi.graded
    intro hgrade
    apply huc
    have hsigmaGrade := (Finset.mem_filter.mp hsigma).2
    have hcg : Parent25.coordFin S u = Parent25.grade sigma := by
      apply Fin.ext
      exact (global_coordFin_val S u).trans hgrade.symm
    exact hcg.trans hsigmaGrade

private theorem q_projected_global_law_count {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) (c : Fin (2*w+1)) :
    projectedCount Parent25.grade beta.val c =
      ∑ u : Shape w, if Parent25.coordFin (GlobalBridge25.side g r W) u = c then
        ((n : ℚ) * g.joint.prob (r, u)).floor.toNat else 0 := by
  classical
  have hbeta : ∀ sigma, beta.val sigma =
      ∑ u : Shape w, xi.count (GlobalBridge25.side g r W) r u sigma :=
    (Finset.mem_filter.mp beta.property).2
  unfold projectedCount
  simp_rw [hbeta]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact q_grid_grade_sum g xi r (GlobalBridge25.side g r W) u c

private theorem q_global_target_coarse_count {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) (c : Fin (2*w+1)) :
    typeCnt (fun i ↦ Parent25.coordFin (GlobalBridge25.side g r W) (j.val.val i)) c =
      projectedCount Parent25.grade beta.val c := by
  classical
  rw [q_projected_global_law_count g xi r W beta c]
  unfold globalPopulation at j ⊢
  dsimp only at j ⊢
  cases GlobalBridge25.side g r W with
  | X => simpa [typeCnt, Parent25.coordFin] using j.val.property .X c
  | Y => simpa [typeCnt, Parent25.coordFin] using j.val.property .Y c
  | Z => simpa [typeCnt, Parent25.coordFin] using j.val.property .Z c

private theorem q_global_beta_sum {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    ∑ sigma, beta.val sigma = (globalPopulation g n xi r).n := by
  classical
  rcases q_finite_globalLawSamples_nonempty g xi r W beta with ⟨z, hz⟩
  have hzlaw := (Finset.mem_filter.mp hz).2
  unfold globalEmpiricalLaw at hzlaw
  calc
    ∑ sigma, beta.val sigma = ∑ sigma, typeCnt z.2 sigma := by
      apply Finset.sum_congr rfl
      intro sigma _
      exact congrFun hzlaw.symm sigma
    _ = (globalPopulation g n xi r).n := OmegaBound.ADVXXZ.sum_typeCnt z.2

private noncomputable def q_globalProjectionWord {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    {y : Fin (globalPopulation g n xi r).n → Fin (2*w+1) //
      ∀ c, typeCnt y c = projectedCount Parent25.grade beta.val c} :=
  ⟨fun i ↦ Parent25.coordFin (GlobalBridge25.side g r W) (j.val.val i),
    q_global_target_coarse_count g xi r W beta j⟩

private noncomputable def q_globalPFiberEquiv {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} ≃
      ProjectionFiber (globalPopulation g n xi r).n Parent25.grade beta.val
        (fun i ↦ Parent25.coordFin (GlobalBridge25.side g r W) (j.val.val i)) := by
  classical
  refine
    { toFun := fun a ↦ ⟨a.val, ?_, ?_⟩
      invFun := fun x ↦ ⟨x.val, ?_, ?_⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  · intro sigma
    change typeCnt a.val sigma = beta.val sigma
    exact congrFun a.property.2 sigma
  · intro i
    apply Fin.ext
    exact (a.property.1 i).trans (global_coordFin_val _ _).symm
  · intro i
    have hi := congrArg Fin.val (x.property.2 i)
    exact hi.trans (global_coordFin_val _ _)
  · funext sigma
    change typeCnt x.val sigma = beta.val sigma
    exact x.property.1 sigma

private theorem q_global_pfiber_card {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} =
      Nat.card (ProjectionFiber (globalPopulation g n xi r).n Parent25.grade beta.val
        (fun i ↦ Parent25.coordFin (GlobalBridge25.side g r W) (j.val.val i))) :=
  Nat.card_congr (q_globalPFiberEquiv g xi r W beta j)

private theorem q_global_pfiber_lower {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    Real.exp (GlobalBridge25.pExponent g n xi r W beta) /
        (((globalPopulation g n xi r).n : ℝ) + 1) ^ Fintype.card (Chunk w) ≤
      (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
        globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
        globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} : ℝ) := by
  classical
  rw [q_global_pfiber_card g xi r W beta j]
  have h := projectionFiber_entropy_lower Parent25.grade beta.val
    (q_global_beta_sum g xi r W beta) (q_globalProjectionWord g xi r W beta j)
  simpa only [GlobalBridge25.pExponent, Nat.card_eq_fintype_card] using h

private theorem q_global_pfiber_upper {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
      globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} : ℝ) ≤
      Real.exp (GlobalBridge25.pExponent g n xi r W beta) *
        (((globalPopulation g n xi r).n : ℝ) + 1) ^
          Fintype.card (Fin (2*w+1)) := by
  classical
  rw [q_global_pfiber_card g xi r W beta j]
  have h := projectionFiber_entropy_upper Parent25.grade beta.val
    (q_global_beta_sum g xi r W beta) (q_globalProjectionWord g xi r W beta j)
  simpa only [GlobalBridge25.pExponent, Nat.card_eq_fintype_card] using h

private theorem q_global_P_entropy_bounds {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    let P := globalPopulation g n xi r
    let A := (P.target.card : ℝ)
    let C := (Fintype.card (GlobalLawSample g n xi r W) : ℝ)
    let poly := ((P.n : ℝ) + 1) ^ Fintype.card (Chunk w)
    let coarsePoly := ((P.n : ℝ) + 1) ^ Fintype.card (Fin (2*w+1))
    A * Real.exp (GlobalBridge25.pExponent g n xi r W beta) / poly ≤
        C * globalJointP g n xi r W beta ∧
      C * globalJointP g n xi r W beta ≤
        A * Real.exp (GlobalBridge25.pExponent g n xi r W beta) * coarsePoly := by
  classical
  dsimp only
  have hcards := q_global_joint_cardinality_identities g xi r W beta
  have htarget :
      Fintype.card {j // j ∈ (globalPopulation g n xi r).target} =
        (globalPopulation g n xi r).target.card := by
    rw [Fintype.card_subtype]
    simp
  constructor
  · rw [hcards.1]
    calc
      ((globalPopulation g n xi r).target.card : ℝ) *
            Real.exp (GlobalBridge25.pExponent g n xi r W beta) /
            (((globalPopulation g n xi r).n : ℝ) + 1) ^ Fintype.card (Chunk w) =
          ∑ _j : {j // j ∈ (globalPopulation g n xi r).target},
            Real.exp (GlobalBridge25.pExponent g n xi r W beta) /
              (((globalPopulation g n xi r).n : ℝ) + 1) ^
                Fintype.card (Chunk w) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, htarget]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        exact q_global_pfiber_lower g xi r W beta j
  · rw [hcards.1]
    calc
      (∑ j : {j // j ∈ (globalPopulation g n xi r).target},
          (Nat.card {a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r W) //
            globalCoarseContains g n xi r (GlobalBridge25.side g r W) j.val a ∧
            globalEmpiricalLaw g n xi r (GlobalBridge25.side g r W) a = beta.val} : ℝ)) ≤
          ∑ _j : {j // j ∈ (globalPopulation g n xi r).target},
            Real.exp (GlobalBridge25.pExponent g n xi r W beta) *
              (((globalPopulation g n xi r).n : ℝ) + 1) ^
                Fintype.card (Fin (2*w+1)) := by
        apply Finset.sum_le_sum
        intro j _
        exact q_global_pfiber_upper g xi r W beta j
      _ = ((globalPopulation g n xi r).target.card : ℝ) *
          Real.exp (GlobalBridge25.pExponent g n xi r W beta) *
            (((globalPopulation g n xi r).n : ℝ) + 1) ^
              Fintype.card (Fin (2*w+1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, htarget]
        ring

private theorem q_global_jointP_pos {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r W) :
    0 < globalJointP g n xi r W beta := by
  classical
  unfold globalJointP
  apply div_pos
  · exact_mod_cast Finset.card_pos.mpr
      (q_finite_globalLawSamples_nonempty g xi r W beta)
  · exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(q_finite_globalLawSamples_nonempty g xi r W beta).choose⟩

theorem global_PQ_finite_bounds : GlobalBridge25.FiniteBounds := by
  intro w g n xi hxi r W beta
  dsimp only
  have hcards := q_global_joint_cardinality_identities g xi r W beta
  have hP := q_global_P_entropy_bounds g xi r W beta
  refine ⟨q_global_jointP_pos g xi r W beta, hcards.1, hcards.2,
    hP.1, hP.2, global_Q_entropy_bound g xi r W beta⟩

end OmegaBound.ADVXXZGeneral
end
