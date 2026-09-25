import OmegaBound.ADVXXZGeneralCExact42Centre

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

private def ifaceSideApprox42 {q w s : ℕ} (n : Fin s → ℕ)
    (beta : Fin s → SplitDist w) (ε : ℚ)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) : Prop :=
  ∀ t, n t = 0 ∨ ApproxConsistent ε (beta t) (chunkSeq (x t))

private def ifaceSideSupport42 {q w s : ℕ} (n : Fin s → ℕ)
    (beta : Fin s → SplitDist w)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) : Prop :=
  ∀ t a, (beta t).num (chunkOf (x t a)) ≠ 0

private noncomputable instance instDecidablePredIfaceSideApprox42 {q w s : ℕ}
    (n : Fin s → ℕ) (beta : Fin s → SplitDist w) (ε : ℚ) :
    DecidablePred (ifaceSideApprox42 (q := q) n beta ε) := fun _ => Classical.dec _

private noncomputable instance instDecidablePredIfaceSideSupport42 {q w s : ℕ}
    (n : Fin s → ℕ) (beta : Fin s → SplitDist w) :
    DecidablePred (ifaceSideSupport42 (q := q) n beta) := fun _ => Classical.dec _

private def ifacePureZ42 (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ) :
    Tensor3 ℤ ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q) :=
  fun x y z => ∏ t, tensorPower (conZ q w (i t) (j t) (k t)) (n t)
    (x t) (y t) (z t)

private theorem ifaceTermZ_eq_keep42 (q w i j k n : ℕ)
    (bX bY bZ : SplitDist w) (ε : ℚ)
    (x y z : Fin n → Fin w → Idx7 q) :
    ifaceTermZ q w i j k n bX bY bZ ε x y z =
      if n = 0 ∨ (ApproxConsistent ε bX (chunkSeq x) ∧
        ApproxConsistent ε bY (chunkSeq y) ∧
        ApproxConsistent ε bZ (chunkSeq z))
      then tensorPower (conZ q w i j k) n x y z else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [ifaceTermZ, tensorPower]
  · simp [ifaceTermZ, hn]

private theorem prod_ite_eq42 {k : ℕ} {R : Type*} [CommMonoidWithZero R]
    (P : Fin k → Prop) [DecidablePred P] (f : Fin k → R) :
    (∏ i, if P i then f i else 0) = if (∀ i, P i) then ∏ i, f i else 0 := by
  by_cases hP : ∀ i, P i
  · simp [hP]
  · simp only [if_neg hP]
    push_neg at hP
    obtain ⟨i, hi⟩ := hP
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem ifaceZ_normal_form42 (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ)
    (beta : Side → Fin s → SplitDist w) (ε : ℚ) :
    (ifaceZ q w n i j k beta ε).tensor =
      zoP (ifaceSideApprox42 n (beta .X) ε) (ifaceSideApprox42 n (beta .Y) ε)
        (ifaceSideApprox42 n (beta .Z) ε) (ifacePureZ42 q w n i j k) := by
  funext x y z
  change (∏ t, ifaceTermZ q w (i t) (j t) (k t) (n t)
      (beta .X t) (beta .Y t) (beta .Z t) ε (x t) (y t) (z t)) = _
  simp_rw [ifaceTermZ_eq_keep42]
  rw [prod_ite_eq42, zoP_apply]
  have hiff :
      (∀ t, n t = 0 ∨ (ApproxConsistent ε (beta .X t) (chunkSeq (x t)) ∧
        ApproxConsistent ε (beta .Y t) (chunkSeq (y t)) ∧
        ApproxConsistent ε (beta .Z t) (chunkSeq (z t)))) ↔
      ifaceSideApprox42 n (beta .X) ε x ∧ ifaceSideApprox42 n (beta .Y) ε y ∧
        ifaceSideApprox42 n (beta .Z) ε z := by
    constructor
    · intro h
      refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> rcases h t with ht | ht
      · exact Or.inl ht
      · exact Or.inr ht.1
      · exact Or.inl ht
      · exact Or.inr ht.2.1
      · exact Or.inl ht
      · exact Or.inr ht.2.2
    · rintro ⟨hX, hY, hZ⟩ t
      rcases hX t with ht | hX
      · exact Or.inl ht
      rcases hY t with ht | hY
      · exact Or.inl ht
      rcases hZ t with ht | hZ
      · exact Or.inl ht
      exact Or.inr ⟨hX, hY, hZ⟩
  by_cases h : ∀ t, n t = 0 ∨
      (ApproxConsistent ε (beta .X t) (chunkSeq (x t)) ∧
        ApproxConsistent ε (beta .Y t) (chunkSeq (y t)) ∧
        ApproxConsistent ε (beta .Z t) (chunkSeq (z t)))
  · rw [if_pos h, if_pos (hiff.mp h)]
    rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

private theorem supportedIfaceZ_normal_form42 (q w : ℕ) {s : ℕ}
    (n i j k : Fin s → ℕ) (beta : Side → Fin s → SplitDist w) (ε : ℚ) :
    (supportedIfaceZ q w n i j k beta ε).tensor =
      zoP (fun x => ifaceSideSupport42 n (beta .X) x ∧ ifaceSideApprox42 n (beta .X) ε x)
        (fun y => ifaceSideSupport42 n (beta .Y) y ∧ ifaceSideApprox42 n (beta .Y) ε y)
        (fun z => ifaceSideSupport42 n (beta .Z) z ∧ ifaceSideApprox42 n (beta .Z) ε z)
        (ifacePureZ42 q w n i j k) := by
  unfold supportedIfaceZ
  rw [ifaceZ_normal_form42, zoP_zoP]
  funext x y z
  simp only [zoP_apply]
  by_cases h :
      (ifaceSideSupport42 n (beta .X) x ∧ ifaceSideApprox42 n (beta .X) ε x) ∧
      (ifaceSideSupport42 n (beta .Y) y ∧ ifaceSideApprox42 n (beta .Y) ε y) ∧
      (ifaceSideSupport42 n (beta .Z) z ∧ ifaceSideApprox42 n (beta .Z) ε z)
  · simp only [ifaceSideSupport42] at h ⊢
    rw [if_pos h, if_pos h]
  · have h' : ¬ (((∀ t a, (beta .X t).num (chunkOf (x t a)) ≠ 0) ∧
          ifaceSideApprox42 n (beta .X) ε x) ∧
        ((∀ t a, (beta .Y t).num (chunkOf (y t a)) ≠ 0) ∧
          ifaceSideApprox42 n (beta .Y) ε y) ∧
        ((∀ t a, (beta .Z t).num (chunkOf (z t a)) ≠ 0) ∧
          ifaceSideApprox42 n (beta .Z) ε z)) := by
        simpa only [ifaceSideSupport42] using h
    rw [if_neg h', if_neg h]

private theorem prob_ne_zero_iff_num_ne_zero42 {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) : P.prob i ≠ 0 ↔ P.num i ≠ 0 := by
  simp [RatDist.prob, P.den_pos.ne']

private theorem ifaceSideApprox_iff_of_prob42 {q w s : ℕ} (n : Fin s → ℕ)
    (beta gamma : Fin s → SplitDist w) (ε : ℚ)
    (hprob : ∀ t σ, (beta t).prob σ = (gamma t).prob σ)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) :
    ifaceSideApprox42 n beta ε x ↔ ifaceSideApprox42 n gamma ε x := by
  unfold ifaceSideApprox42 ApproxConsistent
  constructor <;> intro h t <;> rcases h t with ht | ht
  · exact Or.inl ht
  · exact Or.inr (fun σ => by simpa only [hprob t σ] using ht σ)
  · exact Or.inl ht
  · exact Or.inr (fun σ => by simpa only [hprob t σ] using ht σ)

private theorem ifaceSideSupport_iff_of_prob42 {q w s : ℕ} (n : Fin s → ℕ)
    (beta gamma : Fin s → SplitDist w)
    (hprob : ∀ t σ, (beta t).prob σ = (gamma t).prob σ)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) :
    ifaceSideSupport42 n beta x ↔ ifaceSideSupport42 n gamma x := by
  unfold ifaceSideSupport42
  constructor <;> intro h t a
  · rw [← (prob_ne_zero_iff_num_ne_zero42 (gamma t) _)]
    rw [← hprob]
    exact (prob_ne_zero_iff_num_ne_zero42 (beta t) _).2 (h t a)
  · rw [← (prob_ne_zero_iff_num_ne_zero42 (beta t) _)]
    rw [hprob]
    exact (prob_ne_zero_iff_num_ne_zero42 (gamma t) _).2 (h t a)

private theorem ifaceZ_tensor_eq_of_prob42 (q w : ℕ) {s : ℕ}
    (n i j k : Fin s → ℕ) (beta gamma : Side → Fin s → SplitDist w) (ε : ℚ)
    (hprob : ∀ W t σ, (beta W t).prob σ = (gamma W t).prob σ) :
    (ifaceZ q w n i j k beta ε).tensor = (ifaceZ q w n i j k gamma ε).tensor := by
  rw [ifaceZ_normal_form42, ifaceZ_normal_form42]
  funext x y z
  simp only [zoP_apply]
  have hiff :
      (ifaceSideApprox42 n (beta .X) ε x ∧ ifaceSideApprox42 n (beta .Y) ε y ∧
        ifaceSideApprox42 n (beta .Z) ε z) ↔
      (ifaceSideApprox42 n (gamma .X) ε x ∧ ifaceSideApprox42 n (gamma .Y) ε y ∧
        ifaceSideApprox42 n (gamma .Z) ε z) :=
    and_congr (ifaceSideApprox_iff_of_prob42 n _ _ ε (hprob .X) x)
      (and_congr (ifaceSideApprox_iff_of_prob42 n _ _ ε (hprob .Y) y)
        (ifaceSideApprox_iff_of_prob42 n _ _ ε (hprob .Z) z))
  by_cases h : ifaceSideApprox42 n (beta .X) ε x ∧
      ifaceSideApprox42 n (beta .Y) ε y ∧ ifaceSideApprox42 n (beta .Z) ε z
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

private theorem supportedIfaceZ_tensor_eq_of_prob42 (q w : ℕ) {s : ℕ}
    (n i j k : Fin s → ℕ) (beta gamma : Side → Fin s → SplitDist w) (ε : ℚ)
    (hprob : ∀ W t σ, (beta W t).prob σ = (gamma W t).prob σ) :
    (supportedIfaceZ q w n i j k beta ε).tensor =
      (supportedIfaceZ q w n i j k gamma ε).tensor := by
  rw [supportedIfaceZ_normal_form42, supportedIfaceZ_normal_form42]
  funext x y z
  simp only [zoP_apply]
  have hs (W : Side)
      (a : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) :
      (ifaceSideSupport42 n (beta W) a ∧ ifaceSideApprox42 n (beta W) ε a) ↔
      (ifaceSideSupport42 n (gamma W) a ∧ ifaceSideApprox42 n (gamma W) ε a) :=
    and_congr (ifaceSideSupport_iff_of_prob42 n _ _ (hprob W) a)
      (ifaceSideApprox_iff_of_prob42 n _ _ ε (hprob W) a)
  have hiff :
      ((ifaceSideSupport42 n (beta .X) x ∧ ifaceSideApprox42 n (beta .X) ε x) ∧
        (ifaceSideSupport42 n (beta .Y) y ∧ ifaceSideApprox42 n (beta .Y) ε y) ∧
        (ifaceSideSupport42 n (beta .Z) z ∧ ifaceSideApprox42 n (beta .Z) ε z)) ↔
      ((ifaceSideSupport42 n (gamma .X) x ∧ ifaceSideApprox42 n (gamma .X) ε x) ∧
        (ifaceSideSupport42 n (gamma .Y) y ∧ ifaceSideApprox42 n (gamma .Y) ε y) ∧
        (ifaceSideSupport42 n (gamma .Z) z ∧ ifaceSideApprox42 n (gamma .Z) ε z)) :=
    and_congr (hs .X x) (and_congr (hs .Y y) (hs .Z z))
  by_cases h :
      (ifaceSideSupport42 n (beta .X) x ∧ ifaceSideApprox42 n (beta .X) ε x) ∧
      (ifaceSideSupport42 n (beta .Y) y ∧ ifaceSideApprox42 n (beta .Y) ε y) ∧
      (ifaceSideSupport42 n (beta .Z) z ∧ ifaceSideApprox42 n (beta .Z) ε z)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- At the centre grid, the supported empirical parent tensor is the original supported tensor. -/
theorem constituentCentreInput_tensor_eq42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (m : ℕ) (ε : ℚ) :
    (constituentInputZ q (constituentGridParent27 d hd m
      (constituentCentreExactGrid42 d hd hb m)) (b*m) ε).tensor =
      (constituentInputZ q p (b*m) ε).tensor := by
  change (supportedIfaceZ q (w+w) (fun t => p.baseN t * (b*m))
      p.i p.j p.k
      (constituentGridParent27 d hd m (constituentCentreExactGrid42 d hd hb m)).beta ε).tensor =
    (supportedIfaceZ q (w+w) (fun t => p.baseN t * (b*m))
      p.i p.j p.k p.beta ε).tensor
  apply supportedIfaceZ_tensor_eq_of_prob42
  exact fun W t σ => constituentCentreGridParent_prob42 d hd hb m W t σ

private theorem zero_or_approx_iff_counts42 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (P : RatDist ι) (C : ι → ℕ) (hC : ∑ a, C a = n)
    (hprob : 0 < n → ∀ a, P.prob a = (C a : ℚ) / (n : ℚ))
    (x : Fin n → ι) :
    n = 0 ∨ ApproxConsistent 0 P x ↔ ∀ a, ADVXXZ.typeCnt x a = C a := by
  constructor
  · rintro (hn | ha) a
    · have hle : C a ≤ ∑ z, C z :=
        Finset.single_le_sum (fun z _ => Nat.zero_le (C z)) (Finset.mem_univ a)
      rw [hC, hn] at hle
      rw [Nat.eq_zero_of_le_zero hle]
      unfold ADVXXZ.typeCnt
      apply Finset.card_eq_zero.mpr
      exact Finset.filter_false_of_mem fun z _ _ => by
        have hzlt := z.isLt
        omega
    · by_cases hz : n = 0
      · have hle : C a ≤ ∑ z, C z :=
          Finset.single_le_sum (fun z _ => Nat.zero_le (C z)) (Finset.mem_univ a)
        rw [hC, hz] at hle
        rw [Nat.eq_zero_of_le_zero hle]
        unfold ADVXXZ.typeCnt
        apply Finset.card_eq_zero.mpr
        exact Finset.filter_false_of_mem fun z _ _ => by
          have hzlt := z.isLt
          omega
      · have hn : 0 < n := Nat.pos_of_ne_zero hz
        have hp := (consistent_iff_prob P x hn).mp
          ((approxConsistent_zero_iff P x hn).mp ha) a
        rw [emp, hprob hn a] at hp
        have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        field_simp [hnq] at hp
        exact_mod_cast hp
  · intro hc
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [approxConsistent_zero_iff P x hnpos, consistent_iff_prob P x hnpos]
      intro a
      rw [emp, hprob hnpos a, hc a]

private def gridOutputBeta42 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin (Fintype.card (ConstituentTerm p))) : SplitDist w :=
  let i := constituentIndex (p := p) t
  constituentGridBeta27 d m h W i.1 i.2.1 i.2.2

private theorem gridOutputBeta_prob42 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin (Fintype.card (ConstituentTerm p))) (σ : Chunk w)
    (hn : 0 < constituentOutN d.toPaper m t) :
    (gridOutputBeta42 d m h W t).prob σ =
      ((h.val t W σ).val : ℚ) / (constituentOutN d.toPaper m t : ℚ) := by
  let e := Fintype.equivFin (ConstituentTerm p)
  generalize hi : constituentIndex (p := p) t = i
  rcases i with ⟨ti,r,u⟩
  have ht : t = e ⟨ti,r,u⟩ := by
    have hx := congrArg e hi
    simpa only [constituentIndex, e, Equiv.apply_symm_apply] using hx
  subst t
  unfold gridOutputBeta42
  have hei : constituentIndex (p := p) (e ⟨ti,r,u⟩) = ⟨ti,r,u⟩ :=
    (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨ti,r,u⟩
  rw [hei]
  exact constituentGridBeta27_prob_pos d m h W ti r u σ hn

private def gridOutputKeep42 {q w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m) (W : Side)
    (x : (t : Fin (Fintype.card (ConstituentTerm p))) →
      Fin (constituentOutN d.toPaper m t) → Fin w → Idx7 q) : Prop :=
  ∀ t σ, ADVXXZ.typeCnt (chunkSeq (x t)) σ = (h.val t W σ).val

private noncomputable instance instDecidablePredGridOutputKeep42 {q w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (W : Side) :
    DecidablePred (gridOutputKeep42 (q := q) d m h W) := fun _ => Classical.dec _

private theorem gridOutputKeep_iff_ifaceSideApprox42 {q w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (W : Side)
    (x : (t : Fin (Fintype.card (ConstituentTerm p))) →
      Fin (constituentOutN d.toPaper m t) → Fin w → Idx7 q) :
    gridOutputKeep42 d m h W x ↔
      ifaceSideApprox42 (constituentOutN d.toPaper m) (gridOutputBeta42 d m h W) 0 x := by
  constructor
  · intro hx t
    exact (zero_or_approx_iff_counts42
      (constituentOutN d.toPaper m t) (gridOutputBeta42 d m h W t)
      (fun σ => (h.val t W σ).val) (h.property.1 t W)
      (fun hn σ => gridOutputBeta_prob42 d m h W t σ hn) (chunkSeq (x t))).mpr (hx t)
  · intro hx t
    exact (zero_or_approx_iff_counts42
      (constituentOutN d.toPaper m t) (gridOutputBeta42 d m h W t)
      (fun σ => (h.val t W σ).val) (h.property.1 t W)
      (fun hn σ => gridOutputBeta_prob42 d m h W t σ hn) (chunkSeq (x t))).mp (hx t)

/-- An exact constituent grid tensor is exactly the zero-tolerance output of its grid spec. -/
theorem constituentGridTensor_tensor_eq_output42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (h : ConstituentExactGrid27 d m) :
    (constituentGridTensorZ27 q d m h).tensor =
      (constituentOutputZ q (constituentGridSpec27 d hd m h) m 0).tensor := by
  have hgrid : (constituentGridTensorZ27 q d m h).tensor =
      zoP (gridOutputKeep42 d m h .X) (gridOutputKeep42 d m h .Y)
        (gridOutputKeep42 d m h .Z)
        (ifacePureZ42 q w (constituentOutN d.toPaper m)
          (constituentOutI (p := p)) (constituentOutJ (p := p))
          (constituentOutK (p := p))) := by
    funext x y z
    simp only [constituentGridTensorZ27, zoP_apply, gridOutputKeep42, ifacePureZ42]
  have hnormal := ifaceZ_normal_form42 q w (constituentOutN d.toPaper m)
    (constituentOutI (p := p)) (constituentOutJ (p := p))
    (constituentOutK (p := p)) (gridOutputBeta42 d m h) 0
  have houtput :
      (constituentOutputZ q (constituentGridSpec27 d hd m h) m 0).tensor =
        (ifaceZ q w (constituentOutN d.toPaper m)
          (constituentOutI (p := p)) (constituentOutJ (p := p))
          (constituentOutK (p := p)) (gridOutputBeta42 d m h) 0).tensor := rfl
  rw [hgrid, houtput, hnormal]
  funext x y z
  simp only [zoP_apply]
  have hiff := and_congr (gridOutputKeep_iff_ifaceSideApprox42 d m h .X x)
    (and_congr (gridOutputKeep_iff_ifaceSideApprox42 d m h .Y y)
      (gridOutputKeep_iff_ifaceSideApprox42 d m h .Z z))
  by_cases hk : gridOutputKeep42 d m h .X x ∧ gridOutputKeep42 d m h .Y y ∧
      gridOutputKeep42 d m h .Z z
  · rw [if_pos hk, if_pos (hiff.mp hk)]
  · rw [if_neg hk, if_neg (fun h' => hk (hiff.mpr h'))]

/-- The centre grid tensor is exactly the original fixed-spec exact output. -/
theorem constituentCentreGridTensor_eq_output42 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) (m : ℕ) :
    (constituentGridTensorZ27 q d m (constituentCentreExactGrid42 d hd hb m)).tensor =
      (constituentOutputZ q d m 0).tensor := by
  rw [constituentGridTensor_tensor_eq_output42 q d hd]
  change (ifaceZ q w (constituentOutN d.toPaper m)
      (constituentOutI (p := p)) (constituentOutJ (p := p))
      (constituentOutK (p := p))
      (fun W i => gridOutputBeta42 d m (constituentCentreExactGrid42 d hd hb m) W i) 0).tensor =
    (ifaceZ q w (constituentOutN d.toPaper m)
      (constituentOutI (p := p)) (constituentOutJ (p := p))
      (constituentOutK (p := p)) (constituentOutBeta d.toPaper) 0).tensor
  apply ifaceZ_tensor_eq_of_prob42
  intro W i σ
  let a := constituentIndex (p := p) i
  have hi : Fintype.equivFin (ConstituentTerm p) a = i := by simp [a, constituentIndex]
  have ha : (⟨a.1,a.2.1,a.2.2⟩ : ConstituentTerm p) = a := by
    rcases a with ⟨t,r,u⟩
    rfl
  rw [← hi]
  unfold gridOutputBeta42
  dsimp only
  have hia : constituentIndex (p := p) (Fintype.equivFin (ConstituentTerm p) a) = a :=
    (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply a
  rw [hia]
  rw [constituentCentreGridBeta_prob42]
  change (d.betaChild W a.1 a.2.1 a.2.2).prob σ =
    (d.betaChild W
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).1
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).2.1
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).2.2).prob σ
  rw [hia]

end
end OmegaBound.ADVXXZGeneral
end
