import OmegaBound.ADVXXZGeneralCExact36Repair

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def ifaceSideApprox {q w s : ℕ} (n : Fin s → ℕ)
    (b : Fin s → SplitDist w) (ε : ℚ)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) : Prop :=
  ∀ t, n t = 0 ∨ ApproxConsistent ε (b t) (chunkSeq (x t))

private def ifaceSideSupport {q w s : ℕ} (n : Fin s → ℕ)
    (b : Fin s → SplitDist w)
    (x : (t : Fin s) → Fin (n t) → Fin w → Idx7 q) : Prop :=
  ∀ t a, (b t).num (chunkOf (x t a)) ≠ 0

private noncomputable instance instDecidablePredIfaceSideApprox {q w s : ℕ}
    (n : Fin s → ℕ) (b : Fin s → SplitDist w) (ε : ℚ) :
    DecidablePred (ifaceSideApprox (q := q) n b ε) := fun _ ↦ Classical.dec _

private noncomputable instance instDecidablePredIfaceSideSupport {q w s : ℕ}
    (n : Fin s → ℕ) (b : Fin s → SplitDist w) :
    DecidablePred (ifaceSideSupport (q := q) n b) := fun _ ↦ Classical.dec _

private def ifacePureZ (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ) :
    Tensor3 ℤ ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q)
      ((t : Fin s) → Fin (n t) → Fin w → Idx7 q) :=
  fun x y z ↦ ∏ t, tensorPower (conZ q w (i t) (j t) (k t)) (n t) (x t) (y t) (z t)

private theorem ifaceTermZ_eq_keep (q w i j k n : ℕ) (bX bY bZ : SplitDist w)
    (ε : ℚ) (x y z : Fin n → Fin w → Idx7 q) :
    ifaceTermZ q w i j k n bX bY bZ ε x y z =
      if n = 0 ∨ (ApproxConsistent ε bX (chunkSeq x) ∧
        ApproxConsistent ε bY (chunkSeq y) ∧
        ApproxConsistent ε bZ (chunkSeq z))
      then tensorPower (conZ q w i j k) n x y z else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [ifaceTermZ, tensorPower]
  · simp [ifaceTermZ, hn]

private theorem prod_ite_eq {k : ℕ} {R : Type*} [CommMonoidWithZero R]
    (P : Fin k → Prop) [DecidablePred P] (f : Fin k → R) :
    (∏ i, if P i then f i else 0) = if (∀ i, P i) then ∏ i, f i else 0 := by
  by_cases hP : ∀ i, P i
  · simp [hP]
  · simp only [if_neg hP]
    push_neg at hP
    obtain ⟨i, hi⟩ := hP
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem ifaceZ_normal_form (q w : ℕ) {s : ℕ} (n i j k : Fin s → ℕ)
    (beta : Side → Fin s → SplitDist w) (ε : ℚ) :
    (ifaceZ q w n i j k beta ε).tensor =
      zoP (ifaceSideApprox n (beta .X) ε) (ifaceSideApprox n (beta .Y) ε)
        (ifaceSideApprox n (beta .Z) ε) (ifacePureZ q w n i j k) := by
  funext x y z
  change (∏ t, ifaceTermZ q w (i t) (j t) (k t) (n t)
      (beta .X t) (beta .Y t) (beta .Z t) ε (x t) (y t) (z t)) = _
  simp_rw [ifaceTermZ_eq_keep]
  rw [prod_ite_eq, zoP_apply]
  have hiff :
      (∀ t, n t = 0 ∨ (ApproxConsistent ε (beta .X t) (chunkSeq (x t)) ∧
        ApproxConsistent ε (beta .Y t) (chunkSeq (y t)) ∧
        ApproxConsistent ε (beta .Z t) (chunkSeq (z t)))) ↔
      ifaceSideApprox n (beta .X) ε x ∧ ifaceSideApprox n (beta .Y) ε y ∧
        ifaceSideApprox n (beta .Z) ε z := by
    constructor
    · intro h
      refine ⟨fun t ↦ ?_, fun t ↦ ?_, fun t ↦ ?_⟩ <;>
        rcases h t with ht | ht
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
  · rw [if_neg h, if_neg (fun h' ↦ h (hiff.mpr h'))]


private theorem supportedIfaceZ_normal_form (q w : ℕ) {s : ℕ}
    (n i j k : Fin s → ℕ) (beta : Side → Fin s → SplitDist w) (ε : ℚ) :
    (supportedIfaceZ q w n i j k beta ε).tensor =
      zoP (fun x ↦ ifaceSideSupport n (beta .X) x ∧ ifaceSideApprox n (beta .X) ε x)
        (fun y ↦ ifaceSideSupport n (beta .Y) y ∧ ifaceSideApprox n (beta .Y) ε y)
        (fun z ↦ ifaceSideSupport n (beta .Z) z ∧ ifaceSideApprox n (beta .Z) ε z)
        (ifacePureZ q w n i j k) := by
  unfold supportedIfaceZ
  rw [ifaceZ_normal_form, zoP_zoP]
  funext x y z
  simp only [zoP_apply]
  by_cases h :
      (ifaceSideSupport n (beta .X) x ∧ ifaceSideApprox n (beta .X) ε x) ∧
      (ifaceSideSupport n (beta .Y) y ∧ ifaceSideApprox n (beta .Y) ε y) ∧
      (ifaceSideSupport n (beta .Z) z ∧ ifaceSideApprox n (beta .Z) ε z)
  · simp only [ifaceSideSupport] at h ⊢
    rw [if_pos h, if_pos h]
  · have h' : ¬ (((∀ t a, (beta .X t).num (chunkOf (x t a)) ≠ 0) ∧
          ifaceSideApprox n (beta .X) ε x) ∧
        ((∀ t a, (beta .Y t).num (chunkOf (y t a)) ≠ 0) ∧
          ifaceSideApprox n (beta .Y) ε y) ∧
        ((∀ t a, (beta .Z t).num (chunkOf (z t a)) ≠ 0) ∧
          ifaceSideApprox n (beta .Z) ε z)) := by
        simpa only [ifaceSideSupport] using h
    rw [if_neg h', if_neg h]


private theorem zoP_restricts_of_sub_of_imp
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (pX : X' → Prop) [DecidablePred pX] (pY : Y' → Prop)
    [DecidablePred pY] (pZ : Z' → Prop) [DecidablePred pZ]
    (qX : X → Prop) [DecidablePred qX] (qY : Y → Prop) [DecidablePred qY]
    (qZ : Z → Prop) [DecidablePred qZ] (U : Tensor3 ℤ X' Y' Z')
    (T : Tensor3 ℤ X Y Z) (fX : X' → X) (fY : Y' → Y) (fZ : Z' → Z)
    (hX : ∀ x, pX x → qX (fX x)) (hY : ∀ y, pY y → qY (fY y))
    (hZ : ∀ z, pZ z → qZ (fZ z))
    (hT : ∀ x y z, pX x → pY y → pZ z → U x y z = T (fX x) (fY y) (fZ z)) :
    Restricts (zoP pX pY pZ U) (zoP qX qY qZ T) := by
  let V : Tensor3 ℤ X' Y' Z' := fun x y z ↦ zoP qX qY qZ T (fX x) (fY y) (fZ z)
  have heq : zoP pX pY pZ U = zoP pX pY pZ V := by
    funext x y z
    simp only [zoP_apply]
    by_cases hp : pX x ∧ pY y ∧ pZ z
    · rw [if_pos hp, if_pos hp, hT x y z hp.1 hp.2.1 hp.2.2]
      have hq : qX (fX x) ∧ qY (fY y) ∧ qZ (fZ z) :=
        ⟨hX x hp.1, hY y hp.2.1, hZ z hp.2.2⟩
      simp only [V, zoP_apply, if_pos hq]
    · rw [if_neg hp, if_neg hp]
  rw [heq]
  exact Restricts.trans (zoP_restricts pX pY pZ V)
    (restricts_of_sub fX fY fZ (fun _ _ _ ↦ rfl))


private theorem zero_or_approx_iff_counts36 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (P : RatDist ι) (C : ι → ℕ) (hC : ∑ a, C a = n)
    (hprob : 0 < n → ∀ a, P.prob a = (C a : ℚ) / (n : ℚ))
    (x : Fin n → ι) :
    n = 0 ∨ ApproxConsistent 0 P x ↔ ∀ a, ADVXXZ.typeCnt x a = C a := by
  constructor
  · rintro (hn | ha) a
    · have hle : C a ≤ ∑ z, C z :=
        Finset.single_le_sum (fun z _ => Nat.zero_le (C z)) (Finset.mem_univ a)
      rw [hC, hn] at hle
      have hzero : C a = 0 := Nat.eq_zero_of_le_zero hle
      rw [hzero]
      unfold ADVXXZ.typeCnt
      apply Finset.card_eq_zero.mpr
      exact Finset.filter_false_of_mem fun z _ _ => by
        have hzlt := z.isLt
        omega
    · by_cases hz : n = 0
      · have hle : C a ≤ ∑ z, C z :=
          Finset.single_le_sum (fun z _ => Nat.zero_le (C z)) (Finset.mem_univ a)
        rw [hC, hz] at hle
        have hzero : C a = 0 := Nat.eq_zero_of_le_zero hle
        rw [hzero]
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

private def gridOutputBeta36 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin (Fintype.card (ConstituentTerm p))) : SplitDist w :=
  let i := constituentIndex (p := p) t
  constituentGridBeta27 d m h W i.1 i.2.1 i.2.2

private theorem gridOutputBeta36_prob {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin (Fintype.card (ConstituentTerm p))) (σ : Chunk w)
    (hn : 0 < constituentOutN d.toPaper m t) :
    (gridOutputBeta36 d m h W t).prob σ =
      ((h.val t W σ).val : ℚ) / (constituentOutN d.toPaper m t : ℚ) := by
  let e := Fintype.equivFin (ConstituentTerm p)
  generalize hi : constituentIndex (p := p) t = i
  rcases i with ⟨ti, r, u⟩
  have ht : t = e ⟨ti, r, u⟩ := by
    have hx := congrArg e hi
    simpa only [constituentIndex, e, Equiv.apply_symm_apply] using hx
  subst t
  unfold gridOutputBeta36
  rw [show constituentIndex (p := p) (e ⟨ti, r, u⟩) = ⟨ti, r, u⟩ by
    simpa only [constituentIndex, e] using
      (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨ti, r, u⟩]
  exact constituentGridBeta27_prob_pos d m h W ti r u σ hn

private def gridOutputKeep36 {q w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side)
    (x : (t : Fin (Fintype.card (ConstituentTerm p))) →
      Fin (constituentOutN d.toPaper m t) → Fin w → Idx7 q) : Prop :=
  ∀ t σ, ADVXXZ.typeCnt (chunkSeq (x t)) σ = (h.val t W σ).val

private noncomputable instance instDecidablePredGridOutputKeep36 {q w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (W : Side) :
    DecidablePred (gridOutputKeep36 (q := q) d m h W) := fun _ ↦ Classical.dec _

private theorem gridOutputKeep_iff_ifaceSideApprox36 {q w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (W : Side)
    (x : (t : Fin (Fintype.card (ConstituentTerm p))) →
      Fin (constituentOutN d.toPaper m t) → Fin w → Idx7 q) :
    gridOutputKeep36 d m h W x ↔
      ifaceSideApprox (constituentOutN d.toPaper m) (gridOutputBeta36 d m h W) 0 x := by
  constructor
  · intro hx t
    exact (zero_or_approx_iff_counts36
      (constituentOutN d.toPaper m t) (gridOutputBeta36 d m h W t)
      (fun σ => (h.val t W σ).val) (h.property.1 t W)
      (fun hn σ => gridOutputBeta36_prob d m h W t σ hn) (chunkSeq (x t))).mpr (hx t)
  · intro hx t
    exact (zero_or_approx_iff_counts36
      (constituentOutN d.toPaper m t) (gridOutputBeta36 d m h W t)
      (fun σ => (h.val t W σ).val) (h.property.1 t W)
      (fun hn σ => gridOutputBeta36_prob d m h W t σ hn) (chunkSeq (x t))).mp (hx t)

private theorem constituentGridTensor_tensor_eq_output36 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (h : ConstituentExactGrid27 d m) :
    (constituentGridTensorZ27 q d m h).tensor =
      (constituentOutputZ q (constituentGridSpec27 d hd m h) m 0).tensor := by
  classical
  have hgrid : (constituentGridTensorZ27 q d m h).tensor =
      zoP (gridOutputKeep36 d m h .X) (gridOutputKeep36 d m h .Y)
      (gridOutputKeep36 d m h .Z)
        (ifacePureZ q w (constituentOutN d.toPaper m)
        (constituentOutI (p := p)) (constituentOutJ (p := p))
        (constituentOutK (p := p))) := by
    funext x y z
    simp only [constituentGridTensorZ27, zoP_apply, gridOutputKeep36, ifacePureZ]
  have hnormal := ifaceZ_normal_form q w (constituentOutN d.toPaper m)
    (constituentOutI (p := p)) (constituentOutJ (p := p))
    (constituentOutK (p := p)) (gridOutputBeta36 d m h) 0
  have houtput :
      (constituentOutputZ q (constituentGridSpec27 d hd m h) m 0).tensor =
        (ifaceZ q w (constituentOutN d.toPaper m)
          (constituentOutI (p := p)) (constituentOutJ (p := p))
          (constituentOutK (p := p)) (gridOutputBeta36 d m h) 0).tensor := by
    rfl
  rw [hgrid, houtput, hnormal]
  funext x y z
  simp only [zoP_apply]
  have hiff :
      (gridOutputKeep36 d m h .X x ∧ gridOutputKeep36 d m h .Y y ∧
        gridOutputKeep36 d m h .Z z) ↔
      (ifaceSideApprox (constituentOutN d.toPaper m) (gridOutputBeta36 d m h .X) 0 x ∧
        ifaceSideApprox (constituentOutN d.toPaper m) (gridOutputBeta36 d m h .Y) 0 y ∧
        ifaceSideApprox (constituentOutN d.toPaper m) (gridOutputBeta36 d m h .Z) 0 z) :=
    and_congr (gridOutputKeep_iff_ifaceSideApprox36 d m h .X x)
      (and_congr (gridOutputKeep_iff_ifaceSideApprox36 d m h .Y y)
        (gridOutputKeep_iff_ifaceSideApprox36 d m h .Z z))
  by_cases hk : gridOutputKeep36 d m h .X x ∧ gridOutputKeep36 d m h .Y y ∧
      gridOutputKeep36 d m h .Z z
  · rw [if_pos hk, if_pos (hiff.mp hk)]
  · rw [if_neg hk, if_neg (fun h' => hk (hiff.mpr h'))]

-- P/constituent.tex:120,138-149;
-- H/analysis_constituent.tex:117-122. Target is on the LEFT of Restricts.
theorem constituent_grid_output_restricts36 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (h : ConstituentExactGrid27 d m) :
  Restricts (constituentGridTensorZ27 q d m h).tensor
    (constituentOutputZ q (constituentGridSpec27 d hd m h) m 0).tensor := by
  classical
  rw [constituentGridTensor_tensor_eq_output36 q d hd m h]
  exact ADVXXZ.restricts_of_sub id id id (fun _ _ _ => rfl)

private theorem ratDist_prob_le_one36 {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) : P.prob i ≤ 1 := by
  calc
    P.prob i ≤ ∑ j, P.prob j :=
      Finset.single_le_sum (fun j _ ↦ P.prob_nonneg j) (Finset.mem_univ i)
    _ = 1 := P.sum_prob

private theorem ratDist_convex_abs_le36 {A : Type*} [Fintype A]
    (P : RatDist A) (f g : A → ℚ) (e : ℚ) (he : 0 ≤ e)
    (hfg : ∀ a, |f a - g a| ≤ e) :
    |∑ a, P.prob a * f a - ∑ a, P.prob a * g a| ≤ e := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (P.prob a * f a - P.prob a * g a)|
        ≤ ∑ a, |P.prob a * f a - P.prob a * g a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.prob a * |f a - g a| := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg (P.prob_nonneg a)]
    _ ≤ ∑ a, P.prob a * e := by
      exact Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left (hfg a) (P.prob_nonneg a)
    _ = e := by
      rw [← Finset.sum_mul, P.sum_prob, one_mul]

private theorem abs_mul_sub_mul_le_two36
    (a b c d e : ℚ) (he : 0 ≤ e)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hbd : |b - d| ≤ e) (hac : |a - c| ≤ e) :
    |a * b - c * d| ≤ 2 * e := by
  calc
    |a * b - c * d| = |a * (b - d) + d * (a - c)| := by congr 1 <;> ring
    _ ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = a * |b - d| + d * |a - c| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hd0]
    _ ≤ a * e + d * e :=
      add_le_add (mul_le_mul_of_nonneg_left hbd ha0)
        (mul_le_mul_of_nonneg_left hac hd0)
    _ ≤ 2 * e := by nlinarith

private theorem gridChild_close36 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (e : ℚ) (m : ℕ)
    (h : ConstituentFullGrid27 d m e) (W : Side) (t : Fin s) (r : Fin 6)
    (u : ChildShape p t) (σ : Chunk w) (he : 0 ≤ e) :
    |(constituentGridBeta27 d m h.val W t r u).prob σ -
      (d.betaChild W t r u).prob σ| ≤ e := by
  let i := Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩
  by_cases hn : 0 < constituentOutN d.toPaper m i
  · rw [constituentGridBeta27_prob_pos d m h.val W t r u σ hn]
    have hh := h.property i W hn σ
    have hi : constituentIndex (p := p) i = ⟨t, r, u⟩ := by
      simpa only [i, constituentIndex] using
        (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨t, r, u⟩
    change |↑↑(h.val.val i W σ) / ↑(constituentOutN d.toPaper m i) -
      (d.betaChild W (constituentIndex i).1 (constituentIndex i).2.1
        (constituentIndex i).2.2).prob σ| ≤ e at hh
    rw [hi] at hh
    exact hh
  · unfold constituentGridBeta27
    dsimp only
    rw [dif_neg hn, sub_self, abs_zero]
    exact he

private theorem gridRegion_close36 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) (h : ConstituentFullGrid27 d m e)
    (W : Side) (t : Fin s) (r : Fin 6) (σ : Chunk (w + w)) :
    |(constituentGridRegionBeta27 d m h.val W t r).prob σ -
      (d.betaRegion W t r).prob σ| ≤ 2 * e := by
  rw [constituentGridSpec27_pair_mixture, hd.pair_mixture]
  simp only [mul_assoc]
  refine ratDist_convex_abs_le36 (P := d.alpha t r)
    (f := fun u =>
      (constituentGridBeta27 d m h.val W t r u).prob (leftHalf σ) *
        (constituentGridBeta27 d m h.val W t r (complement p t u)).prob (rightHalf σ))
    (g := fun u => (d.betaChild W t r u).prob (leftHalf σ) *
      (d.betaChild W t r (complement p t u)).prob (rightHalf σ))
    (e := 2 * e) (mul_nonneg (by norm_num) he) ?_
  intro u
  let gu := constituentGridBeta27 d m h.val W t r u
  let gc := constituentGridBeta27 d m h.val W t r (complement p t u)
  let ou := d.betaChild W t r u
  let oc := d.betaChild W t r (complement p t u)
  exact abs_mul_sub_mul_le_two36
    (gu.prob (leftHalf σ)) (gc.prob (rightHalf σ))
    (ou.prob (leftHalf σ)) (oc.prob (rightHalf σ)) e he
    (gu.prob_nonneg _) (ratDist_prob_le_one36 gu _)
    (oc.prob_nonneg _) (ratDist_prob_le_one36 oc _)
    (gridChild_close36 d e m h W t r (complement p t u) (rightHalf σ) he)
    (gridChild_close36 d e m h W t r u (leftHalf σ) he)

private theorem gridParent_close36 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) (h : ConstituentFullGrid27 d m e)
    (W : Side) (t : Fin s) (σ : Chunk (w + w)) :
    |((constituentGridParent27 d hd m h.val).beta W t).prob σ -
      (p.beta W t).prob σ| ≤ 2 * e := by
  change |(mixtureDist27 (d.A t) (constituentGridRegionBeta27 d m h.val W t)).prob σ -
    (p.beta W t).prob σ| ≤ 2 * e
  rw [mixtureDist27_prob, hd.mixture]
  refine ratDist_convex_abs_le36 (P := d.A t)
    (f := fun r => (constituentGridRegionBeta27 d m h.val W t r).prob σ)
    (g := fun r => (d.betaRegion W t r).prob σ)
    (e := 2 * e) (mul_nonneg (by norm_num) he) ?_
  intro r
  exact gridRegion_close36 d hd e he m h W t r σ

private theorem approxConsistent_grid_to_parent36 {w s b n : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (e : ℚ) (he : 0 ≤ e)
    (m : ℕ) (h : ConstituentFullGrid27 d m e) (W : Side) (t : Fin s)
    (x : Fin n → Chunk (w + w))
    (hx : ApproxConsistent e ((constituentGridParent27 d hd m h.val).beta W t) x) :
    ApproxConsistent (3 * e) (p.beta W t) x := by
  intro σ
  calc
    |emp x σ - (p.beta W t).prob σ| =
        |(emp x σ - ((constituentGridParent27 d hd m h.val).beta W t).prob σ) +
          (((constituentGridParent27 d hd m h.val).beta W t).prob σ -
            (p.beta W t).prob σ)| := by congr 1 <;> ring
    _ ≤ |emp x σ - ((constituentGridParent27 d hd m h.val).beta W t).prob σ| +
        |((constituentGridParent27 d hd m h.val).beta W t).prob σ -
          (p.beta W t).prob σ| := abs_add_le _ _
    _ ≤ e + 2 * e := add_le_add (hx σ) (gridParent_close36 d hd e he m h W t σ)
    _ = 3 * e := by ring

-- H/analysis_constituent.tex:123-125;
-- P/constituent.tex:138-149. Nearness is spent only on this window.
theorem constituent_grid_input_window36 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (e : ℚ) (he : 0 ≤ e)
    (m : ℕ) (h : ConstituentFullGrid27 d m e) :
  Restricts (constituentInputZ q (constituentGridParent27 d hd m h.val) (b*m) e).tensor
    (constituentPlainInputZ q p (b*m) (3*e)).tensor := by
  classical
  unfold constituentInputZ constituentPlainInputZ
  rw [supportedIfaceZ_normal_form, ifaceZ_normal_form]
  refine zoP_restricts_of_sub_of_imp _ _ _ _ _ _ _ _ id id id ?_ ?_ ?_ ?_
  · rintro x ⟨_, hx⟩
    intro t
    rcases hx t with ht | ht
    · exact Or.inl ht
    · exact Or.inr (approxConsistent_grid_to_parent36 d hd e he m h .X t _ ht)
  · rintro y ⟨_, hy⟩
    intro t
    rcases hy t with ht | ht
    · exact Or.inl ht
    · exact Or.inr (approxConsistent_grid_to_parent36 d hd e he m h .Y t _ ht)
  · rintro z ⟨_, hz⟩
    intro t
    rcases hz t with ht | ht
    · exact Or.inl ht
    · exact Or.inr (approxConsistent_grid_to_parent36 d hd e he m h .Z t _ ht)
  · intro _ _ _ _ _ _
    rfl

#print axioms constituent_grid_output_restricts36
#print axioms constituent_grid_input_window36

end OmegaBound.ADVXXZGeneral
