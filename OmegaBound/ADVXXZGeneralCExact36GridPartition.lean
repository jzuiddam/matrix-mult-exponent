import OmegaBound.ADVXXZGeneralCExact36Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem integral36_iff_input29 {w s b m : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) :
    ConstituentIntegral36 d b m ↔ InputInt29 d b m ∧
      ∀ t r, integral ((b : ℚ) * p.baseN t * (d.A t).prob r) := by
  constructor
  · intro h
    exact ⟨⟨h.bpos, h.alphaIntegral, h.countsExact⟩, h.regionIntegral⟩
  · rintro ⟨h, hr⟩
    exact ⟨h.bpos, hr, h.alphaIntegral, h.countsExact⟩


theorem constituent_grid_integral36 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (h : ConstituentExactGrid27 d m) :
  ConstituentIntegral36 (constituentGridSpec27 d hd m h) b m := by
  exact (integral36_iff_input29 _).mpr
    ⟨gridInputInt29 d hd hb m h, fun t r => (hb.2 t r).1⟩

private def blockGlue {k : ℕ} {V : Type*} (n : Fin k → ℕ)
    (x : (r : Fin k) → Fin (n r) → V) : Fin (∑ r, n r) → V :=
  fun i ↦ x (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

private theorem blockGlue_apply {k : ℕ} {V : Type*} (n : Fin k → ℕ)
    (x : (r : Fin k) → Fin (n r) → V) (a : (r : Fin k) × Fin (n r)) :
    blockGlue n x (finSigmaFinEquiv a) = x a.1 a.2 := by
  exact congrArg (fun z : (r : Fin k) × Fin (n r) ↦ x z.1 z.2)
    (finSigmaFinEquiv.symm_apply_apply a)

private def blockGlueCast {k N : ℕ} {V : Type*} (n : Fin k → ℕ)
    (h : ∑ r, n r = N) (x : (r : Fin k) → Fin (n r) → V) : Fin N → V :=
  fun i ↦ blockGlue n x ((finCongr h).symm i)

private theorem typeCnt_blockGlueCast {k N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (n : Fin k → ℕ) (h : ∑ r, n r = N)
    (x : (r : Fin k) → Fin (n r) → ι) (a : ι) :
    ADVXXZ.typeCnt (blockGlueCast n h x) a = ∑ r, ADVXXZ.typeCnt (x r) a := by
  let e : ((r : Fin k) × Fin (n r)) ≃ Fin N := finSigmaFinEquiv.trans (finCongr h)
  simp only [typeCnt_eq_sum]
  rw [← Equiv.sum_comp e (fun i : Fin N ↦ if blockGlueCast n h x i = a then 1 else 0),
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show e ⟨r, i⟩ = (finCongr h) (finSigmaFinEquiv ⟨r, i⟩) by rfl,
    blockGlueCast, Equiv.symm_apply_apply, blockGlue_apply]

private theorem approxConsistent_blockGlueCast {k N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (n : Fin k → ℕ) (hN : ∑ r, n r = N)
    (hNpos : 0 < N) (P : Fin k → RatDist ι) (Q : RatDist ι)
    (hmix : ∀ a, Q.prob a = ∑ r, ((n r : ℕ) : ℚ) / (N : ℚ) * (P r).prob a)
    (ε : ℚ) (x : (r : Fin k) → Fin (n r) → ι)
    (hx : ∀ r, n r = 0 ∨ ApproxConsistent ε (P r) (x r)) :
    ApproxConsistent ε Q (blockGlueCast n hN x) := by
  intro a
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  have hWnn : ∀ r : Fin k, (0 : ℚ) ≤ ((n r : ℕ) : ℚ) / (N : ℚ) := by
    intro r
    positivity
  have hWsum : ∑ r : Fin k, ((n r : ℕ) : ℚ) / (N : ℚ) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, hN, div_self hNQ]
  have hemp : emp (blockGlueCast n hN x) a =
      ∑ r : Fin k, ((n r : ℕ) : ℚ) / (N : ℚ) * emp (x r) a := by
    rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) ↦
      weight_mul_emp (x r) a (N : ℚ), ← Finset.sum_div, ← Nat.cast_sum,
      ← typeCnt_blockGlueCast n hN x a, emp]
  rw [hemp, hmix, ← Finset.sum_sub_distrib]
  calc
    |∑ r : Fin k, (((n r : ℕ) : ℚ) / (N : ℚ) * emp (x r) a -
        ((n r : ℕ) : ℚ) / (N : ℚ) * (P r).prob a)|
        ≤ ∑ r : Fin k, |((n r : ℕ) : ℚ) / (N : ℚ) * emp (x r) a -
          ((n r : ℕ) : ℚ) / (N : ℚ) * (P r).prob a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r : Fin k, ((n r : ℕ) : ℚ) / (N : ℚ) *
          |emp (x r) a - (P r).prob a| := by
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg (hWnn r)]
    _ ≤ ∑ r : Fin k, ((n r : ℕ) : ℚ) / (N : ℚ) * ε := by
      refine Finset.sum_le_sum fun r _ ↦ ?_
      rcases hx r with hr | hr
      · simp [hr]
      · exact mul_le_mul_of_nonneg_left (hr a) (hWnn r)
    _ = ε := by rw [← Finset.sum_mul, hWsum, one_mul]

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

private theorem tensorPower_blockGlueCast {k N : ℕ} {X Y Z : Type*}
    (T : Tensor3 ℤ X Y Z) (n : Fin k → ℕ) (hN : ∑ r, n r = N)
    (x : (r : Fin k) → Fin (n r) → X) (y : (r : Fin k) → Fin (n r) → Y)
    (z : (r : Fin k) → Fin (n r) → Z) :
    (∏ r, tensorPower T (n r) (x r) (y r) (z r)) =
      tensorPower T N (blockGlueCast n hN x) (blockGlueCast n hN y)
        (blockGlueCast n hN z) := by
  simp only [tensorPower]
  let e : ((r : Fin k) × Fin (n r)) ≃ Fin N := finSigmaFinEquiv.trans (finCongr hN)
  calc
    _ = ∏ a : ((r : Fin k) × Fin (n r)), T (x a.1 a.2) (y a.1 a.2) (z a.1 a.2) :=
      (Fintype.prod_sigma _).symm
    _ = _ := by
      have hpoint : ∀ a : ((r : Fin k) × Fin (n r)),
          T (blockGlueCast n hN x (e a)) (blockGlueCast n hN y (e a))
              (blockGlueCast n hN z (e a)) = T (x a.1 a.2) (y a.1 a.2) (z a.1 a.2) := by
        intro a
        change T (blockGlue n x ((finCongr hN).symm ((finCongr hN) (finSigmaFinEquiv a))))
          (blockGlue n y ((finCongr hN).symm ((finCongr hN) (finSigmaFinEquiv a))))
          (blockGlue n z ((finCongr hN).symm ((finCongr hN) (finSigmaFinEquiv a)))) = _
        rw [Equiv.symm_apply_apply, blockGlue_apply, blockGlue_apply, blockGlue_apply]
      calc
        _ = ∏ a : ((r : Fin k) × Fin (n r)),
            T (blockGlueCast n hN x (e a)) (blockGlueCast n hN y (e a))
              (blockGlueCast n hN z (e a)) := by
            exact Finset.prod_congr rfl fun a _ ↦ (hpoint a).symm
        _ = _ := Equiv.prod_comp e (fun i : Fin N ↦
          T (blockGlueCast n hN x i) (blockGlueCast n hN y i)
            (blockGlueCast n hN z i))

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

private def splitBlocks {s k : ℕ}
    (e : Fin s × Fin k ≃ Fin (Fintype.card (Fin s × Fin k)))
    (nr : Fin (Fintype.card (Fin s × Fin k)) → ℕ) {V : Type*}
    (x : (a : Fin (Fintype.card (Fin s × Fin k))) → Fin (nr a) → V)
    (t : Fin s) (r : Fin k) : Fin (nr (e (t, r))) → V :=
  x (e (t, r))

private def glueBlocks {s k : ℕ}
    (e : Fin s × Fin k ≃ Fin (Fintype.card (Fin s × Fin k)))
    (n : Fin s → ℕ) (nr : Fin (Fintype.card (Fin s × Fin k)) → ℕ)
    (hsum : ∀ t, ∑ r, nr (e (t, r)) = n t) {V : Type*}
    (x : (a : Fin (Fintype.card (Fin s × Fin k))) → Fin (nr a) → V)
    (t : Fin s) : Fin (n t) → V :=
  blockGlueCast (fun r ↦ nr (e (t, r))) (hsum t) (splitBlocks e nr x t)

private theorem supportedIfaceZ_partition (q w s k : ℕ)
    (e : Fin s × Fin k ≃ Fin (Fintype.card (Fin s × Fin k)))
    (n : Fin s → ℕ) (nr : Fin (Fintype.card (Fin s × Fin k)) → ℕ)
    (i j l : Fin s → ℕ) (beta : Side → Fin s → SplitDist w)
    (betaR : Side → Fin (Fintype.card (Fin s × Fin k)) → SplitDist w)
    (ε : ℚ) (hsum : ∀ t, ∑ r, nr (e (t, r)) = n t)
    (hmix : ∀ W t, 0 < n t → ∀ a, (beta W t).prob a =
      ∑ r, ((nr (e (t, r)) : ℕ) : ℚ) / (n t : ℚ) * (betaR W (e (t, r))).prob a)
    (hsupport : ∀ W t r, 0 < nr (e (t, r)) → ∀ a,
      (betaR W (e (t, r))).num a ≠ 0 → (beta W t).num a ≠ 0) :
    Restricts
      (supportedIfaceZ q w nr (fun a ↦ i (e.symm a).1) (fun a ↦ j (e.symm a).1)
        (fun a ↦ l (e.symm a).1) betaR ε).tensor
      (supportedIfaceZ q w n i j l beta ε).tensor := by
  classical
  rw [supportedIfaceZ_normal_form, supportedIfaceZ_normal_form]
  refine zoP_restricts_of_sub_of_imp _ _ _ _ _ _ _ _
    (fun x t a c ↦ glueBlocks e n nr hsum x t a c)
    (fun y t a c ↦ glueBlocks e n nr hsum y t a c)
    (fun z t a c ↦ glueBlocks e n nr hsum z t a c) ?_ ?_ ?_ ?_
  · rintro x ⟨hxS, hxA⟩
    constructor
    · intro t a
      let v := (finSigmaFinEquiv.symm ((finCongr (hsum t)).symm a))
      have hvpos : 0 < nr (e (t, v.1)) := Fin.pos_iff_nonempty.mpr ⟨v.2⟩
      apply hsupport .X t v.1 hvpos (chunkOf (glueBlocks e n nr hsum x t a))
      simpa only [glueBlocks, splitBlocks, blockGlueCast, blockGlue, v,
        Equiv.symm_apply_apply] using hxS (e (t, v.1)) v.2
    · intro t
      by_cases ht : n t = 0
      · exact Or.inl ht
      · exact Or.inr (approxConsistent_blockGlueCast
          (fun r ↦ nr (e (t, r))) (hsum t) (Nat.pos_of_ne_zero ht)
          (fun r ↦ betaR .X (e (t, r))) (beta .X t) (hmix .X t (Nat.pos_of_ne_zero ht)) ε
          (fun r i ↦ chunkSeq (splitBlocks e nr x t r) i)
          (fun r ↦ hxA (e (t, r))))
  · rintro y ⟨hyS, hyA⟩
    constructor
    · intro t a
      let v := (finSigmaFinEquiv.symm ((finCongr (hsum t)).symm a))
      have hvpos : 0 < nr (e (t, v.1)) := Fin.pos_iff_nonempty.mpr ⟨v.2⟩
      apply hsupport .Y t v.1 hvpos (chunkOf (glueBlocks e n nr hsum y t a))
      simpa only [glueBlocks, splitBlocks, blockGlueCast, blockGlue, v,
        Equiv.symm_apply_apply] using hyS (e (t, v.1)) v.2
    · intro t
      by_cases ht : n t = 0
      · exact Or.inl ht
      · exact Or.inr (approxConsistent_blockGlueCast
          (fun r ↦ nr (e (t, r))) (hsum t) (Nat.pos_of_ne_zero ht)
          (fun r ↦ betaR .Y (e (t, r))) (beta .Y t) (hmix .Y t (Nat.pos_of_ne_zero ht)) ε
          (fun r i ↦ chunkSeq (splitBlocks e nr y t r) i)
          (fun r ↦ hyA (e (t, r))))
  · rintro z ⟨hzS, hzA⟩
    constructor
    · intro t a
      let v := (finSigmaFinEquiv.symm ((finCongr (hsum t)).symm a))
      have hvpos : 0 < nr (e (t, v.1)) := Fin.pos_iff_nonempty.mpr ⟨v.2⟩
      apply hsupport .Z t v.1 hvpos (chunkOf (glueBlocks e n nr hsum z t a))
      simpa only [glueBlocks, splitBlocks, blockGlueCast, blockGlue, v,
        Equiv.symm_apply_apply] using hzS (e (t, v.1)) v.2
    · intro t
      by_cases ht : n t = 0
      · exact Or.inl ht
      · exact Or.inr (approxConsistent_blockGlueCast
          (fun r ↦ nr (e (t, r))) (hsum t) (Nat.pos_of_ne_zero ht)
          (fun r ↦ betaR .Z (e (t, r))) (beta .Z t) (hmix .Z t (Nat.pos_of_ne_zero ht)) ε
          (fun r i ↦ chunkSeq (splitBlocks e nr z t r) i)
          (fun r ↦ hzA (e (t, r))))
  · intro x y z _ _ _
    change (∏ a, tensorPower (conZ q w (i (e.symm a).1) (j (e.symm a).1)
      (l (e.symm a).1)) (nr a) (x a) (y a) (z a)) = _
    rw [← Equiv.prod_comp e (fun a ↦ tensorPower
      (conZ q w (i (e.symm a).1) (j (e.symm a).1) (l (e.symm a).1))
      (nr a) (x a) (y a) (z a)), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun t _ ↦ ?_
    simpa only [Equiv.symm_apply_apply, glueBlocks, splitBlocks] using
      tensorPower_blockGlueCast (conZ q w (i t) (j t) (l t))
        (fun r ↦ nr (e (t, r))) (hsum t) (splitBlocks e nr x t)
        (splitBlocks e nr y t) (splitBlocks e nr z t)

private theorem scaledIntegralCount_eq36 (b base m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * (base : ℚ) * a = (k : ℚ)) :
    (((b * m : ℕ) : ℚ) * (base : ℚ) * a).floor.toNat = k * m := by
  have hq : (((b * m : ℕ) : ℚ) * (base : ℚ) * a) = ((k * m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k * m : ℕ) : ℚ).floor) = (k * m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k * m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k * m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

private theorem scaledIntegralWeight_eq36 (b base m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * (base : ℚ) * a = (k : ℚ))
    (hN : 0 < base * (b * m)) :
    ((((b * m : ℕ) : ℚ) * (base : ℚ) * a).floor.toNat : ℕ) /
        (base * (b * m) : ℚ) = a := by
  rw [scaledIntegralCount_eq36 b base m k a hk]
  have hNQ : ((base * (b * m) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hnum : ((k * m : ℕ) : ℚ) = ((base * (b * m) : ℕ) : ℚ) * a := by
    push_cast
    rw [← hk]
    ring
  rw [hnum]
  push_cast at hNQ ⊢
  exact mul_div_cancel_left₀ a hNQ

private theorem mixture_num_ne_zero36 {k : ℕ} {ι : Type*} [Fintype ι]
    (A : RatDist (Fin k)) (P : Fin k → RatDist ι) (Q : RatDist ι)
    (hmix : ∀ a, Q.prob a = ∑ r, A.prob r * (P r).prob a)
    (r : Fin k) (a : ι) (hA : 0 < A.prob r) (hP : (P r).num a ≠ 0) :
    Q.num a ≠ 0 := by
  have hPpos : 0 < (P r).prob a := by
    unfold RatDist.prob
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hP) (by exact_mod_cast (P r).den_pos)
  have hterm : 0 < A.prob r * (P r).prob a := mul_pos hA hPpos
  have hsum : 0 < ∑ j, A.prob j * (P j).prob a :=
    lt_of_lt_of_le hterm (Finset.single_le_sum
      (fun j _ ↦ mul_nonneg (A.prob_nonneg j) ((P j).prob_nonneg a)) (Finset.mem_univ r))
  have hQpos : 0 < Q.prob a := by rw [hmix]; exact hsum
  intro hQ
  simp [RatDist.prob, hQ] at hQpos

theorem constituent_partition_integral36 (q w s b m : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ) (hε : 0 ≤ ε) :
  Restricts (regionalInputZ q p d (b*m) ε).tensor
    (constituentInputZ q p (b*m) ε).tensor := by
  classical
  let e : Fin s × Fin 6 ≃ Fin (Fintype.card (Fin s × Fin 6)) := Fintype.equivFin _
  let nr : Fin (Fintype.card (Fin s × Fin 6)) → ℕ := fun a ↦
    (((b * m : ℕ) : ℚ) * (p.baseN (e.symm a).1 : ℚ) *
      (d.A (e.symm a).1).prob (e.symm a).2).floor.toNat
  have hsum : ∀ t, ∑ r, nr (e (t, r)) = p.baseN t * (b * m) := by
    intro t
    let kr : Fin 6 → ℕ := fun r ↦ Classical.choose (hb.regionIntegral t r)
    have hkr : ∀ r, (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r = (kr r : ℚ) :=
      fun r ↦ Classical.choose_spec (hb.regionIntegral t r)
    have hcount : ∀ r, nr (e (t, r)) = kr r * m := by
      intro r
      simp only [nr, Equiv.symm_apply_apply]
      exact scaledIntegralCount_eq36 b (p.baseN t) m (kr r) ((d.A t).prob r) (hkr r)
    have hkrSumQ : ((∑ r, kr r : ℕ) : ℚ) = ((b * p.baseN t : ℕ) : ℚ) := by
      rw [Nat.cast_sum]
      calc
        ∑ r, (kr r : ℚ) = ∑ r, (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r := by
          exact Finset.sum_congr rfl fun r _ ↦ (hkr r).symm
        _ = (b : ℚ) * (p.baseN t : ℚ) * ∑ r, (d.A t).prob r := by
          rw [Finset.mul_sum]
        _ = ((b * p.baseN t : ℕ) : ℚ) := by rw [(d.A t).sum_prob]; push_cast; ring
    have hkrSum : ∑ r, kr r = b * p.baseN t := by exact_mod_cast hkrSumQ
    rw [Finset.sum_congr rfl fun r _ ↦ hcount r, ← Finset.sum_mul, hkrSum]
    ring
  have hmix : ∀ W t, 0 < p.baseN t * (b * m) → ∀ a,
      (p.beta W t).prob a = ∑ r,
        ((nr (e (t, r)) : ℕ) : ℚ) / (p.baseN t * (b * m) : ℚ) *
          (d.betaRegion W t r).prob a := by
    intro W t hN a
    have hweight : ∀ r, ((nr (e (t, r)) : ℕ) : ℚ) /
        (p.baseN t * (b * m) : ℚ) = (d.A t).prob r := by
      intro r
      let kr := Classical.choose (hb.regionIntegral t r)
      have hkr : (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r = (kr : ℚ) :=
        Classical.choose_spec (hb.regionIntegral t r)
      simp only [nr, Equiv.symm_apply_apply]
      exact scaledIntegralWeight_eq36 b (p.baseN t) m kr ((d.A t).prob r) hkr hN
    rw [hd.mixture]
    exact Finset.sum_congr rfl fun r _ ↦ by rw [hweight r]
  have hsupport : ∀ W t r, 0 < nr (e (t, r)) → ∀ a,
      (d.betaRegion W t r).num a ≠ 0 → (p.beta W t).num a ≠ 0 := by
    intro W t r hnr a ha
    let kr := Classical.choose (hb.regionIntegral t r)
    have hkr : (b : ℚ) * (p.baseN t : ℚ) * (d.A t).prob r = (kr : ℚ) :=
      Classical.choose_spec (hb.regionIntegral t r)
    have hcount : nr (e (t, r)) = kr * m := by
      simp only [nr, Equiv.symm_apply_apply]
      exact scaledIntegralCount_eq36 b (p.baseN t) m kr ((d.A t).prob r) hkr
    have hm : 0 < m := Nat.pos_of_mul_pos_left (hcount ▸ hnr)
    have hN : 0 < p.baseN t * (b * m) :=
      Nat.mul_pos (p.baseN_pos t) (Nat.mul_pos hb.bpos hm)
    have hweight : ((nr (e (t, r)) : ℕ) : ℚ) /
        (p.baseN t * (b * m) : ℚ) = (d.A t).prob r := by
      simpa only [nr, Equiv.symm_apply_apply] using
        scaledIntegralWeight_eq36 b (p.baseN t) m kr ((d.A t).prob r) hkr hN
    have hA : 0 < (d.A t).prob r := by
      rw [← hweight]
      have hnrQ : (0 : ℚ) < (nr (e (t, r)) : ℕ) := by exact_mod_cast hnr
      have hNQ : (0 : ℚ) < (p.baseN t * (b * m) : ℕ) := by exact_mod_cast hN
      push_cast at hNQ
      exact div_pos hnrQ hNQ
    exact mixture_num_ne_zero36 (d.A t) (fun r ↦ d.betaRegion W t r) (p.beta W t)
      (hd.mixture W t) r a hA ha
  have h := supportedIfaceZ_partition q (w + w) s 6 e
    (fun t ↦ p.baseN t * (b * m)) nr p.i p.j p.k p.beta
    (fun W a ↦ d.betaRegion W (e.symm a).1 (e.symm a).2) ε hsum
    (by
      intro W t ht a
      simpa only [Equiv.symm_apply_apply, Nat.cast_mul] using hmix W t ht a)
    (by
      intro W t r hr a ha
      exact hsupport W t r hr a (by simpa only [Equiv.symm_apply_apply] using ha))
  simpa only [regionalInputZ, constituentInputZ, e, nr] using h


#print axioms OmegaBound.ADVXXZGeneral.constituent_grid_integral36
#print axioms OmegaBound.ADVXXZGeneral.constituent_partition_integral36


end OmegaBound.ADVXXZGeneral
