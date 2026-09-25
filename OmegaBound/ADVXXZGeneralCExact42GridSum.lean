import OmegaBound.ADVXXZGeneralCExact42GridPool
import OmegaBound.ADVXXZGeneralGlobalPositiveInfra

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

private noncomputable def constituentCoefficientCount42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (i : Fin (Fintype.card (ConstituentTerm p))) (W : Side) (σ : Chunk w) : ℕ :=
  match W with
  | .X => typeCnt (chunkSeq (x i)) σ
  | .Y => typeCnt (chunkSeq (y i)) σ
  | .Z => typeCnt (chunkSeq (z i)) σ

private theorem constituentCoefficientCount_total42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (i : Fin (Fintype.card (ConstituentTerm p))) (W : Side) :
    ∑ σ, constituentCoefficientCount42 x y z i W σ =
      constituentOutN d.toPaper m i := by
  cases W
  · exact ADVXXZ.sum_typeCnt (chunkSeq (x i))
  · exact ADVXXZ.sum_typeCnt (chunkSeq (y i))
  · exact ADVXXZ.sum_typeCnt (chunkSeq (z i))

private theorem constituentPositiveOutput_iface_ne42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (i : Fin (Fintype.card (ConstituentTerm p))) :
    ifaceTermZ q w (constituentOutI (p := p) i) (constituentOutJ (p := p) i)
      (constituentOutK (p := p) i) (constituentOutN d.toPaper m i)
      (constituentOutBeta d.toPaper .X i) (constituentOutBeta d.toPaper .Y i)
      (constituentOutBeta d.toPaper .Z i) ε (x i) (y i) (z i) ≠ 0 := by
  have hprod :
      (∏ j : Fin (Fintype.card (ConstituentTerm p)),
        ifaceTermZ q w (constituentOutI (p := p) j)
          (constituentOutJ (p := p) j) (constituentOutK (p := p) j)
          (constituentOutN d.toPaper m j)
          (constituentOutBeta d.toPaper .X j)
          (constituentOutBeta d.toPaper .Y j)
          (constituentOutBeta d.toPaper .Z j) ε (x j) (y j) (z j)) ≠ 0 := by
    simpa [constituentOutputZ, ifaceZ] using hcoeff
  intro hi
  exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hi)

private theorem constituentPositiveOutput_nonzero_approx42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (i : Fin (Fintype.card (ConstituentTerm p)))
    (hn : 0 < constituentOutN d.toPaper m i) :
    ApproxConsistent ε (constituentOutBeta d.toPaper .X i) (chunkSeq (x i)) ∧
      ApproxConsistent ε (constituentOutBeta d.toPaper .Y i) (chunkSeq (y i)) ∧
      ApproxConsistent ε (constituentOutBeta d.toPaper .Z i) (chunkSeq (z i)) := by
  have hi := constituentPositiveOutput_iface_ne42 x y z hcoeff i
  by_contra hguard
  simp [ifaceTermZ, Nat.ne_of_gt hn, hguard] at hi

private theorem constituentPositive_conZ_ne_levels42 {q w i j k : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (h : conZ q w i j k x y z ≠ 0) :
    levOf x = i ∧ levOf y = j ∧ levOf z = k := by
  unfold conZ zoP at h
  split at h
  · assumption
  · simp at h

private theorem constituentPositiveOutput_conZ_ne42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (i : Fin (Fintype.card (ConstituentTerm p)))
    (a : Fin (constituentOutN d.toPaper m i)) :
    conZ q w (constituentOutI (p := p) i) (constituentOutJ (p := p) i)
      (constituentOutK (p := p) i) (x i a) (y i a) (z i a) ≠ 0 := by
  have hn : constituentOutN d.toPaper m i ≠ 0 := by
    have := a.isLt
    omega
  have hi := constituentPositiveOutput_iface_ne42 x y z hcoeff i
  simp only [ifaceTermZ, if_neg hn] at hi
  split at hi
  · intro ha
    exact hi (Finset.prod_eq_zero (Finset.mem_univ a) ha)
  · simp at hi

private theorem constituentCoefficientCount_graded42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (i : Fin (Fintype.card (ConstituentTerm p))) (W : Side) (σ : Chunk w)
    (hgrade : chunkLvl σ ≠ coord W (constituentIndex (p := p) i).2.2.1) :
    constituentCoefficientCount42 x y z i W σ = 0 := by
  by_contra hzero
  have hpos : 0 < constituentCoefficientCount42 x y z i W σ :=
    Nat.pos_of_ne_zero hzero
  have hle : constituentCoefficientCount42 x y z i W σ ≤
      ∑ τ, constituentCoefficientCount42 x y z i W τ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  have hn : 0 < constituentOutN d.toPaper m i := by
    rw [constituentCoefficientCount_total42 x y z i W] at hle
    omega
  cases W with
  | X =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (x i) a = σ).card := by
        simpa [constituentCoefficientCount42, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hc := constituentPositiveOutput_conZ_ne42 x y z hcoeff i a
      have hl := (constituentPositive_conZ_ne_levels42 _ _ _ hc).1
      change chunkLvl (chunkSeq (x i) a) =
        coord .X (constituentIndex (p := p) i).2.2.1 at hl
      rw [haeq] at hl
      exact hgrade hl
  | Y =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (y i) a = σ).card := by
        simpa [constituentCoefficientCount42, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hc := constituentPositiveOutput_conZ_ne42 x y z hcoeff i a
      have hl := (constituentPositive_conZ_ne_levels42 _ _ _ hc).2.1
      change chunkLvl (chunkSeq (y i) a) =
        coord .Y (constituentIndex (p := p) i).2.2.1 at hl
      rw [haeq] at hl
      exact hgrade hl
  | Z =>
      have hp : 0 < (Finset.univ.filter fun a =>
          chunkSeq (z i) a = σ).card := by
        simpa [constituentCoefficientCount42, typeCnt] using hpos
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
      have haeq := (Finset.mem_filter.mp ha).2
      have hc := constituentPositiveOutput_conZ_ne42 x y z hcoeff i a
      have hl := (constituentPositive_conZ_ne_levels42 _ _ _ hc).2.2
      change chunkLvl (chunkSeq (z i) a) =
        coord .Z (constituentIndex (p := p) i).2.2.1 at hl
      rw [haeq] at hl
      exact hgrade hl

private noncomputable def constituentCoefficientExactGrid42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0) :
    ConstituentExactGrid27 d m := by
  refine ⟨fun i W σ => ⟨constituentCoefficientCount42 x y z i W σ, ?_⟩, ?_, ?_⟩
  · apply Nat.lt_succ_of_le
    rw [← constituentCoefficientCount_total42 x y z i W]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  · exact constituentCoefficientCount_total42 x y z
  · intro i W σ hne
    by_contra hgrade
    exact hne (constituentCoefficientCount_graded42 x y z hcoeff i W σ hgrade)

private theorem constituentCoefficientCount_close42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (i : Fin (Fintype.card (ConstituentTerm p))) (W : Side)
    (hn : 0 < constituentOutN d.toPaper m i) (σ : Chunk w) :
    |(constituentCoefficientCount42 x y z i W σ : ℚ) /
        constituentOutN d.toPaper m i -
      (constituentOutBeta d.toPaper W i).prob σ| ≤ ε := by
  have h := constituentPositiveOutput_nonzero_approx42 x y z hcoeff i hn
  cases W
  · simpa [constituentCoefficientCount42, emp] using h.1 σ
  · simpa [constituentCoefficientCount42, emp] using h.2.1 σ
  · simpa [constituentCoefficientCount42, emp] using h.2.2 σ

private noncomputable def constituentCoefficientFullGrid42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0) :
    ConstituentFullGrid27 d m ε := by
  refine ⟨constituentCoefficientExactGrid42 x y z hcoeff, ?_⟩
  intro i W hn σ
  exact constituentCoefficientCount_close42 x y z hcoeff i W hn σ

private noncomputable def ConstituentGridLegMatches42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (W : Side) (h : ConstituentFullGrid27 d m ε)
    (x : (constituentOutputZ q d m ε).X) : Prop :=
  ∀ i σ, (h.val.val i W σ).val = typeCnt (chunkSeq (x i)) σ

private noncomputable def constituentFullGridTensor42 (q : ℕ) {w s m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) {ε : ℚ}
    (h : ConstituentFullGrid27 d m ε) : ITensor :=
  let T := constituentOutputZ q d m ε
  { X := T.X, Y := T.Y, Z := T.Z
    tensor := zoP (ConstituentGridLegMatches42 .X h)
      (ConstituentGridLegMatches42 .Y h)
      (ConstituentGridLegMatches42 .Z h) T.tensor }

private theorem constituentCoefficientFullGrid_matches42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0) :
    ConstituentGridLegMatches42 .X
        (constituentCoefficientFullGrid42 x y z hcoeff) x ∧
      ConstituentGridLegMatches42 .Y
        (constituentCoefficientFullGrid42 x y z hcoeff) y ∧
      ConstituentGridLegMatches42 .Z
        (constituentCoefficientFullGrid42 x y z hcoeff) z := by
  simp [ConstituentGridLegMatches42, constituentCoefficientFullGrid42,
    constituentCoefficientExactGrid42, constituentCoefficientCount42]

private theorem constituentExactGrid_ext42 {w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {ξ η : ConstituentExactGrid27 d m} (h : ξ.val = η.val) : ξ = η := by
  cases ξ
  cases η
  cases h
  rfl

private theorem constituentFullGrid_eq_of_matches42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X)
    (hcoeff : (constituentOutputZ q d m ε).tensor x y z ≠ 0)
    (h : ConstituentFullGrid27 d m ε)
    (hmX : ConstituentGridLegMatches42 .X h x)
    (hmY : ConstituentGridLegMatches42 .Y h y)
    (hmZ : ConstituentGridLegMatches42 .Z h z) :
    h = constituentCoefficientFullGrid42 x y z hcoeff := by
  apply Subtype.ext
  apply constituentExactGrid_ext42
  funext i W σ
  apply Fin.ext
  cases W
  · exact hmX i σ
  · exact hmY i σ
  · exact hmZ i σ

private theorem constituentFullGridTensor_apply42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (h : ConstituentFullGrid27 d m ε)
    (x y z : (constituentOutputZ q d m ε).X) :
    (constituentFullGridTensor42 q d h).tensor x y z =
      if ConstituentGridLegMatches42 .X h x ∧
          ConstituentGridLegMatches42 .Y h y ∧
          ConstituentGridLegMatches42 .Z h z
      then (constituentOutputZ q d m ε).tensor x y z else 0 := rfl

private theorem constituentFullGridTensor_sum_apply42 {q w s m : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p} {ε : ℚ}
    (x y z : (constituentOutputZ q d m ε).X) :
    ((∑ h : ConstituentFullGrid27 d m ε,
        (constituentFullGridTensor42 q d h).tensor) :
      Tensor3 ℤ (constituentOutputZ q d m ε).X
        (constituentOutputZ q d m ε).Y
        (constituentOutputZ q d m ε).Z) x y z =
      ∑ h : ConstituentFullGrid27 d m ε,
        (constituentFullGridTensor42 q d h).tensor x y z := by
  let f : ConstituentFullGrid27 d m ε →
      Tensor3 ℤ (constituentOutputZ q d m ε).X
        (constituentOutputZ q d m ε).Y
        (constituentOutputZ q d m ε).Z :=
    fun h => (constituentFullGridTensor42 q d h).tensor
  change (∑ h, f h) x y z = ∑ h, f h x y z
  rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]

/-- The positive constituent output is the coefficientwise sum of its nearby exact grids. -/
theorem constituentOutputZ_eq_sum_fullGridTensor42 (q : ℕ) {w s m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (ε : ℚ) :
    (constituentOutputZ q d m ε).tensor =
      ∑ h : ConstituentFullGrid27 d m ε,
        (constituentFullGridTensor42 q d h).tensor := by
  classical
  funext x y z
  rw [constituentFullGridTensor_sum_apply42]
  by_cases hcoeff : (constituentOutputZ q d m ε).tensor x y z = 0
  · simp [constituentFullGridTensor_apply42, hcoeff]
  · let h₀ := constituentCoefficientFullGrid42 x y z hcoeff
    symm
    calc
      ∑ h : ConstituentFullGrid27 d m ε,
          (constituentFullGridTensor42 q d h).tensor x y z =
          (constituentFullGridTensor42 q d h₀).tensor x y z := by
        apply Finset.sum_eq_single h₀
        · intro h _ hne
          rw [constituentFullGridTensor_apply42, if_neg (fun hm => hne
            (constituentFullGrid_eq_of_matches42 x y z hcoeff h hm.1 hm.2.1 hm.2.2))]
        · simp
      _ = (constituentOutputZ q d m ε).tensor x y z := by
        rw [constituentFullGridTensor_apply42, if_pos]
        exact constituentCoefficientFullGrid_matches42 x y z hcoeff

set_option maxHeartbeats 1000000 in
-- Comparing the two histogram zero-outs expands all interface factors.
/-- The exact grid tensor `constituentGridTensorZ27` is the corresponding common-leg positive-output summand. -/
theorem constituentGridTensor_eq_fullGridTensor42 (q : ℕ) {w s b m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) {ε : ℚ}
    (h : ConstituentFullGrid27 d m ε) :
    (constituentGridTensorZ27 q d m h.val).tensor =
      (constituentFullGridTensor42 q d h).tensor := by
  classical
  let keep := fun (W : Side)
      (x : (constituentGridTensorZ27 q d m h.val).X) =>
    ∀ i σ, typeCnt (chunkSeq (x i)) σ = (h.val.val i W σ).val
  change zoP (keep .X) (keep .Y) (keep .Z)
      (fun x y z => ∏ i,
        tensorPower (conZ q w (constituentOutI (p := p) i)
          (constituentOutJ (p := p) i) (constituentOutK (p := p) i))
          (constituentOutN d.toPaper m i) (x i) (y i) (z i)) =
    zoP (ConstituentGridLegMatches42 .X h)
      (ConstituentGridLegMatches42 .Y h)
      (ConstituentGridLegMatches42 .Z h)
      (constituentOutputZ q d m ε).tensor
  funext x y z
  by_cases hk : keep .X x ∧ keep .Y y ∧ keep .Z z
  · have hm :
        ConstituentGridLegMatches42 .X h x ∧
          ConstituentGridLegMatches42 .Y h y ∧
          ConstituentGridLegMatches42 .Z h z :=
      ⟨fun i σ => (hk.1 i σ).symm,
        fun i σ => (hk.2.1 i σ).symm,
        fun i σ => (hk.2.2 i σ).symm⟩
    simp only [zoP, if_pos hk, if_pos hm]
    change (∏ i, tensorPower
        (conZ q w (constituentOutI (p := p) i)
          (constituentOutJ (p := p) i) (constituentOutK (p := p) i))
        (constituentOutN d.toPaper m i) (x i) (y i) (z i)) =
      ∏ i, ifaceTermZ q w (constituentOutI (p := p) i)
        (constituentOutJ (p := p) i) (constituentOutK (p := p) i)
        (constituentOutN d.toPaper m i)
        (constituentOutBeta d.toPaper .X i)
        (constituentOutBeta d.toPaper .Y i)
        (constituentOutBeta d.toPaper .Z i) ε (x i) (y i) (z i)
    apply Finset.prod_congr rfl
    intro i _
    by_cases hn : constituentOutN d.toPaper m i = 0
    · simp only [ifaceTermZ, hn, if_pos]
      apply Finset.prod_eq_one
      intro a _
      exact Fin.elim0 (hn ▸ a)
    · have hX : ApproxConsistent ε (constituentOutBeta d.toPaper .X i)
          (chunkSeq (x i)) := by
        intro σ
        rw [emp]
        have hc : (typeCnt (chunkSeq (x i)) σ : ℚ) =
            ((h.val.val i .X σ).val : ℚ) := by exact_mod_cast hk.1 i σ
        exact (congrArg (fun c : ℚ => |c / constituentOutN d.toPaper m i -
          (constituentOutBeta d.toPaper .X i).prob σ|) hc).le.trans
            (h.property i .X (Nat.pos_of_ne_zero hn) σ)
      have hY : ApproxConsistent ε (constituentOutBeta d.toPaper .Y i)
          (chunkSeq (y i)) := by
        intro σ
        rw [emp]
        have hc : (typeCnt (chunkSeq (y i)) σ : ℚ) =
            ((h.val.val i .Y σ).val : ℚ) := by exact_mod_cast hk.2.1 i σ
        exact (congrArg (fun c : ℚ => |c / constituentOutN d.toPaper m i -
          (constituentOutBeta d.toPaper .Y i).prob σ|) hc).le.trans
            (h.property i .Y (Nat.pos_of_ne_zero hn) σ)
      have hZ : ApproxConsistent ε (constituentOutBeta d.toPaper .Z i)
          (chunkSeq (z i)) := by
        intro σ
        rw [emp]
        have hc : (typeCnt (chunkSeq (z i)) σ : ℚ) =
            ((h.val.val i .Z σ).val : ℚ) := by exact_mod_cast hk.2.2 i σ
        exact (congrArg (fun c : ℚ => |c / constituentOutN d.toPaper m i -
          (constituentOutBeta d.toPaper .Z i).prob σ|) hc).le.trans
            (h.property i .Z (Nat.pos_of_ne_zero hn) σ)
      have hguard : ApproxConsistent ε (constituentOutBeta d.toPaper .X i)
          (chunkSeq (x i)) ∧ ApproxConsistent ε (constituentOutBeta d.toPaper .Y i)
          (chunkSeq (y i)) ∧ ApproxConsistent ε (constituentOutBeta d.toPaper .Z i)
          (chunkSeq (z i)) := ⟨hX, hY, hZ⟩
      simp only [ifaceTermZ, if_neg hn, if_pos hguard]
  · have hm : ¬ (ConstituentGridLegMatches42 .X h x ∧
        ConstituentGridLegMatches42 .Y h y ∧
        ConstituentGridLegMatches42 .Z h z) := by
      rintro ⟨hmX, hmY, hmZ⟩
      exact hk ⟨fun i σ => (hmX i σ).symm,
        fun i σ => (hmY i σ).symm, fun i σ => (hmZ i σ).symm⟩
    simp only [zoP, if_neg hk, if_neg hm]

/-- The positive output is equally the coefficientwise sum of the exact grid tensors. -/
theorem constituentOutputZ_eq_sum_gridTensor42 (q : ℕ) {w s b m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ) :
    (constituentOutputZ q d m ε).tensor =
      ∑ h : ConstituentFullGrid27 d m ε,
        (constituentGridTensorZ27 q d m h.val).tensor := by
  rw [constituentOutputZ_eq_sum_fullGridTensor42]
  apply Finset.sum_congr rfl
  intro h _
  exact (constituentGridTensor_eq_fullGridTensor42 q d hd h).symm

end
end OmegaBound.ADVXXZGeneral
end
