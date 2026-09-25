import OmegaBound.ADVXXZGeneralIterateStagesTransport
import OmegaBound.ADVXXZGeneralIterateInfraRates
import OmegaBound.ADVXXZGeneralCExact33Statements

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

/-- The retained-rate contribution of one optional constituent stage. -/
noncomputable def iterateStageRate (C : Certificate) (l : Stage C.top) : ℝ :=
  match C.stage l with
  | none => 0
  | some d => cRate d.data * (constituentBaseTotal d.input : ℝ) / (C.D : ℝ) ^ 2

theorem derivedRetainedRate_eq_iterateStageRate (C : Certificate) :
    derivedRetainedRate C = gRate C.global + ∑ l : Stage C.top, iterateStageRate C l := by
  rfl

/-- The constituent supplied length is its advertised fixed fraction of the outer length. -/
theorem cLength_eq_outer_fraction (C : Certificate) (hC : AdmissibleAt C)
    {w s : ℕ} (p : ConstituentInput w s) (m : ℕ) :
    (cLength p (C.D ^ 2) m : ℝ) =
      ((constituentBaseTotal p : ℝ) / (C.D : ℝ) ^ 2) * (outerN C m : ℝ) := by
  have hD : (C.D : ℝ) ≠ 0 := by exact_mod_cast hC.D_pos.ne'
  simp only [cLength, outerN, Nat.cast_mul, Nat.cast_pow]
  field_simp

/-- Re-express a lower rate after an exact fixed rescaling of its length. -/
theorem lowerRate_rescale
    (O L : ℕ → ℕ) (x : ℚ → ℕ → ℕ) (r scale : ℝ)
    (hscale : 0 ≤ scale) (hL : ∀ m, (L m : ℝ) = scale * (O m : ℝ))
    (h : LowerRate L x r) : LowerRate O x (r * scale) := by
  intro δ hδ
  by_cases hs : scale = 0
  · obtain ⟨ε₀, hε₀, htail⟩ := h 1 (by norm_num)
    refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
    obtain ⟨M, hM⟩ := htail ε hε hεle
    refine ⟨M, fun m hm => ?_⟩
    obtain ⟨hx, -⟩ := hM m hm
    refine ⟨hx, ?_⟩
    have hlog : 0 ≤ Real.log (x ε m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hx)
    rw [hs, mul_zero, zero_sub]
    have hnon : -δ * (O m : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (Nat.cast_nonneg _)
    exact hnon.trans hlog
  · have hspos : 0 < scale := lt_of_le_of_ne hscale (Ne.symm hs)
    have hquot : 0 < δ / scale := div_pos hδ hspos
    obtain ⟨ε₀, hε₀, htail⟩ := h (δ / scale) hquot
    refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
    obtain ⟨M, hM⟩ := htail ε hε hεle
    refine ⟨M, fun m hm => ?_⟩
    obtain ⟨hx, hbound⟩ := hM m hm
    refine ⟨hx, ?_⟩
    rw [hL] at hbound
    calc
      (r * scale - δ) * (O m : ℝ) =
          (r - δ / scale) * (scale * (O m : ℝ)) := by field_simp
      _ ≤ Real.log (x ε m : ℝ) := hbound

/-- Sublinearity is preserved when its length is an exact nonnegative fixed fraction. -/
theorem sublinear_rescale
    (O L : ℕ → ℕ) (f : ℕ → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale) (hL : ∀ m, (L m : ℝ) = scale * (O m : ℝ))
    (h : Sublinear L f) : Sublinear O f := by
  intro δ hδ
  have hden : 0 < scale + 1 := by linarith
  obtain ⟨M, hM⟩ := h (δ / (scale + 1)) (div_pos hδ hden)
  refine ⟨M, fun m hm => ?_⟩
  have hb := hM m hm
  rw [hL] at hb
  have hO : 0 ≤ (O m : ℝ) := Nat.cast_nonneg _
  calc
    |f m| ≤ δ / (scale + 1) * (scale * (O m : ℝ)) := hb
    _ ≤ δ * (O m : ℝ) := by
      have hratio : scale / (scale + 1) ≤ 1 := by
        apply (div_le_one hden).2
        linarith
      calc
        δ / (scale + 1) * (scale * (O m : ℝ)) =
            δ * (scale / (scale + 1)) * (O m : ℝ) := by field_simp
        _ ≤ δ * 1 * (O m : ℝ) := by gcongr
        _ = _ := by ring

/-- The constant-one family has zero lower rate. -/
theorem lowerRate_one_zero (O : ℕ → ℕ) :
    LowerRate O (fun _ _ => 1) 0 := by
  intro δ hδ
  refine ⟨1, by norm_num, fun ε hε _ => ⟨0, fun m _ => ⟨by simp, ?_⟩⟩⟩
  simp only [Nat.cast_one, Real.log_one, zero_sub]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (Nat.cast_nonneg _)

/-- The constant-one logarithm is sublinear. -/
theorem sublinear_log_one (O : ℕ → ℕ) :
    Sublinear O (fun _ => Real.log (((1 : ℕ) : ℝ))) := by
  intro δ hδ
  exact ⟨0, fun m _ => by simp [mul_nonneg hδ.le (Nat.cast_nonneg (O m))]⟩

/-- Concrete data selected from the pooled producer for one optional stage. -/
structure IterateStageData (C : Certificate) (l : Stage C.top) where
  Q : ℚ → ℕ → ℕ
  V : ℚ → ℕ → ℕ
  Q_one : ∀ ε m, 1 ≤ Q ε m
  Q_sublinear : ∀ ε, 0 < ε →
    Sublinear (outerN C) (fun m => Real.log (Q ε m : ℝ))
  V_lowerRate : LowerRate (outerN C) V (iterateStageRate C l)
  production : ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m →
    ∃ N : ℕ, PolyDegeneratesAt ℤ N
      (copiesZ (Q ε m) (inventoryTensorZ C.q (P C l) m (3 * ε))).tensor
      (copiesZ (V ε m) (inventoryTensorZ C.q (QAt C l) m ε)).tensor

private theorem polyDegeneratesAt_refl_iterate (T : ITensor) :
    PolyDegeneratesAt ℤ 0 T.tensor T.tensor := by
  apply polyDegeneratesAt_of_restricts
  exact ADVXXZ.restricts_of_sub id id id (fun _ _ _ => rfl)

/-- The pooled hypothesis supplies normalized concrete data for every optional stage. -/
theorem iterateStageData_nonempty (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) (l : Stage C.top) :
    Nonempty (IterateStageData C l) := by
  classical
  cases hs : C.stage l with
  | none =>
      refine ⟨
        { Q := fun _ _ => 1
          V := fun _ _ => 1
          Q_one := fun _ _ => by simp
          Q_sublinear := fun _ _ => sublinear_log_one (outerN C)
          V_lowerRate := ?_
          production := ?_ }⟩
      · simpa [iterateStageRate, hs] using lowerRate_one_zero (outerN C)
      · intro ε hε
        refine ⟨0, fun m _ => ⟨0, ?_⟩⟩
        have hP : P C l = [] := by simp [P, hs]
        have hQ : QAt C l = [] := by simp [QAt, hs]
        rw [hP, hQ]
        simpa [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ] using
          polyDegeneratesAt_refl_iterate
            (copiesZ 1 (inventoryTensorZ C.q [] m (3 * ε)))
  | some d =>
      have hd := hC.stage_ok l d hs
      have hb := hC.lattice.2 l d hs
      have hw : 0 < wid (l.val - 1) := by
        simp [wid]
      obtain ⟨Q₀, V, delta, ell, hdelta, hell, hcopy, hsub, hprod⟩ :=
        hpool C.q (wid (l.val - 1)) d.s (C.D ^ 2) hC.q_pos hw
          d.input d.data hd hb
      let Q : ℚ → ℕ → ℕ := fun ε m => positiveCopyPool (Q₀ ε) m
      refine ⟨
        { Q := Q
          V := V
          Q_one := fun ε m => positiveCopyPool_one_le (Q₀ ε) m
          Q_sublinear := ?_
          V_lowerRate := ?_
          production := ?_ }⟩
      · intro ε hε
        have hnative := positiveCopyPool_sublinear (cLength d.input (C.D ^ 2))
          (Q₀ ε) (hsub ε hε)
        exact sublinear_rescale (outerN C) (cLength d.input (C.D ^ 2)) _
          ((constituentBaseTotal d.input : ℝ) / (C.D : ℝ) ^ 2)
          (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          (cLength_eq_outer_fraction C hC d.input) hnative
      · have hnative := copyBound_vanishing_loss_lowerRate
          (cLength d.input (C.D ^ 2)) (cRate d.data) V delta ell
          hdelta hell hcopy
        have hscaled := lowerRate_rescale (outerN C) (cLength d.input (C.D ^ 2)) V
          (cRate d.data) ((constituentBaseTotal d.input : ℝ) / (C.D : ℝ) ^ 2)
          (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          (cLength_eq_outer_fraction C hC d.input) hnative
        simpa [iterateStageRate, hs, div_eq_mul_inv, mul_assoc] using hscaled
      · intro ε hε
        obtain ⟨M, hM⟩ := hprod ε hε
        refine ⟨M, fun m hm => ?_⟩
        obtain ⟨hQ₀, -, N, hN⟩ := hM m hm
        have hsource : Restricts
            (copiesZ (Q₀ ε m)
              (constituentPlainInputZ C.q d.input (C.D ^ 2 * m) (3 * ε))).tensor
            (copiesZ (Q₀ ε m)
              (inventoryTensorZ C.q (P C l) m (3 * ε))).tensor :=
          copiesZ_restricts_of_restricts _
            (ordinaryTensorTransport_restricts_reverse
              (stageParent_plain_transport C l hs m (3 * ε)))
        obtain ⟨N₁, h₁⟩ := integral_polyDegeneratesAt_trans
          (polyDegeneratesAt_of_restricts hsource) hN
        have htarget : Restricts
            (copiesZ (V ε m) (inventoryTensorZ C.q (QAt C l) m ε)).tensor
            (copiesZ (V ε m) (constituentOutputZ C.q d.data m ε)).tensor :=
          copiesZ_restricts_of_restricts _
            (ordinaryTensorTransport_restricts
              (stageOutput_plain_transport C l hs m ε))
        obtain ⟨N₂, h₂⟩ := integral_polyDegeneratesAt_trans h₁
          (polyDegeneratesAt_of_restricts htarget)
        refine ⟨N₂, ?_⟩
        change PolyDegeneratesAt ℤ N₂
          (copiesZ (positiveCopyPool (Q₀ ε) m)
            (inventoryTensorZ C.q (P C l) m (3 * ε))).tensor _
        rw [positiveCopyPool_eq_of_one_le (Q₀ ε) hQ₀]
        exact h₂

/-- Select and normalize the pooled positive producer for one stage. -/
noncomputable def iterateStageData (C : Certificate) (hC : AdmissibleAt C)
    (hpool : S_constituent_pooled_positive33) (l : Stage C.top) :
    IterateStageData C l :=
  Classical.choice (iterateStageData_nonempty C hC hpool l)

end
end OmegaBound.ADVXXZGeneral
end
