import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

private theorem constituentMarginal_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (t : Fin s) (r : Fin 6)
    (W : Side) :
    constituentMarginal (d.atScale b hb).toPaper t r W =
      constituentMarginal d.toPaper t r W := by
  rfl

private theorem constituentPenalty_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (t : Fin s) (r : Fin 6) :
    constituentPenalty (d.atScale b hb).toPaper t r =
      constituentPenalty d.toPaper t r := by
  rfl

private theorem constituentEta_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (t : Fin s) (r : Fin 6)
    (X Y Z : Side) :
    constituentEta (d.atScale b hb).toPaper t r X Y Z =
      constituentEta d.toPaper t r X Y Z := by
  rfl

private theorem constituentLambda_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (t : Fin s) (r : Fin 6)
    (X Y Z : Side) :
    constituentLambda (d.atScale b hb).toPaper t r X Y Z =
      constituentLambda d.toPaper t r X Y Z := by
  rfl

private theorem constituentPerm_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6) (W : Side) :
    (d.atScale b hb).toPaper.perm r W = d.toPaper.perm r W := by
  rfl

private theorem constituentRowX_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6) (X : Side) :
    constituentRowX (d.atScale b hb).toPaper r X =
      (b : ℝ) * constituentRowX d.toPaper r X := by
  unfold constituentRowX
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [constituentMarginal_atScale, constituentPenalty_atScale]
  simp only [ConstituentSpec.toPaper, ConstituentSpec.atScale, scaleParent, Nat.cast_mul]
  ring

private theorem constituentRowY_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6) (X Y Z : Side) :
    constituentRowY (d.atScale b hb).toPaper r X Y Z =
      (b : ℝ) * constituentRowY d.toPaper r X Y Z := by
  unfold constituentRowY
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [constituentEta_atScale]
  simp only [ConstituentSpec.toPaper, ConstituentSpec.atScale, scaleParent, Nat.cast_mul]
  ring

private theorem constituentRowZ_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6) (X Y Z : Side) :
    constituentRowZ (d.atScale b hb).toPaper r X Y Z =
      (b : ℝ) * constituentRowZ d.toPaper r X Y Z := by
  unfold constituentRowZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [constituentLambda_atScale]
  simp only [ConstituentSpec.toPaper, ConstituentSpec.atScale, scaleParent, Nat.cast_mul]
  ring

private theorem constituentRegionRate_atScale {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hb : 0 < b) (r : Fin 6) :
    constituentRegionRate (d.atScale b hb).toPaper r =
      (b : ℝ) * constituentRegionRate d.toPaper r := by
  simp only [constituentRegionRate]
  rw [constituentRowX_atScale, constituentRowY_atScale, constituentRowZ_atScale]
  simp only [constituentPerm_atScale]
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  rw [mul_min_of_nonneg _ _ hb0, mul_min_of_nonneg _ _ hb0]

private theorem constituentBaseTotal_scale {w s : ℕ} (p : ConstituentInput w s)
    (b : ℕ) (hb : 0 < b) :
    (constituentBaseTotal (scaleParent p b hb) : ℝ) =
      (b : ℝ) * (constituentBaseTotal p : ℝ) := by
  simp [constituentBaseTotal, scaleParent, Finset.mul_sum]

private theorem constituentRegionRate_setOutBase {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (f : ConstituentTerm p → ℕ) (r : Fin 6) :
    constituentRegionRate ({ d with outBase := f }).toPaper r =
      constituentRegionRate d.toPaper r := by
  rfl

private theorem releasedOrdinaryStep3_regionRate (r : Fin 6) :
    constituentRegionRate releasedOrdinaryStep3.data.toPaper r =
      (ordinaryD : ℝ)^2 * constituentRegionRate releasedConstituentSpec.toPaper r := by
  unfold releasedOrdinaryStep3
  rw [constituentRegionRate_setOutBase]
  rw [← Nat.cast_pow]
  exact constituentRegionRate_atScale releasedConstituentSpec (ordinaryD^2)
    (by decide +kernel) r

private theorem releasedOrdinaryStep3_cRate :
    cRate releasedOrdinaryStep3.data = cRate releasedConstituentSpec := by
  unfold cRate
  rw [show (∑ r, constituentRegionRate releasedOrdinaryStep3.data.toPaper r) =
      (ordinaryD : ℝ)^2 * ∑ r, constituentRegionRate releasedConstituentSpec.toPaper r by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact releasedOrdinaryStep3_regionRate r]
  rw [show (constituentBaseTotal releasedOrdinaryStep3.input : ℝ) =
      (ordinaryD : ℝ)^2 * (constituentBaseTotal releasedParent : ℝ) by
    change (constituentBaseTotal
      (scaleParent releasedParent (ordinaryD^2) (by decide +kernel)) : ℝ) = _
    rw [← Nat.cast_pow]
    exact constituentBaseTotal_scale releasedParent (ordinaryD^2) (by decide +kernel)]
  have hDnat : 0 < ordinaryD := by decide +kernel
  have hD : (ordinaryD : ℝ)^2 ≠ 0 := by exact_mod_cast (pow_pos hDnat 2).ne'
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_div_mul_left
      (Real.log 2 * ∑ r, constituentRegionRate releasedConstituentSpec.toPaper r)
      (constituentBaseTotal releasedParent : ℝ) hD)

theorem released_ordinary_scale_covariance :
  (∀ m, outerN releasedOrdinaryCertificatePhysical m = ordinaryD^4 * outerN physicalLegacyCertificate m) ∧
  cRate releasedOrdinaryStep3.data = cRate releasedConstituentSpec ∧
  cRate releasedOrdinaryStep3.data * (constituentBaseTotal releasedOrdinaryStep3.input : ℝ) /
      (releasedOrdinaryCertificatePhysical.D : ℝ)^2 =
    cRate releasedConstituentSpec * (constituentBaseTotal releasedParent : ℝ) / (ordinaryD : ℝ)^2 ∧
  ∀ r, constituentRegionRate releasedOrdinaryStep3.data.toPaper r =
    (ordinaryD : ℝ)^2 * constituentRegionRate releasedConstituentSpec.toPaper r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    simp only [outerN, releasedOrdinaryCertificatePhysical, physicalLegacyCertificate,
      releasedCertificate, ordinaryD]
    ring
  · exact releasedOrdinaryStep3_cRate
  · rw [releasedOrdinaryStep3_cRate]
    rw [show (constituentBaseTotal releasedOrdinaryStep3.input : ℝ) =
        (ordinaryD : ℝ)^2 * (constituentBaseTotal releasedParent : ℝ) by
      change (constituentBaseTotal
        (scaleParent releasedParent (ordinaryD^2) (by decide +kernel)) : ℝ) = _
      rw [← Nat.cast_pow]
      exact constituentBaseTotal_scale releasedParent (ordinaryD^2) (by decide +kernel)]
    simp only [releasedOrdinaryCertificatePhysical, Nat.cast_pow]
    have hDnat : 0 < ordinaryD := by decide +kernel
    have hD : (ordinaryD : ℝ)^2 ≠ 0 := by exact_mod_cast (pow_pos hDnat 2).ne'
    field_simp [hD]
  · intro r
    exact releasedOrdinaryStep3_regionRate r

end OmegaBound.ADVXXZGeneral
end
