import OmegaBound.ADVXXZGeneralCExact38GateStructural
import OmegaBound.ADVXXZGeneralGridInput29Concentration
import OmegaBound.ADVXXZGeneralCExact33Population

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

/-- The constituent stage population is independent of the tensor atom parameter. -/
@[simp] theorem stagePopulationAt_q_eq_zero38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    stagePopulationAt q p d b m r = stagePopulationAt 0 p d b m r := by
  rfl

/-- Uniformly over the empirical grid, input-atypical exact parts consume at most half
of the `1/(4N)` hole allowance.  The concentration constant and scale threshold are
chosen before the grid. -/
theorem constituent_grid_input_half_threshold38 (q w s b : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) :
    ∀ epsilon : ℚ, 0 < epsilon → ∃ M : ℕ, ∀ m, M ≤ m →
      ∀ (h : ConstituentExactGrid27 d m) (r : Fin 6)
        (j : StageTargetLabel37 q (constituentGridParent27 d hd m h)
          (constituentGridSpec27 d hd m h) b m r) (W : Side),
        (stagePopulationAt q (constituentGridParent27 d hd m h)
          (constituentGridSpec27 d hd m h) b m r).n ≠ 0 →
        (((exactPartsAt q b m (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) r j.val W).filter fun a =>
              ¬ Parent25.inputPartKeep (constituentGridParent27 d hd m h)
                (constituentGridSpec27 d hd m h) b m epsilon r W a).card : ℝ) ≤
          (1 / (8 * (stagePopulationAt q (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) b m r).n) : ℝ) *
            (exactPartsAt q b m (constituentGridParent27 d hd m h)
              (constituentGridSpec27 d hd m h) r j.val W).card := by
  intro epsilon hepsilon
  obtain ⟨C, hC, Minput, hinput⟩ :=
    constituent_grid_input_concentration29 q w s b hq p d hd hb epsilon hepsilon
  obtain ⟨K, hK⟩ := exists_nat_gt
    (16 * C * (constituentBaseTotal p : ℝ))
  refine ⟨max Minput K, ?_⟩
  intro m hm h r j W hn
  let pg := constituentGridParent27 d hd m h
  let dg := constituentGridSpec27 d hd m h
  let N := (stagePopulationAt q pg dg b m r).n
  let L := b * m
  have hmInput : Minput ≤ m := (Nat.le_max_left _ _).trans hm
  have hKm : K ≤ m := (Nat.le_max_right _ _).trans hm
  have hbpos : 0 < b := hb.1
  have hmpos : 0 < m := by
    have hnonneg : 0 ≤ 16 * C * (constituentBaseTotal p : ℝ) := by positivity
    have hKpos : 0 < K := by
      exact_mod_cast (lt_of_le_of_lt hnonneg hK)
    omega
  have hLpos : (0 : ℝ) < L := by
    dsimp only [L]
    positivity
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hNleNat : N ≤ 2 * cLength p b m := by
    have hle := stagePopulation_n_le q pg dg b m r
    simpa only [N, pg, dg, constituentGridParent27, cLength,
      constituentBaseTotal] using hle
  have hNle : (N : ℝ) ≤ 2 * (constituentBaseTotal p : ℝ) * L := by
    have hcast : (N : ℝ) ≤ (2 * cLength p b m : ℕ) := by
      exact_mod_cast hNleNat
    simpa only [cLength, L, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcast
  have hscale : 16 * C * (constituentBaseTotal p : ℝ) ≤ (L : ℝ) := by
    have hKmR : (K : ℝ) ≤ m := by exact_mod_cast hKm
    have hmL : (m : ℝ) ≤ L := by
      dsimp only [L]
      push_cast
      nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hbpos]
    exact (le_of_lt hK).trans (hKmR.trans hmL)
  have hkey : C * (8 * (N : ℝ)) ≤ (L : ℝ) ^ 2 := by
    calc
      C * (8 * (N : ℝ)) ≤ C * (8 * (2 * (constituentBaseTotal p : ℝ) * L)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact mul_le_mul_of_nonneg_left hNle (by positivity)
      _ = (16 * C * (constituentBaseTotal p : ℝ)) * L := by ring
      _ ≤ L * L := mul_le_mul_of_nonneg_right hscale hLpos.le
      _ = (L : ℝ) ^ 2 := by ring
  have hratio : C / (L : ℝ) ^ 2 ≤ 1 / (8 * (N : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hLpos) (by positivity)).2
    simpa only [one_mul] using hkey
  have hdensity := hinput m hmInput h r j W
  unfold constituentGridInputDensity29 at hdensity
  rw [inputDensity_eq_parent25_filter] at hdensity
  dsimp only at hdensity
  have hparts : 0 < (exactPartsAt q b m pg dg r j.val W).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_pos_iff.mpr
    simpa only [pg, dg] using
      (Grid29.stageExactPart_nonempty27 q m (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) (gridInputAdm29 d hd m h)
        (gridInputInt29 d hd hb m h) r j.val j.property W)
  have hpartsR : (0 : ℝ) < (exactPartsAt q b m pg dg r j.val W).card := by
    exact_mod_cast hparts
  have hparts0R : (0 : ℝ) < (exactPartsAt 0 b m pg dg r j.val W).card := by
    simpa only [exactPartsAt, stagePopulationAt_q_eq_zero38] using hpartsR
  have hpartsRaw : (0 : ℝ) <
      (Finset.filter
        ((stagePopulationAt 0 (constituentGridParent27 d hd m h)
          (constituentGridSpec27 d hd m h) b m r).incidence W j.val)
        Finset.univ).card := by
    simpa only [exactPartsAt, pg, dg] using hparts0R
  have hfinal := hdensity.trans (by simpa only [L, Nat.cast_mul] using hratio)
  rw [div_le_iff₀ hpartsRaw] at hfinal
  simpa only [exactPartsAt, stagePopulationAt_q_eq_zero38, pg, dg, N, L]
    using hfinal

end
end OmegaBound.ADVXXZGeneral
end
