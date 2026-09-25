import OmegaBound.ADVXXZGeneralCExact41BrokenSupply
import OmegaBound.ADVXXZGeneralGridInput29Facts

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

noncomputable instance constituentExactGridFintype42 {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ) :
    Fintype (ConstituentExactGrid27 d m) := by
  unfold ConstituentExactGrid27
  infer_instance

noncomputable instance constituentFullGridFintype42 {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ) (ε : ℚ) :
    Fintype (ConstituentFullGrid27 d m ε) := by
  unfold ConstituentFullGrid27
  infer_instance

private theorem stageCount_le_total42 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hb : StepIntegralAt p d b) (m : ℕ)
    (r : Fin 6) (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    stageCounts27 m p d r W t u σ ≤ m * d.outBase ⟨t,r,u⟩ := by
  calc
    stageCounts27 m p d r W t u σ ≤ ∑ τ, stageCounts27 m p d r W t u τ :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
    _ = m * d.outBase ⟨t,r,u⟩ := stageCounts27_sum p d hb m r W t u

/-- The original integral child histograms, regarded as one exact grid. -/
noncomputable def constituentCentreExactGrid42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) (m : ℕ) :
    ConstituentExactGrid27 d m := by
  let C := fun (i : Fin (Fintype.card (ConstituentTerm p))) (W : Side) (σ : Chunk w) =>
    stageCounts27 m p d (constituentIndex i).2.1 W
      (constituentIndex i).1 (constituentIndex i).2.2 σ
  refine ⟨fun i W σ => ⟨C i W σ, ?_⟩, ?_, ?_⟩
  · apply Nat.lt_succ_of_le
    simpa only [C, constituentOutN, Nat.mul_comm] using
      stageCount_le_total42 d hb m (constituentIndex i).2.1 W
        (constituentIndex i).1 (constituentIndex i).2.2 σ
  · intro i W
    simpa only [C, constituentOutN, Nat.mul_comm] using
      stageCounts27_sum p d hb m (constituentIndex i).2.1 W
        (constituentIndex i).1 (constituentIndex i).2.2
  · intro i W σ hC
    apply hd.child_support W (constituentIndex i).1 (constituentIndex i).2.1
      (constituentIndex i).2.2 σ
    intro hnum
    have hprob :
        (d.betaChild W (constituentIndex i).1 (constituentIndex i).2.1
          (constituentIndex i).2.2).prob σ = 0 := by
      simp [RatDist.prob, hnum]
    apply hC
    simp only [C, stageCounts27, hprob, mul_zero]
    change (0 : ℤ).toNat = 0
    rfl

private theorem centre_ratio42 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (W : Side) (t : Fin s)
    (r : Fin 6) (u : ChildShape p t) (σ : Chunk w)
    (hn : 0 < constituentOutN d.toPaper m
      (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩)) :
    (((constituentCentreExactGrid42 d hd hb m).val
        (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) W σ).val : ℚ) /
      (constituentOutN d.toPaper m
        (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) : ℚ) =
      (d.betaChild W t r u).prob σ := by
  have hc := (inputInt29_of_stepIntegralAt hb m).countsExact r W t u σ
  have hN := constituentOutN_grid_index d m t r u
  have hN0 : (m : ℚ) * d.outBase ⟨t,r,u⟩ ≠ 0 := by
    exact_mod_cast (show m * d.outBase ⟨t,r,u⟩ ≠ 0 by
      rw [Nat.mul_comm, ← hN]
      exact hn.ne')
  have hi : constituentIndex (p := p)
      (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) = ⟨t,r,u⟩ :=
    (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨t,r,u⟩
  rw [show ((constituentCentreExactGrid42 d hd hb m).val
      (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) W σ).val =
        stageCounts27 m p d r W t u σ by
          change stageCounts27 m p d
            (constituentIndex (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩)).2.1 W
            (constituentIndex (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩)).1
            (constituentIndex (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩)).2.2 σ = _
          rw [hi]]
  rw [hc, hN]
  push_cast
  rw [mul_comm (d.outBase ⟨t,r,u⟩ : ℚ) (m : ℚ)]
  exact (mul_div_cancel_left₀ _ hN0)

/-- The centre grid is a full grid at every nonnegative tolerance. -/
noncomputable def constituentCentreFullGrid42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (m : ℕ) (ε : ℚ) (hε : 0 ≤ ε) : ConstituentFullGrid27 d m ε := by
  refine ⟨constituentCentreExactGrid42 d hd hb m, ?_⟩
  intro i W hn σ
  let a := constituentIndex (p := p) i
  have hi : Fintype.equivFin (ConstituentTerm p) a = i := by
    simp [a, constituentIndex]
  have hn' : 0 < constituentOutN d.toPaper m
      (Fintype.equivFin (ConstituentTerm p) ⟨a.1,a.2.1,a.2.2⟩) := by
    simpa only [hi] using hn
  have hr := centre_ratio42 d hd hb m W a.1 a.2.1 a.2.2 σ hn'
  have ha : (⟨a.1,a.2.1,a.2.2⟩ : ConstituentTerm p) = a := by
    rcases a with ⟨t,r,u⟩
    rfl
  rw [show i = Fintype.equivFin (ConstituentTerm p) ⟨a.1,a.2.1,a.2.2⟩ by
    exact hi.symm]
  rw [hr]
  have hout : constituentOutBeta d.toPaper W
      (Fintype.equivFin (ConstituentTerm p) ⟨a.1,a.2.1,a.2.2⟩) =
      d.betaChild W a.1 a.2.1 a.2.2 := by
    rw [ha]
    change d.betaChild W
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).1
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).2.1
      (constituentIndex (Fintype.equivFin (ConstituentTerm p) a)).2.2 = _
    have hia : constituentIndex (p := p) (Fintype.equivFin (ConstituentTerm p) a) = a :=
      (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply a
    rw [hia]
  rw [hout, sub_self, abs_zero]
  exact hε

/-- Every empirical child probability of the centre grid is the original child law. -/
theorem constituentCentreGridBeta_prob42 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (W : Side) (t : Fin s)
    (r : Fin 6) (u : ChildShape p t) (σ : Chunk w) :
    (constituentGridBeta27 d m (constituentCentreExactGrid42 d hd hb m) W t r u).prob σ =
      (d.betaChild W t r u).prob σ := by
  by_cases hn : 0 < constituentOutN d.toPaper m
      (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩)
  · rw [constituentGridBeta27_prob_pos d m _ W t r u σ hn]
    exact centre_ratio42 d hd hb m W t r u σ hn
  · unfold constituentGridBeta27
    dsimp only
    rw [dif_neg hn]

/-- The centre grid's regional mixtures are the original regional laws. -/
theorem constituentCentreGridRegion_prob42 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (W : Side) (t : Fin s)
    (r : Fin 6) (σ : Chunk (w+w)) :
    (constituentGridRegionBeta27 d m (constituentCentreExactGrid42 d hd hb m) W t r).prob σ =
      (d.betaRegion W t r).prob σ := by
  rw [constituentGridSpec27_pair_mixture]
  simp_rw [constituentCentreGridBeta_prob42 d hd hb m]
  exact (hd.pair_mixture W t r σ).symm

/-- The centre grid parent has exactly the original parent probabilities. -/
theorem constituentCentreGridParent_prob42 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (W : Side) (t : Fin s)
    (σ : Chunk (w+w)) :
    ((constituentGridParent27 d hd m
      (constituentCentreExactGrid42 d hd hb m)).beta W t).prob σ =
      (p.beta W t).prob σ := by
  change (mixtureDist27 (d.A t)
      (constituentGridRegionBeta27 d m (constituentCentreExactGrid42 d hd hb m) W t)).prob σ = _
  rw [mixtureDist27_prob]
  simp_rw [constituentCentreGridRegion_prob42 d hd hb m]
  exact (hd.mixture W t σ).symm

end
end OmegaBound.ADVXXZGeneral
end
