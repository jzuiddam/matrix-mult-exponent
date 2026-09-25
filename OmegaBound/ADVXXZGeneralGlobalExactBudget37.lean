import OmegaBound.ADVXXZGeneralGlobalExactBudgetBounds37
import OmegaBound.ADVXXZGeneralGlobalExactModulusBranches

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# One repair budget before the grid

The finite modulus and bucket are still selected after the compatible grid, but every loss paid
by their real quotient is bounded by `globalRepairLoss37 w b`, fixed before that grid.
-/

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem budget_quotient_arith37
    {Er E P Cap R es k M T Bc ell : ℝ}
    (hEr : 0 < Er) (hE : 0 < E) (hP : 0 < P) (hCap : 0 < Cap)
    (hR : 0 < R) (hes : 0 < es) (hk : 1 ≤ k) (hM : 0 < M)
    (hMfourk : M ≤ 4*k) (hMcap : M ≤ 4*Cap*E)
    (hB : k*es⁻¹ ≤ Bc) (hT : Er*E/P ≤ T)
    (hloss : Real.log (640/11:ℝ) + Real.log Cap + Real.log P +
      Real.log R + Real.log es ≤ ell) :
    Real.exp (Real.log Er - ell) ≤ (11/40:ℝ)*T*Bc/(M^2*R) := by
  have hT0 : 0 ≤ T := (div_pos (mul_pos hEr hE) hP).le.trans hT
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hlowB0 : 0 ≤ k*es⁻¹ := mul_nonneg hk0 (inv_nonneg.mpr hes.le)
  have hB0 : 0 ≤ Bc := hlowB0.trans hB
  have hnum : (Er*E/P)*(k*es⁻¹) ≤ T*Bc :=
    mul_le_mul hT hB hlowB0 hT0
  have hMsq : M^2 ≤ 16*k*Cap*E := by
    calc
      M^2 = M*M := by ring
      _ ≤ (4*k)*(4*Cap*E) := mul_le_mul hMfourk hMcap hM.le (by positivity)
      _ = 16*k*Cap*E := by ring
  have hden : M^2*R ≤ (16*k*Cap*E)*R :=
    mul_le_mul_of_nonneg_right hMsq hR.le
  have hsmallDen : 0 < M^2*R := mul_pos (sq_pos_of_pos hM) hR
  have hquot : Er/((640/11:ℝ)*Cap*P*R*es) ≤
      (11/40:ℝ)*T*Bc/(M^2*R) := by
    calc
      Er/((640/11:ℝ)*Cap*P*R*es) =
          (11/40:ℝ)*((Er*E/P)*(k*es⁻¹))/((16*k*Cap*E)*R) := by
        field_simp [ne_of_gt hE, ne_of_gt hP, ne_of_gt hCap, ne_of_gt hR,
          ne_of_gt hes, ne_of_gt (lt_of_lt_of_le zero_lt_one hk)]
        ring
      _ ≤ (11/40:ℝ)*(T*Bc)/((16*k*Cap*E)*R) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnum (by norm_num)) (by positivity)
      _ ≤ (11/40:ℝ)*(T*Bc)/(M^2*R) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) (mul_nonneg hT0 hB0)) hsmallDen hden
      _ = (11/40:ℝ)*T*Bc/(M^2*R) := by ring
  have hratio : (0:ℝ) < 640/11 := by norm_num
  have hexpTerms : Real.exp (Real.log (640/11:ℝ) + Real.log Cap + Real.log P +
      Real.log R + Real.log es) = (640/11:ℝ)*Cap*P*R*es := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log hratio, Real.exp_log hCap, Real.exp_log hP,
      Real.exp_log hR, Real.exp_log hes]
  calc
    Real.exp (Real.log Er-ell) ≤ Real.exp (Real.log Er-
        (Real.log (640/11:ℝ)+Real.log Cap+Real.log P+Real.log R+Real.log es)) := by
      exact Real.exp_le_exp.mpr (sub_le_sub_left hloss _)
    _ = Er/((640/11:ℝ)*Cap*P*R*es) := by
      rw [Real.exp_sub, Real.exp_log hEr, hexpTerms]
    _ ≤ (11/40:ℝ)*T*Bc/(M^2*R) := hquot

set_option maxHeartbeats 1200000 in
-- Expanding the dependent exact-grid demand cap requires a larger local elaboration budget.
private theorem globalRepairLoss37_covers_region
    {w b m : ℕ} (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (hb : GlobalIntegral g b) (xi : ExactGrid g (b*m))
    (hxi : GridBoundaryCompatible xi) (r : Fin 6) (k : ℕ)
    (hupper : 2*k+1 ≤ 2*max (max 0 (2*w+3))
      (2*globalDemand g b 0 m xi r))
    (hodd : 2 < 2*k+1) (j0 : GlobalTargetLabel27 g xi r)
    (hm : 0 < m) (hn : (globalPopulation g (b*m) xi r).n ≠ 0) :
    Real.log (640/11:ℝ) + Real.log (globalDemandCap27 w b 0 m) +
        Real.log ((((globalPopulation g (b*m) xi r).n:ℝ)+1)^
          Fintype.card (Shape w)) +
        Real.log (repairReserve (2*(globalPopulation g (b*m) xi r).n)
          (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ) +
        4*Real.sqrt (Real.log k) ≤ globalRepairLoss37 w b m := by
  let N : ℕ := (globalPopulation g (b*m) xi r).n
  let x : ℝ := globalBudgetScale37 b m
  let C : ℝ := globalBudgetPolyConst37 w
  let d : ℕ := globalBudgetPolyDegree37 w
  let Q : ℕ := Fintype.card (Shape w)
  let Cap : ℝ := globalDemandCap27 w b 0 m
  let R : ℕ := repairReserve (2*N)
    (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W))
  have hx : 1 ≤ x := globalBudgetScale37_one_le b m
  have hC : 1 ≤ C := globalBudgetPolyConst37_one_le w
  have hCap : 0 < Cap := by
    dsimp only [Cap]
    exact globalDemandCap27_pos w b 0 m
  have hR : 0 < R := repairReserve_pos _ _
  have hQnat : 0 < Q := by
    dsimp only [Q]
    exact Fintype.card_pos
  have hQ : (1:ℝ) ≤ Q := by exact_mod_cast hQnat
  have hlogQ : 0 ≤ Real.log (Q:ℝ) := Real.log_nonneg hQ
  have hNbm : N ≤ b*m := globalPopulation_n_le27 g xi hb r
  have hNx : (N:ℝ)+1 ≤ x := by
    dsimp only [N, x, globalBudgetScale37]
    exact_mod_cast Nat.add_le_add_right hNbm 1
  have hcapPoly : Cap ≤ C*x^d := by
    dsimp only [Cap, C, x, d]
    exact globalDemandCap27_le_budgetPoly37 w b m
  have hlogCap : Real.log Cap ≤ Real.log C + (d:ℝ)*Real.log x := by
    have hlog := Real.log_le_log hCap hcapPoly
    calc
      Real.log Cap ≤ Real.log (C*x^d) := hlog
      _ = Real.log C + (d:ℝ)*Real.log x := by
        rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hC)) (by positivity),
          Real.log_pow]
  have hlogP : Real.log (((N:ℝ)+1)^Q) ≤ (Q:ℝ)*Real.log x := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) hNx) (Nat.cast_nonneg _)
  have hRcapNat : R ≤ globalRepairCap37 w b m := by
    dsimp only [R, N]
    exact globalRepairReserve_le_cap37 g hg hb xi r j0 hm hn
  have hlogR : Real.log (R:ℝ) ≤ Real.log (globalRepairCap37 w b m:ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hR
    · exact_mod_cast hRcapNat
  have hk : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  let dbits : ℝ := globalDemandBits27 g xi r
  let ErD : ℝ := Real.exp ((N:ℝ)*Real.log 2*dbits)
  have hdbits0 : 0 ≤ dbits := by
    dsimp only [dbits]
    exact globalDemandBits_nonneg27 g xi r
  have hErD : 0 < ErD := Real.exp_pos _
  have hDemand : (globalDemand g b 0 m xi r:ℝ) ≤ Cap*ErD := by
    dsimp only [Cap, ErD, dbits, N]
    exact globalDemand_paper_cap27 g hg hb 0 xi hxi r hn
  have hfloor : 2*w+3 ≤ globalDemand g b 0 m xi r := by
    simpa using globalDemand_floor_le g 0 m xi r
  have hMnat : 2*k+1 ≤ 4*globalDemand g b 0 m xi r := by
    calc
      2*k+1 ≤ 2*max (max 0 (2*w+3)) (2*globalDemand g b 0 m xi r) := hupper
      _ = 4*globalDemand g b 0 m xi r := by
        rw [max_eq_right]
        · ring
        · simp only [max_eq_right (Nat.zero_le _)]
          omega
  have hkCap : (k:ℝ) ≤ 4*Cap*ErD := by
    have hkM : k ≤ 2*k+1 := by omega
    have hreal : (k:ℝ) ≤ 4*(globalDemand g b 0 m xi r:ℝ) := by
      exact_mod_cast hkM.trans hMnat
    have hfour := mul_le_mul_of_nonneg_left hDemand (by norm_num : (0:ℝ) ≤ 4)
    nlinarith [hreal, hfour]
  have hrate := globalRegionRate_nonneg27 g xi r
  have hid := globalRegionRate_eq_entropy_sub_demand27 g xi r
  have hdbitsEntropy : dbits ≤ entropy ((g.alpha r).probR) := by
    dsimp only [dbits]
    linarith
  have hEntropy := entropy_le_logb_card27 (g.alpha r).probR
    ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbitsQ : Real.log 2*dbits ≤ Real.log (Q:ℝ) := by
    have hdbQ : dbits ≤ Real.log (Q:ℝ)/Real.log 2 := by
      dsimp only [Q]
      exact hdbitsEntropy.trans hEntropy
    have := (le_div_iff₀ hlog2).mp hdbQ
    simpa only [mul_comm] using this
  have hErDexp : Real.log ErD ≤ (N:ℝ)*Real.log (Q:ℝ) := by
    rw [show Real.log ErD = (N:ℝ)*Real.log 2*dbits by
      dsimp only [ErD]; rw [Real.log_exp]]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hbitsQ (show (0:ℝ) ≤ N from Nat.cast_nonneg _)
  have hlogk : Real.log k ≤ Real.log (4*C) + (d:ℝ)*Real.log x +
      (N:ℝ)*Real.log (Q:ℝ) := by
    have hkPoly : (k:ℝ) ≤ (4*C*x^d)*ErD := by
      have h4cap : 4*Cap ≤ 4*(C*x^d) :=
        mul_le_mul_of_nonneg_left hcapPoly (by norm_num)
      calc
        (k:ℝ) ≤ 4*Cap*ErD := hkCap
        _ ≤ (4*(C*x^d))*ErD := mul_le_mul_of_nonneg_right h4cap hErD.le
        _ = (4*C*x^d)*ErD := by ring
    have hlog := Real.log_le_log hkpos hkPoly
    calc
      Real.log k ≤ Real.log ((4*C*x^d)*ErD) := hlog
      _ = Real.log (4*C) + (d:ℝ)*Real.log x + Real.log ErD := by
        rw [Real.log_mul (by positivity) (ne_of_gt hErD),
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
      _ ≤ Real.log (4*C) + (d:ℝ)*Real.log x +
          (N:ℝ)*Real.log (Q:ℝ) := by
        simpa only [add_assoc, add_comm, add_left_comm] using
          add_le_add_left hErDexp (Real.log (4*C)+(d:ℝ)*Real.log x)
  have hlogx : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hx)
    linarith
  have hNlogQ : (N:ℝ)*Real.log (Q:ℝ) ≤ x*Real.log (Q:ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [hNx]) hlogQ
  have hrootScale : Real.log k ≤ globalBudgetRootConst37 w*x := by
    have hlog4C : 0 ≤ Real.log (4*C) := by
      apply Real.log_nonneg
      nlinarith
    have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
    have h1 : Real.log (4*C) ≤ Real.log (4*C)*x := by nlinarith
    have h2 : (d:ℝ)*Real.log x ≤ (d:ℝ)*x :=
      mul_le_mul_of_nonneg_left hlogx hd0
    have h3 := hNlogQ
    calc
      Real.log k ≤ Real.log (4*C)+(d:ℝ)*Real.log x+(N:ℝ)*Real.log (Q:ℝ) := hlogk
      _ ≤ Real.log (4*C)*x + (d:ℝ)*x + x*Real.log (Q:ℝ) :=
        add_le_add (add_le_add h1 h2) h3
      _ = (Real.log (4*C)+(d:ℝ)+Real.log (Q:ℝ))*x := by ring
      _ = globalBudgetRootConst37 w*x := by
        dsimp only [C, d, Q, globalBudgetRootConst37]
  have hsqrt : 4*Real.sqrt (Real.log k) ≤
      4*Real.sqrt (globalBudgetRootConst37 w)*Real.sqrt x := by
    have hroot0 := globalBudgetRootConst37_nonneg w
    have hs := Real.sqrt_le_sqrt hrootScale
    rw [Real.sqrt_mul hroot0] at hs
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 4)
  calc
    Real.log (640/11:ℝ)+Real.log Cap+Real.log (((N:ℝ)+1)^Q)+
        Real.log (R:ℝ)+4*Real.sqrt (Real.log k) ≤
      Real.log (640/11:ℝ)+(Real.log C+(d:ℝ)*Real.log x)+
        (Q:ℝ)*Real.log x+Real.log (globalRepairCap37 w b m:ℝ)+
        4*Real.sqrt (globalBudgetRootConst37 w)*Real.sqrt x :=
      add_le_add (add_le_add (add_le_add (add_le_add le_rfl hlogCap) hlogP) hlogR) hsqrt
    _ = globalRepairLoss37 w b m := by
      unfold globalRepairLoss37
      dsimp only [Cap, R, N, x, C, d, Q]
      push_cast
      ring

set_option maxHeartbeats 600000 in
/-- **One repair budget before the grid.** -/
theorem globalRepairBudget_uniform37 : GlobalExactEnvelope37.globalRepairBudget_uniform37 := by
  intro w b g hg hw hb
  refine ⟨globalRepairLoss37 w b, globalRepairLoss37_nonneg w b,
    globalRepairLoss37_sublinear w b hb.1, 0, ?_⟩
  intro m hLm hm xi hxi
  obtain ⟨k, B, hvalid, hbounds, hbucket⟩ :=
    global_demand_valid_hashes_with_buckets27 g 0 m xi
  refine ⟨k, B, hvalid, fun r => (hbounds r).1,
    fun r => Finset.nonempty_coe_sort.mp (hbucket r), ?_⟩
  intro r hn j0
  let N : ℕ := (globalPopulation g (b*m) xi r).n
  let H : ℝ := entropy ((g.alpha r).probR)
  let dbits : ℝ := globalDemandBits27 g xi r
  let rate : ℝ := globalRegionRate (globalExactGridData27 g xi) r
  let Er : ℝ := Real.exp ((N:ℝ)*Real.log 2*rate)
  let E : ℝ := Real.exp ((N:ℝ)*Real.log 2*dbits)
  let P : ℝ := ((N:ℝ)+1)^Fintype.card (Shape w)
  let Cap : ℝ := globalDemandCap27 w b 0 m
  let R : ℝ := (repairReserve (2*N)
    (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)):ℝ)
  let es : ℝ := Real.exp (4*Real.sqrt (Real.log (k r)))
  let M : ℝ := ((2*k r+1:ℕ):ℝ)
  let T : ℝ := (Fintype.card (GlobalTargetLabel27 g xi r):ℝ)
  let Bc : ℝ := (Fintype.card (GlobalBucketLabel27 (B r)):ℝ)
  have hk : 1 ≤ k r := by
    have hodd : 2 < 2*k r+1 := by simpa using (hvalid r).2.1
    omega
  have hM : 0 < M := by dsimp only [M]; positivity
  have hMfourk : M ≤ 4*(k r:ℝ) := by
    dsimp only [M]
    push_cast
    nlinarith [show (1:ℝ) ≤ k r by exact_mod_cast hk]
  have hCap : 0 < Cap := by dsimp only [Cap]; exact globalDemandCap27_pos w b 0 m
  have hE : 0 < E := Real.exp_pos _
  have hDemand : (globalDemand g b 0 m xi r:ℝ) ≤ Cap*E := by
    dsimp only [Cap, E, dbits, N]
    exact globalDemand_paper_cap27 g hg hb 0 xi hxi r hn
  have hMcap : M ≤ 4*Cap*E := by
    have hfloor : 2*w+3 ≤ globalDemand g b 0 m xi r := by
      simpa using globalDemand_floor_le g 0 m xi r
    have hMn : 2*k r+1 ≤ 4*globalDemand g b 0 m xi r := by
      calc
        2*k r+1 ≤ 2*max (max 0 (2*w+3)) (2*globalDemand g b 0 m xi r) :=
          (hbounds r).2.1
        _ = 4*globalDemand g b 0 m xi r := by
          rw [max_eq_right]
          · ring
          · simp only [max_eq_right (Nat.zero_le _)]
            omega
    have hreal : M ≤ 4*(globalDemand g b 0 m xi r:ℝ) := by
      dsimp only [M]
      exact_mod_cast hMn
    have := mul_le_mul_of_nonneg_left hDemand (by norm_num : (0:ℝ) ≤ 4)
    nlinarith
  have hEr : 0 < Er := Real.exp_pos _
  have hP : 0 < P := by dsimp only [P]; positivity
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast repairReserve_pos (2*N)
      (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W))
  have hes : 0 < es := Real.exp_pos _
  have hB : (k r:ℝ)*es⁻¹ ≤ Bc := by
    have hbehrend := CW90.card_apFree_zmod_lower (k r)
    rw [← (hbounds r).2.2] at hbehrend
    dsimp only [Bc, es]
    rw [show Fintype.card (GlobalBucketLabel27 (B r)) = (B r).card from
      Fintype.card_coe (B r)]
    rw [← Real.exp_neg]
    simpa only [neg_mul] using hbehrend
  have hsplit : Er*E = Real.exp ((N:ℝ)*Real.log 2*H) := by
    rw [show Er*E = Real.exp ((N:ℝ)*Real.log 2*rate +
        (N:ℝ)*Real.log 2*dbits) by
      dsimp only [Er, E]; rw [Real.exp_add]]
    congr 1
    have hid := globalRegionRate_eq_entropy_sub_demand27 g xi r
    dsimp only [rate, dbits, H]
    rw [hid]
    ring
  have hT : Er*E/P ≤ T := by
    rw [hsplit]
    dsimp only [P, T, H, N]
    have hTbank := (globalTargetLabel_paper_entropy_bounds27 g hg hb xi r hn).1
    dsimp only [GlobalSpec.toPaper] at hTbank
    change Real.exp (((globalPopulation g (b*m) xi r).n:ℝ)*
        (Real.log 2*entropy ((g.alpha r).probR))) /
          (((globalPopulation g (b*m) xi r).n:ℝ)+1)^Fintype.card (Shape w) ≤
        (Fintype.card (GlobalTargetLabel27 g xi r):ℝ) at hTbank
    simpa only [mul_assoc] using hTbank
  have hloss0 := globalRepairLoss37_covers_region g hg hb xi hxi r (k r)
    (hbounds r).2.1 (hvalid r).2.1 j0 hm hn
  have hloss : Real.log (640/11:ℝ)+Real.log Cap+Real.log P+Real.log R+
      Real.log es ≤ globalRepairLoss37 w b m := by
    dsimp only [Cap, P, R, N, es]
    rw [Real.log_exp]
    exact hloss0
  have harith := budget_quotient_arith37 hEr hE hP hCap hR hes
    (by exact_mod_cast hk) hM hMfourk hMcap hB hT hloss
  dsimp only [Er, M, T, Bc, R, rate, N] at harith ⊢
  rw [Real.log_exp] at harith
  exact harith

theorem globalRepairBudget_uniform37_matches_display :
    GlobalExactEnvelope37.globalRepairBudget_uniform37 := globalRepairBudget_uniform37

end
end OmegaBound.ADVXXZGeneral
end
