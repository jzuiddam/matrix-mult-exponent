import OmegaBound.ADVXXZGeneralCExact41SelectionLoss
import OmegaBound.ADVXXZGeneralCExact36SelectionBoundary

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem c41_vanishes_add {f g : ℚ → ℝ}
    (hf : VanishesWithTolerance f) (hg : VanishesWithTolerance g) :
    VanishesWithTolerance (fun ε => f ε + g ε) := by
  constructor
  · intro ε
    exact add_nonneg (hf.1 ε) (hg.1 ε)
  · intro ζ hζ
    obtain ⟨εf, hεf, hsmallf⟩ := hf.2 (ζ / 2) (half_pos hζ)
    obtain ⟨εg, hεg, hsmallg⟩ := hg.2 (ζ / 2) (half_pos hζ)
    refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    intro ε hε hεle
    have hf' := hsmallf ε hε (hεle.trans (min_le_left _ _))
    have hg' := hsmallg ε hε (hεle.trans (min_le_right _ _))
    rw [abs_of_nonneg (add_nonneg (hf.1 ε) (hg.1 ε))]
    rw [abs_of_nonneg (hf.1 ε)] at hf'
    rw [abs_of_nonneg (hg.1 ε)] at hg'
    linarith

private theorem c41_vanishes_rat_abs :
    VanishesWithTolerance (fun ε : ℚ => |(ε : ℝ)|) := by
  constructor
  · intro ε
    exact abs_nonneg _
  · intro ζ hζ
    obtain ⟨ε₀, hε0, hεζ⟩ := exists_rat_btwn hζ
    have hε0Q : 0 < ε₀ := by exact_mod_cast hε0
    refine ⟨ε₀, hε0Q, ?_⟩
    intro ε hε hεle
    rw [abs_of_nonneg (abs_nonneg _), abs_of_pos (by exact_mod_cast hε)]
    have hεleR : (ε : ℝ) ≤ (ε₀ : ℝ) := by exact_mod_cast hεle
    exact hεleR.trans hεζ.le

/-- The single vanishing debit used by the selection theorem. -/
noncomputable def constituentSelectionDelta41 {w s : ℕ}
    (p : ConstituentInput w s) (rho : ℚ → ℝ) (ε : ℚ) : ℝ :=
  rho ε + constituentPCompDelta40 p ε + |(ε : ℝ)|

theorem constituentSelectionDelta_vanishes41 {w s : ℕ}
    (p : ConstituentInput w s) {rho : ℚ → ℝ}
    (hrho : VanishesWithTolerance rho) :
    VanishesWithTolerance (constituentSelectionDelta41 p rho) := by
  unfold constituentSelectionDelta41
  exact c41_vanishes_add
    (c41_vanishes_add hrho (constituentPCompDelta40_vanishes p))
    c41_vanishes_rat_abs

private theorem c41_grid_demandExponent_le {w s b m : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (h : ConstituentFullGrid27 d m ε)
    (rho : ℚ → ℝ)
    (hrate : ∀ r : Fin 6,
      Real.log 2 * constituentRegionRate d.toPaper r - rho ε ≤
        Real.log 2 * constituentRegionRate
          (constituentGridSpec27 d hd m h.val).toPaper r)
    (r : Fin 6) :
    demandExponent (constituentGridParent27 d hd m h.val)
        (constituentGridSpec27 d hd m h.val) r ≤
      demandExponent p d r + rho ε := by
  let pg := constituentGridParent27 d hd m h.val
  let dg := constituentGridSpec27 d hd m h.val
  have hfixed : constituentAlphaNats41 pg dg r = constituentAlphaNats41 p d r := by
    rfl
  have hgrid := constituentAlphaNats_sub_demand41 pg dg r
  have horig := constituentAlphaNats_sub_demand41 p d r
  dsimp only [pg, dg] at hfixed hgrid
  have hr := hrate r
  rw [← hgrid, hfixed, ← horig] at hr
  linarith

private theorem c41_reserve_log_le {q w s b m : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) (r : Fin 6)
    {a : ℝ}
    (hpool : |Real.log (constituentRepairPool33 q p d b m : ℝ)| ≤ a) :
    Real.log (constituentRegionalReserve33 q P r : ℝ) ≤ a := by
  classical
  have hresprod : constituentRegionalReserve33 q P r ≤
      ∏ i : Fin 6, constituentRegionalReserve33 q P i := by
    have hrestpos : 0 < (Finset.univ.erase r).prod
        (fun i : Fin 6 => constituentRegionalReserve33 q P i) :=
      Finset.prod_pos fun i _ => constituentRegionalReserve33_pos q P i
    calc
      constituentRegionalReserve33 q P r =
          1 * constituentRegionalReserve33 q P r := by simp
      _ ≤ (Finset.univ.erase r).prod
          (fun i : Fin 6 => constituentRegionalReserve33 q P i) *
          constituentRegionalReserve33 q P r := by
        exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hrestpos)
      _ = ∏ i : Fin 6, constituentRegionalReserve33 q P i :=
        Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ r)
  have hrespool : constituentRegionalReserve33 q P r ≤
      constituentRepairPool33 q p d b m :=
    hresprod.trans (constituent_reserve_pool_dominated33 q P)
  have hresposR : (0 : ℝ) < constituentRegionalReserve33 q P r := by
    exact_mod_cast constituentRegionalReserve33_pos q P r
  have hlogle : Real.log (constituentRegionalReserve33 q P r : ℝ) ≤
      Real.log (constituentRepairPool33 q p d b m : ℝ) := by
    exact Real.log_le_log hresposR (by exact_mod_cast hrespool)
  exact hlogle.trans ((le_abs_self _).trans hpool)

private theorem c41_log_k_le_root {w s b m k : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (floor : ℕ)
    (rho : ℚ → ℝ) (hrho : VanishesWithTolerance rho)
    (hb : 0 < b) (r : Fin 6) (hk : 1 ≤ k)
    (hdemandGrid : ℝ)
    (hdemandRate : hdemandGrid ≤ demandExponent p d r + rho ε)
    (hkle : (k : ℝ) ≤ 4 * constituentDemandCap40 p b floor m *
      Real.exp ((hdemandGrid + constituentPCompDelta40 p ε) * (b * m : ℝ))) :
    Real.log k ≤ constituentSelectionRootCoeff41 p d b floor rho ε *
      ((cLength p b m : ℝ) + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcap : 0 < constituentDemandCap40 p b floor m := by
    unfold constituentDemandCap40
    exact Real.exp_pos _
  have hlog := Real.log_le_log hkR hkle
  have hlogCap : Real.log (constituentDemandCap40 p b floor m) =
      constituentDemandLogLoss40 p b floor m := by
    unfold constituentDemandCap40
    rw [Real.log_exp]
  have hstep : Real.log k ≤ Real.log 4 +
      constituentDemandCoeff41 p b floor * Real.log ((m : ℝ) + 1) +
      (demandExponent p d r + rho ε + constituentPCompDelta40 p ε) *
        (b * m : ℝ) := by
    calc
      Real.log k ≤ Real.log (4 * constituentDemandCap40 p b floor m *
          Real.exp ((hdemandGrid + constituentPCompDelta40 p ε) *
            (b * m : ℝ))) := hlog
      _ = Real.log 4 + constituentDemandLogLoss40 p b floor m +
          (hdemandGrid + constituentPCompDelta40 p ε) * (b * m : ℝ) := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hcap))
              (ne_of_gt (Real.exp_pos _)),
          Real.log_mul (by norm_num) (ne_of_gt hcap),
          Real.log_exp, hlogCap]
      _ = Real.log 4 + constituentDemandCoeff41 p b floor *
          Real.log ((m : ℝ) + 1) +
          (hdemandGrid + constituentPCompDelta40 p ε) * (b * m : ℝ) := by
        rw [constituentDemandLogLoss_eq41]
      _ ≤ _ := by
        have hbm : (0 : ℝ) ≤ b * m := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hdemandRate hbm]
  let L : ℝ := cLength p b m
  have hmLnat : m ≤ cLength p b m := le_cLength 1 p d b m hb
  have hbmLnat : b * m ≤ cLength p b m := by
    unfold cLength
    calc
      b * m = 1 * (b * m) := by ring
      _ ≤ constituentBaseTotal p * (b * m) := by
        apply Nat.mul_le_mul_right
        exact Nat.succ_le_iff.mpr (by
          unfold constituentBaseTotal
          let t : Fin s := ⟨0, p.terms_nonempty⟩
          exact lt_of_lt_of_le (p.baseN_pos t)
            (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)))
  have hmL : (m : ℝ) ≤ L := by
    dsimp only [L]
    exact_mod_cast hmLnat
  have hbmL : (b * m : ℝ) ≤ L := by
    dsimp only [L]
    exact_mod_cast hbmLnat
  have hlogm : Real.log ((m : ℝ) + 1) ≤ L + 1 := by
    have hpos : 0 < (m : ℝ) + 1 := by positivity
    have hbase := Real.log_le_sub_one_of_pos hpos
    linarith
  have horig : demandExponent p d r ≤ ∑ i : Fin 6, |demandExponent p d i| := by
    exact (le_abs_self _).trans
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin 6 => |demandExponent p d i|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ r))
  have hcoefAbs : 0 ≤ (∑ i : Fin 6, |demandExponent p d i|) + rho ε +
      constituentPCompDelta40 p ε := by
    exact add_nonneg
      (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hrho.1 ε))
      ((constituentPCompDelta40_vanishes p).1 ε)
  have hL1 : 0 ≤ L + 1 := by
    have hL : 0 ≤ L := by dsimp only [L]; positivity
    linarith
  calc
    Real.log k ≤ Real.log 4 + constituentDemandCoeff41 p b floor *
        Real.log ((m : ℝ) + 1) +
        (demandExponent p d r + rho ε + constituentPCompDelta40 p ε) *
          (b * m : ℝ) := hstep
    _ ≤ Real.log 4 * (L + 1) +
        constituentDemandCoeff41 p b floor * (L + 1) +
        ((∑ i : Fin 6, |demandExponent p d i|) + rho ε +
          constituentPCompDelta40 p ε) * (L + 1) := by
      apply add_le_add
      · apply add_le_add
        · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          have hone : 1 ≤ L + 1 := by
            have hL : 0 ≤ L := by dsimp only [L]; positivity
            linarith
          calc
            Real.log 4 = Real.log 4 * 1 := by ring
            _ ≤ Real.log 4 * (L + 1) := mul_le_mul_of_nonneg_left hone hlog4
        · exact mul_le_mul_of_nonneg_left hlogm
            (constituentDemandCoeff_nonneg41 p b floor)
      · calc
          (demandExponent p d r + rho ε + constituentPCompDelta40 p ε) *
              (b * m : ℝ) ≤
            ((∑ i : Fin 6, |demandExponent p d i|) + rho ε +
              constituentPCompDelta40 p ε) * (b * m : ℝ) := by
                apply mul_le_mul_of_nonneg_right
                · linarith [horig]
                · positivity
          _ ≤ ((∑ i : Fin 6, |demandExponent p d i|) + rho ε +
              constituentPCompDelta40 p ε) * (L + 1) :=
            mul_le_mul_of_nonneg_left (hbmL.trans (by linarith)) hcoefAbs
    _ = constituentSelectionRootCoeff41 p d b floor rho ε * (L + 1) := by
      unfold constituentSelectionRootCoeff41
      ring

set_option maxHeartbeats 2000000 in
-- The six region choices and the final exponent normalization need one local elaboration budget.
/-- The selection-count statement `S_constituent_grid_selection_count36`. -/
theorem constituent_grid_selection_count41 : S_constituent_grid_selection_count36 := by
  intro q w s b hq hw p d hd hb
  let floor : ℕ := 2 * (w + w) + 3
  obtain ⟨rho, hrho, hrate⟩ := constituent_grid_rate_ge_rate_sub_rho d hd
  let delta : ℚ → ℝ := constituentSelectionDelta41 p rho
  let ell : ℚ → ℕ → ℝ := constituentSelectionLoss41 p d b floor rho
  have hdelta : VanishesWithTolerance delta :=
    constituentSelectionDelta_vanishes41 p hrho
  have hell : ConstituentFiniteLoss29 p b ell := by
    exact constituentSelectionLoss_finite41 p d hb.1 floor rho hrho
  refine ⟨delta, ell, hdelta, hell, ?_⟩
  intro ε hε
  obtain ⟨Minput, hinput⟩ :=
    constituent_grid_input_half_threshold38 q w s b hq p d hd hb ε hε
  obtain ⟨Mscale, hscale⟩ := constituent_grid_hole_scale_threshold39 q d hd hb
  have hsub := constituent_repair_pool_sublinear33 q w s b hq hw p d hd hb
  obtain ⟨Mreserve, hreserve⟩ := hsub (ε : ℝ) (by exact_mod_cast hε)
  let M : ℕ := max 1 (max Minput (max Mscale Mreserve))
  refine ⟨M, ?_⟩
  intro m hm h
  have hmpos : 0 < m := (Nat.succ_le_iff.mp ((le_max_left _ _).trans hm))
  have hmInput : Minput ≤ m := by
    exact (le_max_left Minput (max Mscale Mreserve)).trans
      ((le_max_right 1 _).trans hm)
  have hmScale : Mscale ≤ m := by
    exact (le_max_left Mscale Mreserve).trans
      ((le_max_right Minput _).trans ((le_max_right 1 _).trans hm))
  have hmReserve : Mreserve ≤ m := by
    exact (le_max_right Mscale Mreserve).trans
      ((le_max_right Minput _).trans ((le_max_right 1 _).trans hm))
  have hscale' := hscale m hmScale h.val
  have hinput' := hinput m hmInput
  rcases constituent_grid_raw_selection39 q hq d hd hb floor ε hε m h
      hscale' (fun r j W => hinput' h.val r j W) with hzero | ⟨k, B, P, hbounds, hcount⟩
  · left
    intro x y z
    exact congrFun (congrFun (congrFun hzero x) y) z
  · rcases constituent_grid_boundary_or_zero28 q d m h.val with hboundary | hzero'
    · right
      refine ⟨P, ?_⟩
      intro r hn
      let pg := constituentGridParent27 d hd m h.val
      let dg := constituentGridSpec27 d hd m h.val
      let bm : ℝ := b * m
      let L : ℝ := cLength p b m
      let rate0 : ℝ := Real.log 2 * constituentRegionRate d.toPaper r
      let rateg : ℝ := Real.log 2 * constituentRegionRate dg.toPaper r
      let demandg : ℝ := demandExponent pg dg r
      let Er : ℝ := Real.exp ((rate0 - rho ε - constituentPCompDelta40 p ε) * bm)
      let E : ℝ := Real.exp ((demandg + constituentPCompDelta40 p ε) * bm)
      let Cap : ℝ := constituentDemandCap40 p b floor m
      let TP : ℝ := constituentTargetPoly41 (b := b) (m := m) pg dg r
      let R : ℝ := constituentRegionalReserve33 q P r
      let es : ℝ := Real.exp (4 * Real.sqrt (Real.log (k r)))
      let Mod : ℝ := (2 * k r + 1 : ℕ)
      let T : ℝ := Fintype.card (StageTargetLabel37 q pg dg b m r)
      let Bc : ℝ := Fintype.card (StageBucketLabel37 (B r))
      have hfloorDemand : floor ≤ stageDemand25 pg dg b floor ε m r := by
        unfold stageDemand25 natural_demand
        dsimp only
        exact (le_max_left floor (2 * (w + w) + 3)).trans (le_max_left _ _)
      have hk : 1 ≤ k r := by
        have hlower : 2 * stageDemand25 pg dg b floor ε m r ≤ 2 * k r + 1 :=
          (hbounds r).1
        dsimp only [floor, pg, dg] at hfloorDemand hlower
        omega
      have hMod : 0 < Mod := by dsimp only [Mod]; positivity
      have hModfourk : Mod ≤ 4 * (k r : ℝ) := by
        dsimp only [Mod]
        push_cast
        nlinarith [show (1 : ℝ) ≤ k r by exact_mod_cast hk]
      have hCap : 0 < Cap := by
        dsimp only [Cap, constituentDemandCap40]
        exact Real.exp_pos _
      have hE : 0 < E := Real.exp_pos _
      have hDemand : (stageDemand25 pg dg b floor ε m r : ℝ) ≤ Cap * E := by
        dsimp only [pg, dg, Cap, E, demandg]
        exact constituent_full_grid_demand_cap41 d hd hb h.val hboundary floor le_rfl
          ε hε hmpos r
      have hModNat : 2 * k r + 1 ≤ 4 * stageDemand25 pg dg b floor ε m r := by
        calc
          2 * k r + 1 ≤ 2 * max (max floor (2 * (w + w) + 3))
              (2 * stageDemand25 pg dg b floor ε m r) := (hbounds r).2.1
          _ = 4 * stageDemand25 pg dg b floor ε m r := by
            rw [show max floor (2 * (w + w) + 3) = floor by
              dsimp only [floor]; exact max_self _]
            rw [max_eq_right]
            · ring
            · omega
      have hModcap : Mod ≤ 4 * Cap * E := by
        have hreal : Mod ≤ 4 * (stageDemand25 pg dg b floor ε m r : ℝ) := by
          dsimp only [Mod]
          exact_mod_cast hModNat
        have hfour := mul_le_mul_of_nonneg_left hDemand (by norm_num : (0 : ℝ) ≤ 4)
        nlinarith
      have hEr : 0 < Er := Real.exp_pos _
      have hTP : 0 < TP := by
        dsimp only [TP, constituentTargetPoly41]
        exact Finset.prod_pos fun t _ => by positivity
      have hR : 0 < R := by
        dsimp only [R]
        exact_mod_cast constituentRegionalReserve33_pos q P r
      have hes : 0 < es := Real.exp_pos _
      have hB : (k r : ℝ) * es⁻¹ ≤ Bc := by
        have hbehrend := CW90.card_apFree_zmod_lower (k r)
        rw [← (hbounds r).2.2] at hbehrend
        dsimp only [Bc, es]
        rw [show Fintype.card (StageBucketLabel37 (B r)) = (B r).card from
          Fintype.card_coe (B r)]
        rw [← Real.exp_neg]
        simpa only [neg_mul] using hbehrend
      have hrateNow := hrate ε hε m h r
      have hrateGE : rate0 - rho ε ≤ rateg := by
        simpa only [rate0, rateg, dg] using hrateNow
      have hgridID := constituentAlphaNats_sub_demand41 pg dg r
      have hsplit : Er * E ≤ Real.exp (constituentAlphaNats41 pg dg r * bm) := by
        rw [show Er * E = Real.exp
            (((rate0 - rho ε - constituentPCompDelta40 p ε) * bm) +
              ((demandg + constituentPCompDelta40 p ε) * bm)) by
          dsimp only [Er, E]; rw [Real.exp_add]]
        apply Real.exp_le_exp.mpr
        have hbm0 : 0 ≤ bm := by dsimp only [bm]; positivity
        have hrateDemand : rateg + demandg = constituentAlphaNats41 pg dg r := by
          dsimp only [rateg, demandg]
          linarith [hgridID]
        nlinarith [mul_le_mul_of_nonneg_right hrateGE hbm0]
      have hT : Er * E / TP ≤ T := by
        calc
          Er * E / TP ≤ Real.exp (constituentAlphaNats41 pg dg r * bm) / TP :=
            div_le_div_of_nonneg_right hsplit hTP.le
          _ ≤ T := by
            dsimp only [bm, TP, T]
            exact stageTargetLabel_rate_lower41 q pg dg
              (constituent_grid_integral36 d hd hb m h.val) r
      have hpoolNow := hreserve m hmReserve
      have hreserveLog : Real.log R ≤ (ε : ℝ) * L := by
        dsimp only [R, L]
        exact c41_reserve_log_le P r hpoolNow
      have hdemandRate : demandg ≤ demandExponent p d r + rho ε := by
        dsimp only [demandg, pg, dg]
        exact c41_grid_demandExponent_le d hd h rho
          (fun i => hrate ε hε m h i) r
      have hkcap : (k r : ℝ) ≤ 4 * Cap * E := by
        have hkMod : (k r : ℝ) ≤ Mod := by
          dsimp only [Mod]
          push_cast
          linarith
        exact hkMod.trans hModcap
      have hlogk := c41_log_k_le_root d floor rho hrho hb.1 r hk demandg hdemandRate (by
        simpa only [Cap, E, demandg, bm] using hkcap)
      have hroot0 := constituentSelectionRootCoeff_nonneg41 (b := b) p d floor rho hrho ε
      have hsqrt : 4 * Real.sqrt (Real.log (k r)) ≤
          4 * Real.sqrt (constituentSelectionRootCoeff41 p d b floor rho ε) *
            Real.sqrt (L + 1) := by
        have hs := Real.sqrt_le_sqrt hlogk
        rw [Real.sqrt_mul hroot0] at hs
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)
      have hTPpoly : TP ≤ (L + 1) ^ constituentTargetDegree41 p := by
        dsimp only [TP, L, pg, dg]
        simpa only [constituentGridParent27] using
          constituentTargetPoly_le41 pg dg r
      have hlogTP : Real.log TP ≤ (constituentTargetDegree41 p : ℝ) *
          Real.log (L + 1) := by
        have hlog := Real.log_le_log hTP hTPpoly
        calc
          Real.log TP ≤ Real.log ((L + 1) ^ constituentTargetDegree41 p) := hlog
          _ = _ := by rw [Real.log_pow]
      have hlogCap : Real.log Cap = constituentDemandLogLoss40 p b floor m := by
        dsimp only [Cap, constituentDemandCap40]
        rw [Real.log_exp]
      have hloges : Real.log es = 4 * Real.sqrt (Real.log (k r)) := by
        dsimp only [es]
        rw [Real.log_exp]
      have hloss : Real.log (320 / 11 : ℝ) + Real.log Cap + Real.log TP +
          Real.log R + Real.log es ≤ ell ε m + (ε : ℝ) * L := by
        rw [hlogCap, hloges]
        dsimp only [ell, constituentSelectionLoss41]
        linarith
      have harith := selection_budget_quotient_arith41 hEr hE hTP hCap hR hes
        (by exact_mod_cast hk) hMod hModfourk hModcap hB hT hloss
      have hraw := hcount r hn
      have hselected : R *
          Real.exp (Real.log Er - (ell ε m + (ε : ℝ) * L)) ≤
          ((P.selected r).card : ℝ) := by
        calc
          R * Real.exp (Real.log Er - (ell ε m + (ε : ℝ) * L)) ≤
              R * ((11 / 20 : ℝ) * T * Bc / (Mod ^ 2 * R)) :=
            mul_le_mul_of_nonneg_left harith hR.le
          _ = (11 / 20 : ℝ) * T * Bc / Mod ^ 2 := by
            field_simp [ne_of_gt hR]
          _ ≤ ((P.selected r).card : ℝ) := by
            dsimp only [T, Bc, Mod]
            exact hraw
      have hbmL : bm ≤ L := by
        dsimp only [bm, L, cLength]
        push_cast
        have hbase : (1 : ℝ) ≤ constituentBaseTotal p := by
          exact_mod_cast (show 1 ≤ constituentBaseTotal p by
            unfold constituentBaseTotal
            let t : Fin s := ⟨0, p.terms_nonempty⟩
            exact (p.baseN_pos t).trans_le
              (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)))
        have hmul := mul_le_mul_of_nonneg_right hbase
          (show 0 ≤ (b : ℝ) * m by positivity)
        simpa only [one_mul, mul_assoc] using hmul
      have hdebit0 : 0 ≤ rho ε + constituentPCompDelta40 p ε :=
        add_nonneg (hrho.1 ε) ((constituentPCompDelta40_vanishes p).1 ε)
      have hexponent : rate0 * bm - delta ε * L - ell ε m ≤
          Real.log Er - (ell ε m + (ε : ℝ) * L) := by
        have hεR : |(ε : ℝ)| = (ε : ℝ) := abs_of_pos (by exact_mod_cast hε)
        rw [show Real.log Er = (rate0 - rho ε - constituentPCompDelta40 p ε) * bm by
          dsimp only [Er]; rw [Real.log_exp]]
        dsimp only [delta, constituentSelectionDelta41]
        rw [hεR]
        nlinarith [mul_le_mul_of_nonneg_left hbmL hdebit0]
      calc
        R * Real.exp (rate0 * bm - delta ε * L - ell ε m) ≤
            R * Real.exp (Real.log Er - (ell ε m + (ε : ℝ) * L)) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hR.le
        _ ≤ ((P.selected r).card : ℝ) := hselected
    · left
      intro x y z
      exact congrFun (congrFun (congrFun hzero' x) y) z

-- Type check against the statement.
example : S_constituent_grid_selection_count36 := constituent_grid_selection_count41

end
end OmegaBound.ADVXXZGeneral
