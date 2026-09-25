import OmegaBound.ADVXXZGeneralGlobalExactMarginalCounts
import OmegaBound.ADVXXZGeneralDemandIdentity

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The three paper demand branches, in bits per occupied regional position. -/
noncomputable def globalDemandBits27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) : ℝ :=
  let d := globalExactGridData27 g xi
  let X := g.perm r .X
  let Y := g.perm r .Y
  let Z := g.perm r .Z
  let H := entropy ((g.alpha r).probR)
  let xDemand := H + penalty ((g.alpha r).probR) -
    entropy (marginal (g.alpha r).probR X)
  let yDemand := H + globalEta d r X Y Z - entropy (globalAverage d r Y)
  let zDemand := H + globalLambda d r X Y Z - entropy (globalAverage d r Z)
  max xDemand (max yDemand zDemand)

theorem globalRegionRate_eq_entropy_sub_demand27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    globalRegionRate (globalExactGridData27 g xi) r =
      entropy ((g.alpha r).probR) - globalDemandBits27 g xi r := by
  have halg (H P B E AY L AZ : ℝ) :
      min (B - P) (min (AY - E) (AZ - L)) =
        H - max (H + P - B) (max (H + E - AY) (H + L - AZ)) := by
    rw [show H + P - B = H - (B - P) by ring,
      show H + E - AY = H - (AY - E) by ring,
      show H + L - AZ = H - (AZ - L) by ring]
    exact (alpha_sub_demand_min H (B - P) (AY - E) (AZ - L)).symm
  simpa only [globalRegionRate, globalDemandBits27] using halg
    (entropy ((g.alpha r).probR))
    (penalty ((g.alpha r).probR))
    (entropy (marginal (g.alpha r).probR (g.perm r .X)))
    (globalEta (globalExactGridData27 g xi) r
      (g.perm r .X) (g.perm r .Y) (g.perm r .Z))
    (entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y)))
    (globalLambda (globalExactGridData27 g xi) r
      (g.perm r .X) (g.perm r .Y) (g.perm r .Z))
    (entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)))

private theorem gdb_negMulLog_sum_le27 {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (p : alpha → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∀ a, p a ≤ 1) (S : Finset alpha) :
    Real.negMulLog (∑ a ∈ S, p a) ≤ ∑ a ∈ S, Real.negMulLog (p a) := by
  let q := ∑ a ∈ S, p a
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun a _ => hp0 a
  by_cases hq : q = 0
  · change Real.negMulLog q ≤ _
    rw [hq, Real.negMulLog_zero]
    exact Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hp0 a) (hp1 a)
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    rw [Entropy.negMulLog_eq]
    have hrewrite : -(q * Real.log q) = ∑ a ∈ S, -(p a * Real.log q) := by
      dsimp only [q]
      rw [Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hrewrite]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpapos : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm hpa)
      have hpaq : p a ≤ q := by
        dsimp only [q]
        exact Finset.single_le_sum (fun x _ => hp0 x) ha
      have hlog : Real.log (p a) ≤ Real.log q :=
        Real.strictMonoOn_log.monotoneOn hpapos hqpos hpaq
      rw [Entropy.negMulLog_eq]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hlog (hp0 a))

private theorem gdb_entropy_map_le27 {alpha gamma : Type*}
    [Fintype alpha] [Fintype gamma] [DecidableEq alpha] [DecidableEq gamma]
    (p : alpha → ℝ) (hp : IsProbability p) (f : alpha → gamma) :
    entropy (fun c => ∑ a ∈ (Finset.univ.filter fun a => f a = c), p a) ≤ entropy p := by
  let q := fun c : gamma => ∑ a ∈ (Finset.univ.filter fun a => f a = c), p a
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    calc
      p a ≤ ∑ x, p x := Finset.single_le_sum (fun x _ => hp.1 x) (Finset.mem_univ a)
      _ = 1 := hp.2
  have hfiber :
      (∑ c ∈ (Finset.univ : Finset gamma),
          ∑ a ∈ (Finset.univ.filter fun a => f a = c), Real.negMulLog (p a)) =
        ∑ a ∈ (Finset.univ : Finset alpha), Real.negMulLog (p a) := by
    exact Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset alpha)) (t := (Finset.univ : Finset gamma))
      (g := f) (fun a _ => Finset.mem_univ (f a)) (fun a => Real.negMulLog (p a))
  have hH : Entropy.H (Finset.univ : Finset gamma) q ≤
      Entropy.H (Finset.univ : Finset alpha) p := by
    unfold Entropy.H
    calc
      (∑ c ∈ (Finset.univ : Finset gamma), Real.negMulLog (q c)) ≤
          ∑ c ∈ (Finset.univ : Finset gamma),
            ∑ a ∈ (Finset.univ.filter fun a => f a = c), Real.negMulLog (p a) := by
        apply Finset.sum_le_sum
        intro c _
        exact gdb_negMulLog_sum_le27 p hp.1 hp1 _
      _ = ∑ a ∈ (Finset.univ : Finset alpha), Real.negMulLog (p a) := hfiber
  unfold entropy Entropy.H₂
  exact div_le_div_of_nonneg_right hH (Real.log_pos one_lt_two).le

private theorem gdb_marginal_entropy_le27 {w : ℕ} (g : GlobalSpec w)
    (r : Fin 6) (S : Side) :
    entropy (marginal (g.alpha r).probR S) ≤ entropy ((g.alpha r).probR) := by
  let f := fun u : Shape w => Parent25.coordFin S u
  have hp : IsProbability (g.alpha r).probR :=
    ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩
  have hmap := gdb_entropy_map_le27 (g.alpha r).probR hp f
  have hq : (fun c => ∑ u ∈ (Finset.univ.filter fun u => f u = c),
      (g.alpha r).probR u) = marginal (g.alpha r).probR S := by
    funext c
    unfold marginal
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : f u = c
    · rw [if_pos h, if_pos]
      cases S <;> exact congrArg Fin.val h
    · rw [if_neg h, if_neg]
      intro hc
      apply h
      apply Fin.ext
      cases S <;> exact hc
  rwa [hq] at hmap

private theorem gdb_penalty_nonneg27 {w : ℕ} (g : GlobalSpec w) (r : Fin 6) :
    0 ≤ penalty ((g.alpha r).probR) := by
  let p := (g.alpha r).probR
  let S : Set ℝ := {h : ℝ | ∃ p' : Shape w → ℝ,
    IsProbability p' ∧ SameMarginals p p' ∧ h = entropy p'}
  have hp : IsProbability p := ⟨(g.alpha r).probR_nonneg, (g.alpha r).sum_probR⟩
  have hmem : entropy p ∈ S := ⟨p, hp, fun _ _ => rfl, rfl⟩
  letI : Nonempty (Shape w) := RatDist.nonempty (g.alpha r)
  have hbdd : BddAbove S := by
    refine ⟨Real.log (Fintype.card (Shape w) : ℝ) / Real.log 2, ?_⟩
    intro h hh
    rcases hh with ⟨p', hp', -, rfl⟩
    have hH := Entropy.H_le_log_card (s := (Finset.univ : Finset (Shape w)))
      Finset.univ_nonempty (fun u _ => hp'.1 u) (by simpa using hp'.2)
    have hHn : entropyNats p' ≤ Real.log (Fintype.card (Shape w) : ℝ) := by
      calc
        entropyNats p' = Entropy.H Finset.univ p' :=
          (Entropy.H_eq_neg_sum Finset.univ p').symm
        _ ≤ Real.log ((Finset.univ : Finset (Shape w)).card : ℝ) := hH
        _ = _ := by simp
    rw [entropyNats_eq_log_two_mul_entropy, mul_comm] at hHn
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).2 hHn
  have hsup : entropy p ≤ sSup S := le_csSup hbdd hmem
  unfold penalty
  change 0 ≤ sSup S - entropy p
  linarith

theorem globalDemandBits_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) : 0 ≤ globalDemandBits27 g xi r := by
  unfold globalDemandBits27
  dsimp only
  have hm := gdb_marginal_entropy_le27 g r (g.perm r .X)
  have hp := gdb_penalty_nonneg27 g r
  have hx : 0 ≤ entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR) -
      entropy (marginal (g.alpha r).probR (g.perm r .X)) := by
    linarith
  exact hx.trans (le_max_left _ _)

private noncomputable def gdb_representedLaw27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    GlobalRepresentedLaw g n xi r which := by
  let j : GlobalTargetLabel27 g xi r := Classical.choice (globalTargetLabel_nonempty27 g xi r)
  let a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which) :=
    Classical.choice (globalExactPart_nonempty27 1 g xi r j.val j.property _)
  exact globalExactRepresentedLaw27 g xi r which j a

/-- P/Q, the exact P and Q exponent identities, and the unique represented law give the
    literal Eta/Lambda compatibility exponent. -/
theorem globalPcompMax_paper_entropy_bound27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (which : Fin 2) :
    globalPcompMax g (b * m) xi r which ≤
      Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
        (if which = 0 then
          globalEta (globalExactGridData27 g xi) r
              (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
            entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y)) +
            entropy (marginal (g.alpha r).probR (g.perm r .Y))
        else
          globalLambda (globalExactGridData27 g xi) r
              (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
            entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)) +
            entropy (marginal (g.alpha r).probR (g.perm r .Z)))) *
        (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          Fintype.card (Chunk w) := by
  have h := globalPcompMax_entropy_bound27 g hg hb m xi hxi r which
    (gdb_representedLaw27 g xi r which)
  rw [globalQExponent_paper27 g hg hb xi r which,
    globalPExponent_paper27 g hg hb xi r hn which] at h
  dsimp only [GlobalSpec.toPaper] at h
  by_cases hwhich : which = 0
  · subst which
    simp only [GlobalBridge25.side, if_pos] at h ⊢
    convert h using 1 <;> ring
  · have hwhich1 : which = 1 := by omega
    subst which
    have h10 : (1 : Fin 2) ≠ 0 := by omega
    simp only [GlobalBridge25.side, h10, if_false] at h ⊢
    convert h using 1 <;> ring

private theorem gdb_globalPcomp_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    0 ≤ globalPcomp g n xi r which beta := by
  classical
  unfold globalPcomp
  dsimp only
  split_ifs <;> positivity

private theorem gdb_globalPcompMax_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    0 ≤ globalPcompMax g n xi r which := by
  classical
  unfold globalPcompMax
  dsimp only
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g n xi r which)).image
    (globalPcomp g n xi r which)
  by_cases hv : values.Nonempty
  · rw [dif_pos hv]
    rcases Finset.mem_image.mp (Finset.max'_mem values hv) with ⟨beta, -, hbeta⟩
    rw [← hbeta]
    exact gdb_globalPcomp_nonneg27 g xi r which beta
  · rw [dif_neg hv]

theorem globalDemand_x_ratio_bound27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (r : Fin 6)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0) :
    (Fintype.card (globalPopulation g (b * m) xi r).Label : ℝ) /
        (((Finset.univ : Finset (globalPopulation g (b * m) xi r).Label).image
          (fun j => (globalPopulation g (b * m) xi r).coarse j (g.perm r .X))).card : ℝ) ≤
      (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          (Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1))) *
        Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          (entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR) -
            entropy (marginal (g.alpha r).probR (g.perm r .X)))) := by
  let N : ℝ := (globalPopulation g (b * m) xi r).n
  let PS : ℝ := (N + 1) ^ Fintype.card (Shape w)
  let PC : ℝ := (N + 1) ^ Fintype.card (Fin (2 * w + 1))
  let A := entropy ((g.alpha r).probR) + penalty ((g.alpha r).probR)
  let B := entropy (marginal (g.alpha r).probR (g.perm r .X))
  let NX : ℝ := ((Finset.univ : Finset (globalPopulation g (b * m) xi r).Label).image
    (fun j => (globalPopulation g (b * m) xi r).coarse j (g.perm r .X))).card
  have hlabel := globalLabel_paper_entropy_upper27 g hg hb xi r hn
  have hcoarse := globalCoarseImage_paper_entropy_lower27 g hg hb xi r hn (g.perm r .X)
  have hPC : 0 < PC := by unfold PC; positivity
  have hNX : 0 < NX := lt_of_lt_of_le (div_pos (Real.exp_pos _) hPC) hcoarse
  rw [show ((N + 1) ^ (Fintype.card (Shape w) +
      Fintype.card (Fin (2 * w + 1)))) = PS * PC by
        unfold PS PC
        rw [pow_add]]
  apply (div_le_iff₀ hNX).2
  calc
    (Fintype.card (globalPopulation g (b * m) xi r).Label : ℝ) ≤
        PS * Real.exp (N * Real.log 2 * A) := hlabel
    _ = (Real.exp (N * Real.log 2 * B) / PC) *
        (PS * PC * Real.exp (N * Real.log 2 * (A - B))) := by
      rw [show N * Real.log 2 * (A - B) =
        N * Real.log 2 * A - N * Real.log 2 * B by ring, Real.exp_sub]
      field_simp
    _ ≤ NX * (PS * PC * Real.exp (N * Real.log 2 * (A - B))) :=
      mul_le_mul_of_nonneg_right hcoarse (by positivity)
    _ = (PS * PC * Real.exp (N * Real.log 2 * (A - B))) * NX := by ring

theorem globalDemand_target_pcomp_ratio_bound27 {w b m : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (which : Fin 2) :
    ((globalPopulation g (b * m) xi r).target.card : ℝ) *
        globalPcompMax g (b * m) xi r which /
        (((Finset.univ : Finset (globalPopulation g (b * m) xi r).Label).image
          (fun j => (globalPopulation g (b * m) xi r).coarse j
            (GlobalBridge25.side g r which))).card : ℝ) ≤
      (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          (Fintype.card (Chunk w) + Fintype.card (Fin (2 * w + 1))) *
        Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) * Real.log 2 *
          (if which = 0 then
            entropy ((g.alpha r).probR) +
                globalEta (globalExactGridData27 g xi) r
                  (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
              entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y))
          else
            entropy ((g.alpha r).probR) +
                globalLambda (globalExactGridData27 g xi) r
                  (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
              entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)))) := by
  let N : ℝ := (globalPopulation g (b * m) xi r).n
  let PC : ℝ := (N + 1) ^ Fintype.card (Fin (2 * w + 1))
  let PQ : ℝ := (N + 1) ^ Fintype.card (Chunk w)
  let H := entropy ((g.alpha r).probR)
  let S := GlobalBridge25.side g r which
  let B := entropy (marginal (g.alpha r).probR S)
  let C := if which = 0 then
      globalEta (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
        entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y)) + B
    else
      globalLambda (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
        entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z)) + B
  let D := if which = 0 then
      H + globalEta (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
        entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Y))
    else
      H + globalLambda (globalExactGridData27 g xi) r
          (g.perm r .X) (g.perm r .Y) (g.perm r .Z) -
        entropy (globalAverage (globalExactGridData27 g xi) r (g.perm r .Z))
  let NW : ℝ := ((Finset.univ : Finset (globalPopulation g (b * m) xi r).Label).image
    (fun j => (globalPopulation g (b * m) xi r).coarse j S)).card
  have htarget0 := (globalTargetLabel_paper_entropy_bounds27 g hg hb xi r hn).2
  have htarget : ((globalPopulation g (b * m) xi r).target.card : ℝ) ≤
      Real.exp (N * Real.log 2 * H) := by
    simp only [GlobalTargetLabel27, Fintype.card_coe, GlobalSpec.toPaper] at htarget0
    calc
      ((globalPopulation g (b * m) xi r).target.card : ℝ) ≤
          Real.exp (((globalPopulation g (b * m) xi r).n : ℝ) *
            (Real.log 2 * entropy ((g.alpha r).probR))) := htarget0
      _ = Real.exp (N * Real.log 2 * H) := by
        congr 1
        unfold N H
        ring
  have hpcomp := globalPcompMax_paper_entropy_bound27 g hg hb xi hxi r hn which
  have hpcomp' : globalPcompMax g (b * m) xi r which ≤
      Real.exp (N * Real.log 2 * C) * PQ := by
    fin_cases which <;>
      simpa only [N, C, PQ, S, B, GlobalBridge25.side, if_pos, if_false] using hpcomp
  have hcoarse := globalCoarseImage_paper_entropy_lower27 g hg hb xi r hn S
  have hPC : 0 < PC := by unfold PC; positivity
  have hNW : 0 < NW := lt_of_lt_of_le (div_pos (Real.exp_pos _) hPC) hcoarse
  have hpnonneg := gdb_globalPcompMax_nonneg27 g xi r which
  rw [show (N + 1) ^ (Fintype.card (Chunk w) +
      Fintype.card (Fin (2 * w + 1))) = PQ * PC by
        unfold PQ PC
        rw [pow_add]]
  apply (div_le_iff₀ hNW).2
  calc
    ((globalPopulation g (b * m) xi r).target.card : ℝ) *
        globalPcompMax g (b * m) xi r which ≤
      Real.exp (N * Real.log 2 * H) * (Real.exp (N * Real.log 2 * C) * PQ) :=
        mul_le_mul htarget hpcomp' hpnonneg (Real.exp_pos _).le
    _ = (Real.exp (N * Real.log 2 * B) / PC) *
        (PQ * PC * Real.exp (N * Real.log 2 * D)) := by
      have hCD : H + C - B = D := by
        by_cases hwhich : which = 0
        · subst which
          simp only [H, C, D, B, S, GlobalBridge25.side, if_pos]
          ring
        · have hwhich1 : which = 1 := by omega
          subst which
          have h10 : (1 : Fin 2) ≠ 0 := by omega
          simp only [H, C, D, B, S, GlobalBridge25.side, h10, if_false]
          ring
      have hexp : Real.exp (N * Real.log 2 * H) * Real.exp (N * Real.log 2 * C) =
          Real.exp (N * Real.log 2 * B) * Real.exp (N * Real.log 2 * D) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        calc
          N * Real.log 2 * H + N * Real.log 2 * C =
              N * Real.log 2 * (H + C - B) + N * Real.log 2 * B := by ring
          _ = N * Real.log 2 * D + N * Real.log 2 * B := by rw [hCD]
          _ = N * Real.log 2 * B + N * Real.log 2 * D := by ring
      calc
        Real.exp (N * Real.log 2 * H) * (Real.exp (N * Real.log 2 * C) * PQ) =
            (Real.exp (N * Real.log 2 * H) * Real.exp (N * Real.log 2 * C)) * PQ := by
              ring
        _ = (Real.exp (N * Real.log 2 * B) * Real.exp (N * Real.log 2 * D)) * PQ := by
              rw [hexp]
        _ = (Real.exp (N * Real.log 2 * B) / PC) *
            (PQ * PC * Real.exp (N * Real.log 2 * D)) := by
              field_simp
    _ ≤ NW * (PQ * PC * Real.exp (N * Real.log 2 * D)) :=
      mul_le_mul_of_nonneg_right hcoarse (by positivity)
    _ = (PQ * PC * Real.exp (N * Real.log 2 * D)) * NW := by ring

end
end OmegaBound.ADVXXZGeneral
end
