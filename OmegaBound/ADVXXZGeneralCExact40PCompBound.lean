import OmegaBound.ADVXXZGeneralCExact40FiniteBounds
import OmegaBound.ADVXXZGeneralCExact40Quotient
import OmegaBound.ADVXXZGeneralPCompEntropy

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral

namespace Parent25

/-- A continuity modulus chosen from the fixed parent before any empirical grid. -/
def RateContinuityBridge40 : Prop :=
  ∀ {w s : ℕ} (p : ConstituentInput w s),
    ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
      ∀ {b m : ℕ} (d : ConstituentSpec p),
        ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
        ∀ ε, 0 < ε → 0 < m → ∀ r W (β : RepresentedLaw p d b ε m r W),
          qRate p d r W - pRate p d b ε m r W β ≤
            demandCompatRate p d r W + delta ε

end Parent25

def constituentPCompPower40 {w s : ℕ} (p : ConstituentInput w s) (b : ℕ) : ℕ :=
  (∑ t : Fin s, b * p.baseN t) * Fintype.card (Chunk (w+w))

noncomputable def constituentPCompLoss40 {w s : ℕ} (p : ConstituentInput w s)
    (b m : ℕ) : ℝ :=
  (constituentPCompPower40 p b : ℝ) * Real.log ((m : ℝ) + 1)

private def apqLegacyAlphaCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def apqLegacyParentCount {w s : ℕ} (b m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, apqLegacyAlphaCount b m p d r t u

private def apqLegacySide {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) : Side :=
  if W = 0 then d.perm r .Y else d.perm r .Z

private theorem apq_probR_eq_cast_prob {alpha : Type*} [Fintype alpha]
    (P : RatDist alpha) (a : alpha) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem apq_representedLaw_typical {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    ∀ t, 0 < Parent25.parentCount p d b m r t → ∀ σ,
      |(β.val t σ : ℝ) - (d.betaRegion (Parent25.side d r W) t r).probR σ| ≤ ε := by
  classical
  have h := β.property
  simp only [RepresentedLaw] at h
  have ht := (Finset.mem_filter.mp h).2
  have ht' : ∀ t, 0 < apqLegacyParentCount b m p d r t → ∀ σ,
      |β.val t σ - (d.betaRegion (apqLegacySide d r W) t r).prob σ| ≤ ε :=
    cast (by rfl) ht
  intro t hn σ
  have hcount : apqLegacyParentCount b m p d r t =
      Parent25.parentCount p d b m r t := by rfl
  have hside : apqLegacySide d r W = Parent25.side d r W := by
    by_cases hW : W = 0
    · simp only [apqLegacySide, Parent25.side, hW, if_pos]
    · simp [apqLegacySide, Parent25.side, hW]
  rw [← hside]
  have hrat := ht' t (hcount.symm ▸ hn) σ
  rw [apq_probR_eq_cast_prob]
  exact_mod_cast hrat

private theorem apq_beta_nonneg {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (t : Fin s) (hn : Parent25.parentCount p d b m r t ≠ 0) (σ : Chunk (w+w)) :
    0 ≤ (β.val t σ : ℝ) := by
  rw [← congrFun (parent25_betaCount_normalized40 p d ε m r W β t hn) σ]
  positivity

private theorem apq_beta_sum_one {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (t : Fin s) (hn : Parent25.parentCount p d b m r t ≠ 0) :
    ∑ σ, (β.val t σ : ℝ) = 1 := by
  have hnorm := parent25_betaCount_normalized40 p d ε m r W β t hn
  calc
    ∑ σ, (β.val t σ : ℝ) =
        ∑ σ, (Parent25.betaCount p d b ε m r W β t σ : ℝ) /
          Parent25.parentCount p d b m r t := by
            apply Finset.sum_congr rfl
            intro σ _
            exact (congrFun hnorm σ).symm
    _ = (∑ σ, (Parent25.betaCount p d b ε m r W β t σ : ℝ)) /
        Parent25.parentCount p d b m r t := by rw [Finset.sum_div]
    _ = (Parent25.parentCount p d b m r t : ℝ) /
        Parent25.parentCount p d b m r t := by
          rw [← Nat.cast_sum, parent25_betaCount_sum40]
    _ = 1 := div_self (by exact_mod_cast hn)

private theorem apq_prob_le_one {alpha : Type*} [Fintype alpha]
    (P : RatDist alpha) (a : alpha) : P.probR a ≤ 1 := by
  calc
    P.probR a ≤ ∑ x, P.probR x :=
      Finset.single_le_sum (fun x _ => P.probR_nonneg x) (Finset.mem_univ a)
    _ = 1 := P.sum_probR

private theorem apq_rate_sub_eq {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β =
      demandCompatRate p d r W +
        ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
          (entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
            entropyNats (fun σ => (β.val t σ : ℝ))) := by
  by_cases hW : W = 0
  · subst W
    unfold Parent25.qRate Parent25.pRate demandCompatRate Parent25.side splitEntropy
    simp only [if_pos]
    simp_rw [Finset.mul_sum, entropyNats_eq_log_two_mul_entropy40]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · unfold Parent25.qRate Parent25.pRate demandCompatRate Parent25.side splitEntropy
    simp only [hW, if_false]
    simp_rw [Finset.mul_sum, entropyNats_eq_log_two_mul_entropy40]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring

/-- The canonical entropy modulus used by every empirical parent of width `w`. -/
noncomputable def constituentEntropyDelta40 (w : ℕ) : ℚ → ℝ :=
  Classical.choose (entropy_uniform_continuity (α := Chunk (w + w)))

theorem constituentEntropyDelta40_spec (w : ℕ) :
    VanishesWithTolerance (constituentEntropyDelta40 w) ∧
      ∀ (ε : ℚ), 0 < ε → ∀ (p q : Chunk (w + w) → ℝ),
        (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ q a) →
        (∑ a, p a = 1) → (∑ a, q a = 1) →
        (∀ a, |p a - q a| ≤ ε) →
          |entropyNats p - entropyNats q| ≤ constituentEntropyDelta40 w ε := by
  exact Classical.choose_spec (entropy_uniform_continuity (α := Chunk (w + w)))

/-- A compatibility modulus depending only on the coarse multiplicities of the parent. -/
noncomputable def constituentPCompDelta40 {w s : ℕ} (p : ConstituentInput w s) : ℚ → ℝ :=
  fun ε => (∑ t : Fin s, (p.baseN t : ℝ)) * constituentEntropyDelta40 w ε

theorem constituentPCompDelta40_vanishes {w s : ℕ} (p : ConstituentInput w s) :
    VanishesWithTolerance (constituentPCompDelta40 p) := by
  apply vanishesWithTolerance_const_mul
    (∑ t : Fin s, (p.baseN t : ℝ))
    (Finset.sum_nonneg fun t _ => Nat.cast_nonneg (p.baseN t))
  exact (constituentEntropyDelta40_spec w).1

/-- The rate difference is controlled by the canonical pre-grid modulus. -/
theorem parent25_rate_continuity40 {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : ConstituentIntegral36 d b m) (ε : ℚ) (hε : 0 < ε) (hm : 0 < m)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β ≤
      demandCompatRate p d r W + constituentPCompDelta40 p ε := by
  let delta0 := constituentEntropyDelta40 w
  have hdelta0 := (constituentEntropyDelta40_spec w).1
  have hcontinuity := (constituentEntropyDelta40_spec w).2
  let C : ℝ := ∑ t : Fin s, (p.baseN t : ℝ)
  let delta : ℚ → ℝ := fun ε => C * delta0 ε
  have hC : 0 ≤ C := Finset.sum_nonneg fun t _ => Nat.cast_nonneg (p.baseN t)
  have hcell : ∀ t : Fin s,
      (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
          (entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
            entropyNats (fun σ => (β.val t σ : ℝ))) ≤
        (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) * delta0 ε := by
    intro t
    by_cases hn : Parent25.parentCount p d b m r t = 0
    · have hweight : (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) = 0 := by
        have hbm : 0 < b * m := Nat.mul_pos hb.bpos hm
        have hbase : 0 < b * m * p.baseN t := Nat.mul_pos hbm (p.baseN_pos t)
        have hcast : (Parent25.parentCount p d b m r t : ℝ) =
            ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := by
          exact_mod_cast parent25_parentCount_cast40 p d m hb r t
        rw [hn] at hcast
        have hfactor : ((b * m * p.baseN t : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast hbase.ne'
        have hzero : ((b * m * p.baseN t : ℕ) : ℝ) *
            ((d.A t).prob r : ℝ) = 0 := by simpa using hcast.symm
        have hp : ((d.A t).prob r : ℝ) = 0 :=
          (mul_eq_zero.mp hzero).resolve_left hfactor
        rw [hp]
        ring
      rw [hweight]
      simp
    · have hcont := hcontinuity ε hε
        (fun σ => (β.val t σ : ℝ))
        (d.betaRegion (Parent25.side d r W) t r).probR
        (apq_beta_nonneg p d ε m r W β t hn)
        (d.betaRegion (Parent25.side d r W) t r).probR_nonneg
        (apq_beta_sum_one p d ε m r W β t hn)
        (d.betaRegion (Parent25.side d r W) t r).sum_probR
        (apq_representedLaw_typical p d ε m r W β t (Nat.pos_of_ne_zero hn))
      have hdifference : entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
          entropyNats (fun σ => (β.val t σ : ℝ)) ≤ delta0 ε := by
        calc
          _ ≤ |entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
              entropyNats (fun σ => (β.val t σ : ℝ))| := le_abs_self _
          _ = |entropyNats (fun σ => (β.val t σ : ℝ)) -
              entropyNats (d.betaRegion (Parent25.side d r W) t r).probR| := abs_sub_comm _ _
          _ ≤ delta0 ε := hcont
      exact mul_le_mul_of_nonneg_left hdifference
        (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (d.A t).prob_nonneg r))
  rw [apq_rate_sub_eq]
  have herr : (∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
        (entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
          entropyNats (fun σ => (β.val t σ : ℝ)))) ≤ delta ε := by
    calc
    ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) *
        (entropyNats (d.betaRegion (Parent25.side d r W) t r).probR -
          entropyNats (fun σ => (β.val t σ : ℝ))) ≤
      ∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) * delta0 ε :=
        Finset.sum_le_sum fun t _ => hcell t
    _ = (∑ t, (p.baseN t : ℝ) * ((d.A t).prob r : ℝ)) * delta0 ε := by
      rw [Finset.sum_mul]
    _ ≤ C * delta0 ε := by
      apply mul_le_mul_of_nonneg_right _ (hdelta0.1 ε)
      apply Finset.sum_le_sum
      intro t _
      calc
        (p.baseN t : ℝ) * ((d.A t).prob r : ℝ) ≤
            (p.baseN t : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (by
            rw [← apq_probR_eq_cast_prob]
            exact apq_prob_le_one (d.A t) r) (Nat.cast_nonneg _)
        _ = (p.baseN t : ℝ) := mul_one _
    _ = delta ε := rfl
  simpa only [delta, C, delta0, constituentPCompDelta40] using
    (add_le_add_right herr (demandCompatRate p d r W))

/-- The existential bridge retained for the Parent25 interface. -/
theorem parent25_rate_continuity_bridge40 : Parent25.RateContinuityBridge40 := by
  intro w s p
  refine ⟨constituentPCompDelta40 p, constituentPCompDelta40_vanishes p, ?_⟩
  intro b m d hd hb ε hε hm r W β
  exact parent25_rate_continuity40 p d hd hb ε hε hm r W β

private theorem apq_parentCount_le {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    Parent25.parentCount p d b m r t ≤ b * p.baseN t * m := by
  have hcast : (Parent25.parentCount p d b m r t : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := by
    exact_mod_cast parent25_parentCount_cast40 p d m hb r t
  have hprob : ((d.A t).prob r : ℝ) ≤ 1 := by
    rw [← apq_probR_eq_cast_prob]
    exact apq_prob_le_one (d.A t) r
  exact_mod_cast (calc
    (Parent25.parentCount p d b m r t : ℝ) =
        ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := hcast
    _ ≤ ((b * m * p.baseN t : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hprob (Nat.cast_nonneg _)
    _ = (b * p.baseN t * m : ℕ) := by push_cast; ring)

private theorem apq_poly_le_pow {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    let Cn := (∑ t : Fin s, b * p.baseN t) * Fintype.card (Chunk (w+w))
    (∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
        Fintype.card (Chunk (w+w))) ≤ ((m : ℝ) + 1) ^ Cn := by
  classical
  dsimp only
  let K := Fintype.card (Chunk (w+w))
  have hfactor : ∀ t : Fin s,
      ((Parent25.parentCount p d b m r t : ℝ) + 1) ^ K ≤
        ((m : ℝ) + 1) ^ ((b * p.baseN t) * K) := by
    intro t
    have hlinear : (Parent25.parentCount p d b m r t : ℝ) + 1 ≤
        ((m : ℝ) + 1) ^ (b * p.baseN t) := by
      calc
        (Parent25.parentCount p d b m r t : ℝ) + 1 ≤
            (b * p.baseN t * m : ℕ) + 1 := by
          exact_mod_cast Nat.add_le_add_right (apq_parentCount_le p d m hb r t) 1
        _ = 1 + (b * p.baseN t : ℕ) * (m : ℝ) := by push_cast; ring
        _ ≤ (1 + (m : ℝ)) ^ (b * p.baseN t) :=
          one_add_mul_le_pow (by
            have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            linarith) _
        _ = ((m : ℝ) + 1) ^ (b * p.baseN t) := by ring_nf
    calc
      ((Parent25.parentCount p d b m r t : ℝ) + 1) ^ K ≤
          (((m : ℝ) + 1) ^ (b * p.baseN t)) ^ K := by
        exact pow_le_pow_left₀ (by positivity) hlinear K
      _ = ((m : ℝ) + 1) ^ ((b * p.baseN t) * K) := by
        rw [← pow_mul]
  calc
    (∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^ K) ≤
        ∏ t, ((m : ℝ) + 1) ^ ((b * p.baseN t) * K) := by
      apply Finset.prod_le_prod
      · intro t _
        positivity
      · intro t _
        exact hfactor t
    _ = ((m : ℝ) + 1) ^ (∑ t : Fin s, (b * p.baseN t) * K) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = ((m : ℝ) + 1) ^ ((∑ t : Fin s, b * p.baseN t) * K) := by
      rw [Finset.sum_mul]

private theorem apq_poly_le_exp_loss {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    let Cn := (∑ t : Fin s, b * p.baseN t) * Fintype.card (Chunk (w+w))
    (∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
        Fintype.card (Chunk (w+w))) ≤
      Real.exp ((Cn : ℝ) * Real.log ((m : ℝ) + 1)) := by
  dsimp only
  rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (m : ℝ) + 1)]
  exact apq_poly_le_pow p d m hb r

private theorem apq_joint_ratio_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) :
    let Cn := (∑ t : Fin s, b * p.baseN t) * Fintype.card (Chunk (w+w))
    Parent25.jointQ p d b ε m r W β / Parent25.jointP p d b ε m r W β ≤
      Real.exp ((Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β) *
        (b*m : ℕ) + (Cn : ℝ) * Real.log ((m : ℝ) + 1)) := by
  classical
  dsimp only
  let N := (Nat.card (AlphaLabel p d b m r) : ℝ)
  let ambient := (Nat.card (AlphaLabel p d b m r ×
    (Parent25.Pop p d b m r).Part (Parent25.side d r W)) : ℝ)
  let poly := ∏ t, ((Parent25.parentCount p d b m r t : ℝ) + 1) ^
    Fintype.card (Chunk (w+w))
  let P := Parent25.jointP p d b ε m r W β
  let Q := Parent25.jointQ p d b ε m r W β
  let pr := Parent25.pRate p d b ε m r W β * (b*m : ℕ)
  let qr := Parent25.qRate p d r W * (b*m : ℕ)
  let loss := (((∑ t : Fin s, b * p.baseN t) * Fintype.card (Chunk (w+w)) : ℕ) : ℝ) *
    Real.log ((m : ℝ) + 1)
  have hfin := parent25_finite_bounds_bridge40 p d hd hb ε r W β
  have hPlower : N * Real.exp pr / poly ≤ ambient * P := hfin.2.2.1
  have hQupper : ambient * Q ≤ N * Real.exp qr := hfin.2.2.2.2
  have hPpos : 0 < P := (compatibility_quotient_parent40 p d hd m hb ε r W β).1
  rcases parent25_representedLaw_witness p d ε m r W β with ⟨J, a, -, -⟩
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast Nat.card_pos_iff.mpr ⟨⟨J⟩, inferInstance⟩
  have hambientpos : 0 < ambient := by
    dsimp only [ambient]
    exact_mod_cast Nat.card_pos_iff.mpr ⟨⟨(J, a)⟩, inferInstance⟩
  have hpolypos : 0 < poly := Finset.prod_pos fun t _ => pow_pos (by positivity) _
  have hpoly : poly ≤ Real.exp loss := apq_poly_le_exp_loss p d m hb r
  let factor := Real.exp qr * poly / Real.exp pr
  have hfactor : 0 ≤ factor := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hPlower hfactor
  have hNS : N * Real.exp qr ≤ factor * (ambient * P) := by
    calc
      N * Real.exp qr = factor * (N * Real.exp pr / poly) := by
        dsimp only [factor]
        field_simp [ne_of_gt (Real.exp_pos pr), ne_of_gt hpolypos]
      _ ≤ factor * (ambient * P) := hscaled
  have hAQ : ambient * Q ≤ factor * (ambient * P) := hQupper.trans hNS
  have hQP : Q / P ≤ factor := by
    rw [div_le_iff₀ hPpos]
    exact le_of_mul_le_mul_left (show ambient * Q ≤
      ambient * (factor * P) by simpa only [mul_assoc, mul_left_comm] using hAQ)
      hambientpos
  calc
    Q / P ≤ factor := hQP
    _ ≤ Real.exp qr * Real.exp loss / Real.exp pr := by
      dsimp only [factor]
      gcongr
    _ = Real.exp ((Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β) *
        (b*m : ℕ) + loss) := by
      rw [← Real.exp_add, ← Real.exp_sub]
      congr 1
      dsimp only [pr, qr]
      push_cast
      ring
    _ = _ := rfl

private theorem apq_parent_pcompMax_le {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (W : Fin 2) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ β : RepresentedLaw p d b ε m r W,
      Parent25.pcomp p d b ε m r W β ≤ B) :
    Parent25.pcompMax p d b ε m r W ≤ B := by
  classical
  unfold Parent25.pcompMax
  dsimp only
  let values := (Finset.univ : Finset (RepresentedLaw p d b ε m r W)).image
    (Parent25.pcomp p d b ε m r W)
  by_cases hvalues : values.Nonempty
  · rw [dif_pos hvalues]
    rcases Finset.mem_image.mp (Finset.max'_mem values hvalues) with ⟨β, -, hβ⟩
    rw [← hβ]
    exact h β
  · rw [dif_neg hvalues]
    exact hB

theorem constituent_pcomp_bound_parent40 {w s : ℕ} (p : ConstituentInput w s) :
  ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
    ∀ {b m : ℕ} (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
      (hb : ConstituentIntegral36 d b m) (ε : ℚ), 0 < ε → 0 < m →
      ∀ (r : Fin 6) (W : Fin 2),
        Parent25.pcompMax p d b ε m r W ≤
          Real.exp ((demandCompatRate p d r W + delta ε) * (b*m : ℝ) +
            constituentPCompLoss40 p b m) := by
  obtain ⟨delta, hdelta, hrate⟩ := parent25_rate_continuity_bridge40 p
  refine ⟨delta, hdelta, ?_⟩
  intro b m d hd hb ε hε hmpos r W
  let B := Real.exp ((demandCompatRate p d r W + delta ε) * (b*m : ℝ) +
    constituentPCompLoss40 p b m)
  apply apq_parent_pcompMax_le p d b ε m r W B (Real.exp_pos _).le
  intro β
  rw [(compatibility_quotient_parent40 p d hd m hb ε r W β).2]
  calc
    Parent25.jointQ p d b ε m r W β / Parent25.jointP p d b ε m r W β ≤
        Real.exp ((Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β) *
          (b*m : ℕ) + constituentPCompLoss40 p b m) := by
      simpa only [constituentPCompLoss40, constituentPCompPower40] using
        apq_joint_ratio_bound p d hd m hb ε r W β
    _ ≤ B := by
      dsimp only [B]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right (hrate d hd hb ε hε hmpos r W β)
        (show (0 : ℝ) ≤ ((b*m : ℕ) : ℝ) from Nat.cast_nonneg _)
      simpa only [Nat.cast_mul, add_comm] using
        add_le_add_right hmul (constituentPCompLoss40 p b m)

/-- The same compatibility bound with its pre-grid modulus exposed in the conclusion. -/
theorem constituent_pcomp_bound_parent40_at_delta {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (hε : 0 < ε) (hmpos : 0 < m) (r : Fin 6) (W : Fin 2) :
    Parent25.pcompMax p d b ε m r W ≤
      Real.exp ((demandCompatRate p d r W + constituentPCompDelta40 p ε) *
        (b * m : ℝ) + constituentPCompLoss40 p b m) := by
  let B := Real.exp ((demandCompatRate p d r W + constituentPCompDelta40 p ε) *
    (b * m : ℝ) + constituentPCompLoss40 p b m)
  apply apq_parent_pcompMax_le p d b ε m r W B (Real.exp_pos _).le
  intro β
  rw [(compatibility_quotient_parent40 p d hd m hb ε r W β).2]
  calc
    Parent25.jointQ p d b ε m r W β / Parent25.jointP p d b ε m r W β ≤
        Real.exp ((Parent25.qRate p d r W - Parent25.pRate p d b ε m r W β) *
          (b * m : ℕ) + constituentPCompLoss40 p b m) := by
      simpa only [constituentPCompLoss40, constituentPCompPower40] using
        apq_joint_ratio_bound p d hd m hb ε r W β
    _ ≤ B := by
      dsimp only [B]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right
        (parent25_rate_continuity40 p d hd hb ε hε hmpos r W β)
        (show (0 : ℝ) ≤ ((b * m : ℕ) : ℝ) from Nat.cast_nonneg _)
      simpa only [Nat.cast_mul, add_comm] using
        add_le_add_right hmul (constituentPCompLoss40 p b m)

end OmegaBound.ADVXXZGeneral
end
