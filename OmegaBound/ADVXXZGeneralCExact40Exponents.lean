import OmegaBound.ADVXXZGeneralCExact40QTypes

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

namespace Parent25

/-- The two Parent25 entropy-exponent identities at one empirical-grid scale. -/
def ExponentBridge40 : Prop :=
  ∀ {w s b m : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
    ∀ ε r W (β : RepresentedLaw p d b ε m r W) (j : AlphaLabel p d b m r),
      (∑ t, ∑ c : Cell p t,
        let n := Nat.card (CellPos p d b m r W j.val t c)
        (n : ℝ) * entropyNats (fun σ => (cellHistogram p d m r W t c σ : ℝ) / n)) =
          qRate p d r W * (b*m : ℕ) ∧
      (∑ t, let n := parentCount p d b m r t
        (n : ℝ) * (entropyNats (fun σ => (betaCount p d b ε m r W β t σ : ℝ) / n) -
          entropyNats (fun c => (projectedCount (fun σ : Chunk (w+w) => grade (leftHalf σ))
            (betaCount p d b ε m r W β t) c : ℝ) / n))) =
          pRate p d b ε m r W β * (b*m : ℕ)

end Parent25

private theorem apq_probR_eq_cast_prob {ι : Type*} [Fintype ι]
    (P : RatDist ι) (a : ι) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem apq_floor_nat (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem apq_alphaCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (Parent25.alphaCount p d b m r t v : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob v := by
  rcases hb.alphaIntegral t r v with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob v =
        ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) *
          ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob v) := by
        push_cast
        ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  unfold Parent25.alphaCount
  rw [hscaled, apq_floor_nat]

private theorem apq_parentCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    (Parent25.parentCount p d b m r t : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r := by
  unfold Parent25.parentCount
  rw [Nat.cast_sum]
  simp_rw [apq_alphaCount_cast p d m hb r t]
  rw [← Finset.mul_sum, RatDist.sum_prob]
  ring

private theorem apq_alphaCount_cast_real {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (Parent25.alphaCount p d b m r t v : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
        ((d.alpha t r).prob v : ℝ) := by
  exact_mod_cast apq_alphaCount_cast p d m hb r t v

private theorem apq_coordFin_val {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

private theorem apq_betaCount_eq_typeCnt {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (ha : Parent25.empirical p d b m r W a = β.val)
    (t : Fin s) (σ : Chunk (w+w)) :
    Parent25.betaCount p d b ε m r W β t σ =
      OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ := by
  have ha' := congrFun (congrFun ha t) σ
  unfold Parent25.betaCount
  rw [← ha']
  unfold Parent25.empirical
  by_cases hn : Parent25.parentCount p d b m r t = 0
  · haveI : IsEmpty (Fin (Parent25.parentCount p d b m r t)) := by
      rw [hn]
      infer_instance
    have hcnt : OmegaBound.ADVXXZ.typeCnt
        (fun i => Parent25.paired a t i) σ = 0 := by
      simp [OmegaBound.ADVXXZ.typeCnt]
    rw [hcnt]
    simp only [Nat.cast_zero, zero_div, zero_mul]
    exact apq_floor_nat 0
  · rw [div_mul_cancel₀]
    · exact apq_floor_nat _
    · exact_mod_cast hn

private theorem apq_typeCnt_comp_eq_projectedCount
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ) (x : Fin n → α)
    (hx : ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k a) (c : γ) :
    OmegaBound.ADVXXZ.typeCnt (fun i => g (x i)) c = projectedCount g k c := by
  classical
  rw [OmegaBound.ADVXXZ.typeCnt, projectedCount,
    Finset.card_eq_sum_card_fiberwise (f := x)
      (s := (Finset.univ : Finset (Fin n)).filter (fun i => g (x i) = c))
      (t := (Finset.univ : Finset α).filter (fun a => g a = c))]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [← hx a, OmegaBound.ADVXXZ.typeCnt]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hxi
      exact ⟨by simpa [hxi] using (Finset.mem_filter.mp ha).2, hxi⟩
  · intro i hi
    have hi' : i ∈ (Finset.univ : Finset (Fin n)) ∧ g (x i) = c :=
      Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.2⟩)

theorem parent25_betaCount_sum40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) (t : Fin s) :
    ∑ σ, Parent25.betaCount p d b ε m r W β t σ =
      Parent25.parentCount p d b m r t := by
  classical
  rcases parent25_representedLaw_witness p d ε m r W β with ⟨J, a, _, ha⟩
  calc
    _ = ∑ σ, OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact apq_betaCount_eq_typeCnt p d ε m r W β a ha t σ
    _ = _ := OmegaBound.ADVXXZ.sum_typeCnt _

private theorem apq_betaCount_normalized {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (t : Fin s) (hn : Parent25.parentCount p d b m r t ≠ 0) :
    (fun σ => (Parent25.betaCount p d b ε m r W β t σ : ℝ) /
        Parent25.parentCount p d b m r t) =
      fun σ => (β.val t σ : ℝ) := by
  funext σ
  rcases parent25_representedLaw_witness p d ε m r W β with ⟨J, a, _, ha⟩
  have hcount := apq_betaCount_eq_typeCnt p d ε m r W β a ha t σ
  have hlaw := congrFun (congrFun ha t) σ
  unfold Parent25.empirical at hlaw
  rw [hcount]
  calc
    (OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ : ℝ) /
        Parent25.parentCount p d b m r t =
      (((OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ : ℚ) /
        Parent25.parentCount p d b m r t : ℚ) : ℝ) := by
          simp only [Rat.cast_div, Rat.cast_natCast]
    _ = (β.val t σ : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) hlaw

private theorem apq_projected_normalized {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r)
    (t : Fin s) (hn : Parent25.parentCount p d b m r t ≠ 0) :
    (fun c => (projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
          (Parent25.betaCount p d b ε m r W β t) c : ℝ) /
        Parent25.parentCount p d b m r t) =
      constituentMarginal d.toPaper t r (Parent25.side d r W) := by
  funext c
  rw [← parent25_projected_beta_count p d ε m r W β J t c]
  have htype := apq_typeCnt_comp_eq_projectedCount
    (fun u : ChildShape p t => Parent25.coordFin (Parent25.side d r W) u.val)
    (Parent25.alphaCount p d b m r t)
    (fun i => J.val.val ⟨t, i, 0⟩)
    (fun u => parent25_alphaLabel_target_count p d r J t u) c
  rw [htype]
  unfold projectedCount constituentMarginal
  have hfilter :
      (Finset.univ.filter fun u : ChildShape p t =>
        Parent25.coordFin (Parent25.side d r W) u.val = c) =
      Finset.univ.filter fun u : ChildShape p t =>
        coord (Parent25.side d r W) u.val = c.val := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h
    · simpa only [apq_coordFin_val] using congrArg Fin.val h
    · apply Fin.ext
      simpa only [apq_coordFin_val] using h
  rw [hfilter]
  rw [← Finset.sum_filter]
  have hnq : (Parent25.parentCount p d b m r t : ℚ) ≠ 0 := by exact_mod_cast hn
  have hscaleq := apq_parentCount_cast p d m hb r t
  have hscaleq_ne :
      (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r) ≠ 0 := hscaleq ▸ hnq
  have hscale :
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) ≠ 0 := by
    exact_mod_cast hscaleq_ne
  rw [Nat.cast_sum]
  simp_rw [apq_alphaCount_cast_real p d m hb r t]
  rw [show (Parent25.parentCount p d b m r t : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) by exact_mod_cast hscaleq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  rw [show d.toPaper.alpha t r u = ((d.alpha t r).prob u : ℝ) by
    simp only [ConstituentSpec.toPaper, apq_probR_eq_cast_prob]]
  change
    (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
        ((d.alpha t r).prob u : ℝ)) /
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) =
        ((d.alpha t r).prob u : ℝ)
  exact mul_div_cancel_left₀ _ hscale

private theorem apq_entropyNats_eq_log_two_mul_entropy40
    {α : Type*} [Fintype α] (f : α → ℝ) :
    entropyNats f = Real.log 2 * entropy f := by
  calc
    entropyNats f = Entropy.H Finset.univ f := by
      exact (Entropy.H_eq_neg_sum Finset.univ f).symm
    _ = entropy f * Real.log 2 := by
      simpa only [entropy] using (Entropy.H_mul_log_two Finset.univ f).symm
    _ = Real.log 2 * entropy f := by ring

/-- A represented complete paired law is the normalized exact beta-count table on every
occupied parent. -/
theorem parent25_betaCount_normalized40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (t : Fin s) (hn : Parent25.parentCount p d b m r t ≠ 0) :
    (fun σ => (Parent25.betaCount p d b ε m r W β t σ : ℝ) /
        Parent25.parentCount p d b m r t) =
      fun σ => (β.val t σ : ℝ) :=
  apq_betaCount_normalized p d ε m r W β t hn

/-- The integral parent count, retaining the exact natural scale factor. -/
theorem parent25_parentCount_cast40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    (Parent25.parentCount p d b m r t : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r :=
  apq_parentCount_cast p d m hb r t

/-- Conversion between the natural-log and base-two entropy conventions. -/
theorem entropyNats_eq_log_two_mul_entropy40
    {alpha : Type*} [Fintype alpha] (f : alpha → ℝ) :
    entropyNats f = Real.log 2 * entropy f :=
  apq_entropyNats_eq_log_two_mul_entropy40 f

private theorem apq_scaled_entropy_rho {α : Type*} [Fintype α]
    (n : ℕ) (k : α → ℕ) (L mass : ℝ) (rho : α → ℝ)
    (hn : (n : ℝ) = L * mass)
    (hk : ∀ a, (k a : ℝ) = L * mass * rho a) :
    (n : ℝ) * entropyNats (fun a => (k a : ℝ) / n) =
      L * mass * entropyNats rho := by
  by_cases hn0 : n = 0
  · have hzero : L * mass = 0 := by simpa [hn0] using hn.symm
    simp [hn0, hzero]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hnormalized : (fun a => (k a : ℝ) / n) = rho := by
      funext a
      rw [hk a, ← hn]
      exact mul_div_cancel_left₀ _ hnR
    rw [hnormalized, hn]

private theorem apq_scaled_entropy_num {α : Type*} [Fintype α]
    (n : ℕ) (k : α → ℕ) (L mass : ℝ) (num : α → ℝ)
    (hn : (n : ℝ) = L * mass)
    (hk : ∀ a, (k a : ℝ) = L * num a) :
    (n : ℝ) * entropyNats (fun a => (k a : ℝ) / n) =
      L * mass * entropyNats (fun a => num a / mass) := by
  by_cases hn0 : n = 0
  · have hzero : L * mass = 0 := by simpa [hn0] using hn.symm
    simp [hn0, hzero]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hprod : L * mass ≠ 0 := hn ▸ hnR
    have hL : L ≠ 0 := left_ne_zero_of_mul hprod
    have hmass : mass ≠ 0 := right_ne_zero_of_mul hprod
    have hnormalized : (fun a => (k a : ℝ) / n) = fun a => num a / mass := by
      funext a
      rw [hk a, hn]
      field_simp [hL, hmass]
    rw [hnormalized, hn]

private theorem apq_childCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (W : Fin 2)
    (t : Fin s) (v : ChildShape p t) (σ : Chunk w) :
    (Parent25.childCount p d m r W t v σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t, r, v⟩ *
        (d.betaChild (Parent25.side d r W) t r v).prob σ := by
  simpa [Parent25.childCount, stageCounts27] using
    hb.countsExact r (Parent25.side d r W) t v σ

private theorem apq_symWeight_eq {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (t : Fin s) (r : Fin 6) (v : ChildShape p t) :
    symWeight d.toPaper t r v =
      (d.alpha t r).probR v + (d.alpha t r).probR (complement p t v) := by
  simp [symWeight, ConstituentSpec.toPaper]

private theorem apq_toPaper_betaChild {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (S : Side) (t : Fin s) (r : Fin 6)
    (u : ChildShape p t) :
    d.toPaper.betaChild S t r u = d.betaChild S t r u := by
  rfl

private theorem apq_childCount_cast_real {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (t : Fin s)
    (v : ChildShape p t) (σ : Chunk w) :
    (Parent25.childCount p d m r W t v σ : ℝ) =
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) *
        symWeight d.toPaper t r v *
          (d.betaChild (Parent25.side d r W) t r v).probR σ := by
  have hq := apq_childCount_cast p d m hb r W t v σ
  rw [hd.out_eq t r v] at hq
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
  rw [apq_symWeight_eq d t r v]
  simp_rw [apq_probR_eq_cast_prob]
  simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Nat.cast_ofNat] using hr.trans (by
    push_cast
    ring)

private theorem apq_key_eq_inl_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    {t : Fin s} (u v : ChildShape p t) :
    Parent25.key d r W u = Sum.inl v ↔ Parent25.boundary d r W u.val ∧ u = v := by
  classical
  unfold Parent25.key
  by_cases h : Parent25.boundary d r W u.val
  · simp [h]
  · simp [h]

private theorem apq_key_eq_inr_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    {t : Fin s} (u : ChildShape p t) (k : Fin (2*w+1)) :
    Parent25.key d r W u = Sum.inr k ↔
      ¬ Parent25.boundary d r W u.val ∧
        Parent25.coordFin (Parent25.side d r W) u.val = k := by
  classical
  unfold Parent25.key
  by_cases h : Parent25.boundary d r W u.val
  · simp [h]
  · simp [h]

private theorem apq_boundary_histogram_of {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (r : Fin 6) (W : Fin 2) (t : Fin s) (v : ChildShape p t)
    (σ : Chunk w) (hv : Parent25.boundary d r W v.val) :
    Parent25.cellHistogram p d m r W t (.inl v) σ =
      Parent25.childCount p d m r W t v σ := by
  classical
  unfold Parent25.cellHistogram
  simp only [apq_key_eq_inl_iff]
  have hcond : ∀ u : ChildShape p t,
      (Parent25.boundary d r W u.val ∧ u = v) ↔ u = v := by
    intro u
    constructor
    · exact And.right
    · intro huv
      subst u
      exact ⟨hv, rfl⟩
  simp_rw [hcond]
  rw [Finset.sum_ite_eq']
  simp

private theorem apq_boundary_histogram_not {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (r : Fin 6) (W : Fin 2) (t : Fin s) (v : ChildShape p t)
    (σ : Chunk w) (hv : ¬ Parent25.boundary d r W v.val) :
    Parent25.cellHistogram p d m r W t (.inl v) σ = 0 := by
  classical
  unfold Parent25.cellHistogram
  simp only [apq_key_eq_inl_iff]
  have hnone : ∀ u : ChildShape p t,
      ¬(Parent25.boundary d r W u.val ∧ u = v) := by
    intro u hu
    exact hv (hu.2 ▸ hu.1)
  simp [hnone]

private theorem apq_residual_histogram_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (t : Fin s) (k : Fin (2*w+1))
    (σ : Chunk w) :
    (Parent25.cellHistogram p d m r W t (.inr k) σ : ℝ) =
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) *
        (∑ u, if Parent25.key d r W u = Sum.inr k then
          symWeight d.toPaper t r u *
            (d.betaChild (Parent25.side d r W) t r u).probR σ else 0) := by
  classical
  unfold Parent25.cellHistogram
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : Parent25.key d r W u = Sum.inr k
  · simp only [hu, if_pos]
    simpa only [mul_assoc] using apq_childCount_cast_real p d hd m hb r W t u σ
  · simp [hu]

private theorem apq_boundary_cell_entropy_of {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (J : AlphaLabel p d b m r)
    (t : Fin s) (v : ChildShape p t) (hv : Parent25.boundary d r W v.val) :
    let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v))
    (n : ℝ) * entropyNats (fun σ =>
      (Parent25.cellHistogram p d m r W t (.inl v) σ : ℝ) / n) =
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) *
        symWeight d.toPaper t r v *
          entropyNats (d.betaChild (Parent25.side d r W) t r v).probR := by
  classical
  dsimp only
  let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v))
  let L := ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)
  have htotal := (constituent_Q_type_classes40 p d hd hb r W J).2 t (.inl v)
  have hhist : ∀ σ : Chunk w,
      (Parent25.cellHistogram p d m r W t (.inl v) σ : ℝ) =
      L * symWeight d.toPaper t r v *
        (d.betaChild (Parent25.side d r W) t r v).probR σ := by
    intro σ
    rw [apq_boundary_histogram_of p d m r W t v σ hv]
    exact apq_childCount_cast_real p d hd m hb r W t v σ
  have hn : (n : ℝ) = L * symWeight d.toPaper t r v := by
    calc
      (n : ℝ) = (∑ σ, Parent25.cellHistogram p d m r W t (.inl v) σ : ℕ) := by
        exact_mod_cast htotal.symm
      _ = ∑ σ, (Parent25.cellHistogram p d m r W t (.inl v) σ : ℝ) := by
        norm_cast
      _ = ∑ σ, L * symWeight d.toPaper t r v *
          (d.betaChild (Parent25.side d r W) t r v).probR σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hhist σ
      _ = L * symWeight d.toPaper t r v := by
        rw [← Finset.mul_sum, RatDist.sum_probR]
        ring
  exact apq_scaled_entropy_rho n
    (Parent25.cellHistogram p d m r W t (.inl v)) L
    (symWeight d.toPaper t r v)
    (d.betaChild (Parent25.side d r W) t r v).probR hn hhist

private theorem apq_boundary_cell_entropy_not {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (J : AlphaLabel p d b m r)
    (t : Fin s) (v : ChildShape p t) (hv : ¬ Parent25.boundary d r W v.val) :
    let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v))
    (n : ℝ) * entropyNats (fun σ =>
      (Parent25.cellHistogram p d m r W t (.inl v) σ : ℝ) / n) = 0 := by
  classical
  dsimp only
  let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v))
  have htotal := (constituent_Q_type_classes40 p d hd hb r W J).2 t (.inl v)
  have hhist : ∀ σ : Chunk w,
      Parent25.cellHistogram p d m r W t (.inl v) σ = 0 := by
      intro σ
      exact apq_boundary_histogram_not p d m r W t v σ hv
  have hn : Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v)) = 0 := by
    rw [← htotal]
    simp only [hhist, Finset.sum_const_zero]
  rw [hn]
  simp only [Nat.cast_zero, zero_mul]

private theorem apq_residual_cell_entropy {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (J : AlphaLabel p d b m r)
    (t : Fin s) (k : Fin (2*w+1)) :
    let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inr k))
    let mass := ∑ u, if Parent25.key d r W u = Sum.inr k then
      symWeight d.toPaper t r u else 0
    (n : ℝ) * entropyNats (fun σ =>
      (Parent25.cellHistogram p d m r W t (.inr k) σ : ℝ) / n) =
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) * mass *
        entropyNats (weightedSplit (symWeight d.toPaper t r)
          (d.betaChild (Parent25.side d r W) t r)
          (fun u => Parent25.key d r W u = Sum.inr k)) := by
  classical
  dsimp only
  let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inr k))
  let L := ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)
  let mass := ∑ u, if Parent25.key d r W u = Sum.inr k then
    symWeight d.toPaper t r u else 0
  let num : Chunk w → ℝ := fun σ =>
    ∑ u, if Parent25.key d r W u = Sum.inr k then
      symWeight d.toPaper t r u *
        (d.betaChild (Parent25.side d r W) t r u).probR σ else 0
  have hhist : ∀ σ, (Parent25.cellHistogram p d m r W t (.inr k) σ : ℝ) =
      L * num σ := by
    intro σ
    exact apq_residual_histogram_cast p d hd m hb r W t k σ
  have htotal := (constituent_Q_type_classes40 p d hd hb r W J).2 t (.inr k)
  have hnumsum : ∑ σ, num σ = mass := by
    unfold num mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : Parent25.key d r W u = Sum.inr k
    · simp only [hu, if_pos, ← Finset.mul_sum, RatDist.sum_probR, mul_one]
    · simp [hu]
  have hn : (n : ℝ) = L * mass := by
    calc
      (n : ℝ) = (∑ σ, Parent25.cellHistogram p d m r W t (.inr k) σ : ℕ) := by
        exact_mod_cast htotal.symm
      _ = ∑ σ, (Parent25.cellHistogram p d m r W t (.inr k) σ : ℝ) := by
        norm_cast
      _ = ∑ σ, L * num σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hhist σ
      _ = L * mass := by rw [← Finset.mul_sum, hnumsum]
  have hscaled := apq_scaled_entropy_num n
    (Parent25.cellHistogram p d m r W t (.inr k)) L mass num hn hhist
  simpa only [weightedSplit, num, mass] using hscaled

private theorem apq_key_y_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) {t : Fin s}
    (u : ChildShape p t) (k : Fin (2 * w + 1)) :
    Parent25.key d r (0 : Fin 2) u = Sum.inr k ↔
      coord (d.perm r .Y) u.val = k.val ∧ 0 < coord (d.perm r .Z) u.val := by
  rw [apq_key_eq_inr_iff]
  simp only [Parent25.boundary, Parent25.side, if_pos, Fin.ext_iff, apq_coordFin_val]
  omega

private theorem apq_key_z_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) {t : Fin s}
    (u : ChildShape p t) (k : Fin (2 * w + 1)) :
    Parent25.key d r (1 : Fin 2) u = Sum.inr k ↔
      0 < coord (d.perm r .X) u.val ∧ 0 < coord (d.perm r .Y) u.val ∧
        coord (d.perm r .Z) u.val = k.val := by
  have h10 : (1 : Fin 2) ≠ 0 := by omega
  rw [apq_key_eq_inr_iff]
  simp only [Parent25.boundary, Parent25.side, h10, if_false, Fin.ext_iff,
    apq_coordFin_val]
  omega

private theorem apq_weightedSplit_congr {ι : Type*} [Fintype ι] {w : ℕ}
    (mass : ι → ℝ) (laws : ι → SplitDist w) (P Q : ι → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ u, P u ↔ Q u) :
    weightedSplit mass laws P = weightedSplit mass laws Q := by
  funext σ
  unfold weightedSplit
  apply congrArg₂ (· / ·)
  · apply Finset.sum_congr rfl
    intro u _
    exact if_congr (h u) rfl rfl
  · apply Finset.sum_congr rfl
    intro u _
    exact if_congr (h u) rfl rfl

private theorem apq_q_parent_entropy {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
     (r : Fin 6) (W : Fin 2) (J : AlphaLabel p d b m r)
    (t : Fin s) :
    (∑ c : Parent25.Cell p t,
      let n := Nat.card (Parent25.CellPos p d b m r W J.val t c)
      (n : ℝ) * entropyNats (fun σ =>
        (Parent25.cellHistogram p d m r W t c σ : ℝ) / n)) =
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)) *
        Real.log 2 *
          (if W = 0 then
            constituentEta d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
          else constituentLambda d.toPaper t r
            (d.perm r .X) (d.perm r .Y) (d.perm r .Z)) := by
  classical
  let L := ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ)
  rw [Fintype.sum_sum_type]
  have hcells :
      (∑ v : ChildShape p t,
          let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inl v))
          (n : ℝ) * entropyNats (fun σ =>
            (Parent25.cellHistogram p d m r W t (.inl v) σ : ℝ) / n)) +
        (∑ k : Fin (2 * w + 1),
          let n := Nat.card (Parent25.CellPos p d b m r W J.val t (.inr k))
          (n : ℝ) * entropyNats (fun σ =>
            (Parent25.cellHistogram p d m r W t (.inr k) σ : ℝ) / n)) =
      (∑ v : ChildShape p t,
          if Parent25.boundary d r W v.val then
            L * symWeight d.toPaper t r v *
              entropyNats (d.betaChild (Parent25.side d r W) t r v).probR
          else 0) +
        ∑ k : Fin (2 * w + 1),
          let mass := ∑ u, if Parent25.key d r W u = Sum.inr k then
            symWeight d.toPaper t r u else 0
          L * mass * entropyNats
            (weightedSplit (symWeight d.toPaper t r)
              (d.betaChild (Parent25.side d r W) t r)
              (fun u => Parent25.key d r W u = Sum.inr k)) := by
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : Parent25.boundary d r W v.val
      · rw [if_pos hv]
        exact apq_boundary_cell_entropy_of p d hd m hb r W J t v hv
      · rw [if_neg hv]
        exact apq_boundary_cell_entropy_not p d hd m hb r W J t v hv
    · apply Finset.sum_congr rfl
      intro k _
      exact apq_residual_cell_entropy p d hd m hb r W J t k
  rw [hcells]
  by_cases hW : W = 0
  · subst W
    simp only [Parent25.boundary, Parent25.side, if_pos]
    simp_rw [apq_entropyNats_eq_log_two_mul_entropy40]
    simp_rw [apq_key_y_iff]
    unfold constituentEta splitEntropy
    simp_rw [apq_toPaper_betaChild]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : coord (d.perm r .Z) v.val = 0
      · simp only [hv, if_pos]
        ring
      · simp [hv]
    · apply Finset.sum_congr rfl
      intro k _
      have hweighted :
          weightedSplit (symWeight d.toPaper t r)
              (d.betaChild (d.perm r .Y) t r)
              (fun u => Parent25.key d r (0 : Fin 2) u = Sum.inr k) =
            constituentAverage d.toPaper t r (d.perm r .Y)
              (d.perm r .Y) (d.perm r .Z) k := by
        unfold constituentAverage
        apply apq_weightedSplit_congr
        intro u
        exact apq_key_y_iff d r u k
      rw [hweighted]
      ring
  · have hW1 : W = 1 := by omega
    subst W
    have h10 : (1 : Fin 2) ≠ 0 := by omega
    simp only [Parent25.boundary, Parent25.side, h10, if_false]
    simp_rw [apq_entropyNats_eq_log_two_mul_entropy40]
    simp_rw [apq_key_z_iff]
    unfold constituentLambda splitEntropy
    simp_rw [apq_toPaper_betaChild]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro v _
      by_cases hv : coord (d.perm r .X) v.val = 0 ∨ coord (d.perm r .Y) v.val = 0
      · simp only [hv, if_pos]
        ring
      · simp [hv]
    · apply Finset.sum_congr rfl
      intro k _
      have hweighted :
          weightedSplit (symWeight d.toPaper t r)
              (d.betaChild (d.perm r .Z) t r)
              (fun u => Parent25.key d r (1 : Fin 2) u = Sum.inr k) =
            weightedSplit (symWeight d.toPaper t r)
              (d.betaChild (d.perm r .Z) t r)
              (fun u => 0 < coord (d.perm r .X) u.val ∧
                0 < coord (d.perm r .Y) u.val ∧
                coord (d.perm r .Z) u.val = k.val) := by
        apply apq_weightedSplit_congr
        intro u
        exact apq_key_z_iff d r u k
      rw [hweighted]
      have hbeta : d.toPaper.betaChild (d.perm r .Z) t r =
          d.betaChild (d.perm r .Z) t r := by
        funext u
        exact apq_toPaper_betaChild d (d.perm r .Z) t r u
      rw [hbeta]
      ring

/-- The exact Q-fibre exponent in parent-indexed form.  Boundary and residual cells are
kept separate until their finite entropy expressions are identified with Eta/Lambda. -/
theorem parent25_q_exponent_identity40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    (∑ t, ∑ c : Parent25.Cell p t,
      let n := Nat.card (Parent25.CellPos p d b m r W J.val t c)
      (n : ℝ) * entropyNats (fun σ =>
        (Parent25.cellHistogram p d m r W t c σ : ℝ) / n)) =
      Parent25.qRate p d r W * (b*m : ℕ) := by
  classical
  unfold Parent25.qRate
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [apq_q_parent_entropy p d hd m hb r W J t]
  push_cast
  ring

/-- The exact P-fibre exponent in parent-indexed form, including empty parents and
the unchanged `(b*m)` scale. -/
theorem parent25_p_exponent_identity40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (β : RepresentedLaw p d b ε m r W) (J : AlphaLabel p d b m r) :
    (∑ t, let n := Parent25.parentCount p d b m r t
      (n : ℝ) * (entropyNats (fun σ =>
          (Parent25.betaCount p d b ε m r W β t σ : ℝ) / n) -
        entropyNats (fun c =>
          (projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
            (Parent25.betaCount p d b ε m r W β t) c : ℝ) / n))) =
      Parent25.pRate p d b ε m r W β * (b*m : ℕ) := by
  classical
  unfold Parent25.pRate
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  have hcountQ := apq_parentCount_cast p d m hb r t
  have hcountR : (Parent25.parentCount p d b m r t : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := by
    exact_mod_cast hcountQ
  by_cases hn : Parent25.parentCount p d b m r t = 0
  · rw [hn]
    simp only [Nat.cast_zero, zero_mul]
    symm
    calc
      Real.log 2 *
          (↑(p.baseN t) * ↑((d.A t).prob r) *
            (entropy (fun σ => (β.val t σ : ℝ)) -
              entropy (constituentMarginal d.toPaper t r (Parent25.side d r W)))) *
          ↑(b * m) =
        (((b * m * p.baseN t : ℕ) : ℝ) * ↑((d.A t).prob r)) *
          (Real.log 2 *
            (entropy (fun σ => (β.val t σ : ℝ)) -
              entropy (constituentMarginal d.toPaper t r (Parent25.side d r W)))) := by
          push_cast
          ring
      _ = 0 := by rw [← hcountR, hn]; simp
  · rw [apq_betaCount_normalized p d ε m r W β t hn,
      apq_projected_normalized p d m hb ε r W β J t hn]
    rw [apq_entropyNats_eq_log_two_mul_entropy40,
      apq_entropyNats_eq_log_two_mul_entropy40]
    rw [hcountR]
    push_cast
    ring

theorem constituent_PQ_exponents40 : Parent25.ExponentBridge40 := by
  intro w s b m p d hd hb ε r W β J
  exact ⟨parent25_q_exponent_identity40 p d hd m hb ε r W β J,
    parent25_p_exponent_identity40 p d hd m hb ε r W β J⟩

end OmegaBound.ADVXXZGeneral
end
