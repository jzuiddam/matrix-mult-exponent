import OmegaBound.ADVXXZGeneralCExact40Counts
import OmegaBound.ADVXXZGeneralCExact40PCompBound

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable section

/- `ADVXXZGeneralCExact40Counts` keeps its implementation lemmas private.  Re-export kernel
aliases by their unique declaration suffix. -/
open Lean Elab Command in
private def findDemandCheckpointName
    (env : Environment) (suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains "_private.OmegaBound.ADVXXZGeneralCExact40Counts." ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then
    return names[0]
  else
    throwError "expected one demand-checkpoint declaration ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_demand_checkpoint41 " id:ident " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findDemandCheckpointName env suffix.getString
  let newName := (← getCurrNamespace) ++ id.getId
  let some info := env.find? oldName | throwError "demand-checkpoint declaration vanished"
  let value := mkConst oldName (info.levelParams.map Level.param)
  match info with
  | .defnInfo d =>
      liftCoreM <| addDecl <| .defnDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value
        hints := .abbrev
        safety := .safe
      }
  | .thmInfo d =>
      liftCoreM <| addDecl <| .thmDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value
      }
  | _ => throwError "unsupported demand-checkpoint declaration kind for {oldName}"

expose_demand_checkpoint41 demand25ParentCount40 :=
  ".OmegaBound.ADVXXZGeneral.demandParentCount"
expose_demand_checkpoint41 Demand25ValidTable40 :=
  ".OmegaBound.ADVXXZGeneral.DemandValidTable"
expose_demand_checkpoint41 demand25ValidTableFintype40Checkpoint40 :=
  ".OmegaBound.ADVXXZGeneral.demandValidTableFintype"
expose_demand_checkpoint41 demand25ParentFactor40 :=
  ".OmegaBound.ADVXXZGeneral.demandParentFactor"
expose_demand_checkpoint41 demand25AllFactor40 :=
  ".OmegaBound.ADVXXZGeneral.demandAllFactor"
expose_demand_checkpoint41 demand25TargetParentFactor40 :=
  ".OmegaBound.ADVXXZGeneral.demandTargetParentFactor"
expose_demand_checkpoint41 demand25TargetAllFactor40 :=
  ".OmegaBound.ADVXXZGeneral.demandTargetAllFactor"
expose_demand_checkpoint41 demand25LabelCardCheckpoint40 :=
  ".OmegaBound.ADVXXZGeneral.demand_label_card_le"
expose_demand_checkpoint41 demand25TargetCardCheckpoint40 :=
  ".OmegaBound.ADVXXZGeneral.demand_target_card_le"

noncomputable instance demand25ValidTableFintype40 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    Fintype (Demand25ValidTable40 (b := b) (m := m) p d r) := by
  exact demand25ValidTableFintype40Checkpoint40 (b := b) (m := m) p d r

theorem demand25_label_card_le40 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) :
    (Fintype.card (stagePopulationAt 0 p d b m r).Label : ℝ) ≤
      (((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
        (fun J => (stagePopulationAt 0 p d b m r).coarse J W)).card : ℝ) *
      ((Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) *
        demand25AllFactor40 (b := b) (m := m) p d r W) := by
  exact demand25LabelCardCheckpoint40 (b := b) (m := m) p d hb r W

theorem demand25_target_card_le40 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) :
    ((stagePopulationAt 0 p d b m r).target.card : ℝ) ≤
      (((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
        (fun J => (stagePopulationAt 0 p d b m r).coarse J W)).card : ℝ) *
      demand25TargetAllFactor40 (b := b) (m := m) p d r W := by
  exact demand25TargetCardCheckpoint40 (b := b) (m := m) p d hb r W

private theorem demand25_probR_eq_cast_prob {α : Type*} [Fintype α]
    (P : RatDist α) (a : α) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem demand25_parentCount_le {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    demand25ParentCount40 p d b m r t ≤ b * p.baseN t * m := by
  classical
  change Parent25.parentCount p d b m r t ≤ b * p.baseN t * m
  have hcast : (Parent25.parentCount p d b m r t : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := by
    exact_mod_cast parent25_parentCount_cast40 p d m hb r t
  have hprob : ((d.A t).prob r : ℝ) ≤ 1 := by
    rw [← demand25_probR_eq_cast_prob]
    calc
      (d.A t).probR r ≤ ∑ i, (d.A t).probR i :=
        Finset.single_le_sum (fun i _ => RatDist.probR_nonneg (d.A t) i)
          (Finset.mem_univ r)
      _ = 1 := RatDist.sum_probR (d.A t)
  exact_mod_cast (calc
    (Parent25.parentCount p d b m r t : ℝ) =
        ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := hcast
    _ ≤ ((b * m * p.baseN t : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hprob (Nat.cast_nonneg _)
    _ = (b * p.baseN t * m : ℕ) := by push_cast; ring)

private theorem demand25_factor_power_le {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (K : ℕ) :
    ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^ K ≤
      ((m : ℝ) + 1) ^ ((b * p.baseN t) * K) := by
  have hlinear : (demand25ParentCount40 p d b m r t : ℝ) + 1 ≤
      ((m : ℝ) + 1) ^ (b * p.baseN t) := by
    calc
      (demand25ParentCount40 p d b m r t : ℝ) + 1 ≤
          (b * p.baseN t * m : ℕ) + 1 := by
        exact_mod_cast Nat.add_le_add_right (demand25_parentCount_le p d m hb r t) 1
      _ = 1 + (b * p.baseN t : ℕ) * (m : ℝ) := by push_cast; ring
      _ ≤ (1 + (m : ℝ)) ^ (b * p.baseN t) :=
        one_add_mul_le_pow (by
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith) _
      _ = ((m : ℝ) + 1) ^ (b * p.baseN t) := by ring_nf
  calc
    ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^ K ≤
        (((m : ℝ) + 1) ^ (b * p.baseN t)) ^ K := by
      exact pow_le_pow_left₀ (by positivity) hlinear K
    _ = ((m : ℝ) + 1) ^ ((b * p.baseN t) * K) := by rw [← pow_mul]

private theorem demand25_poly_le_pow {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (K : Fin s → ℕ) :
    (∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^ K t) ≤
      ((m : ℝ) + 1) ^ (∑ t, (b * p.baseN t) * K t) := by
  classical
  calc
    (∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^ K t) ≤
        ∏ t, ((m : ℝ) + 1) ^ ((b * p.baseN t) * K t) := by
      apply Finset.prod_le_prod
      · intro t _
        positivity
      · intro t _
        exact demand25_factor_power_le p d m hb r t (K t)
    _ = ((m : ℝ) + 1) ^ (∑ t, (b * p.baseN t) * K t) := by
      rw [Finset.prod_pow_eq_pow_sum]

private theorem demand25_validTable_card_le {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    (Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) ≤
      ((m : ℝ) + 1) ^
        (∑ t : Fin s, (b * p.baseN t) * Fintype.card (ChildShape p t)) := by
  classical
  have hsub : Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) ≤
      Fintype.card ((t : Fin s) → ChildShape p t →
        Fin (demand25ParentCount40 p d b m r t + 1)) := by
    exact Fintype.card_subtype_le _
  have hcast : (Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) ≤
      ∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
        Fintype.card (ChildShape p t) := by
    exact_mod_cast (show Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) ≤
        ∏ t, (demand25ParentCount40 p d b m r t + 1) ^
          Fintype.card (ChildShape p t) by
      simpa only [Fintype.card_pi, Fintype.card_fun, Fintype.card_fin,
        Finset.prod_const] using hsub)
  exact hcast.trans (demand25_poly_le_pow p d m hb r
    (fun t => Fintype.card (ChildShape p t)))

private def demand25XRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r -
      entropy (constituentMarginal d.toPaper t r (d.perm r .X)))

private def demand25YBaseRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) -
      entropy (constituentMarginal d.toPaper t r (d.perm r .Y)))

private def demand25ZBaseRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) -
      entropy (constituentMarginal d.toPaper t r (d.perm r .Z)))

private def demand25YRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) +
      constituentEta d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
      splitEntropy (d.betaRegion (d.perm r .Y) t r))

private def demand25ZRate {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  Real.log 2 * ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) +
      constituentLambda d.toPaper t r (d.perm r .X) (d.perm r .Y) (d.perm r .Z) -
      splitEntropy (d.betaRegion (d.perm r .Z) t r))

private theorem demand25_compat_y {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    demand25YBaseRate p d r + demandCompatRate p d r 0 = demand25YRate p d r := by
  unfold demand25YBaseRate demand25YRate demandCompatRate
  simp only [if_pos rfl]
  have hA : ∀ t : Fin s, d.toPaper.A t r = ((d.A t).prob r : ℝ) := by
    intro t
    simp only [ConstituentSpec.toPaper, demand25_probR_eq_cast_prob]
  simp_rw [hA]
  simp only [if_true]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun x : ℝ => Real.log 2 * x)
  apply Finset.sum_congr rfl
  intro t _
  ring_nf

private theorem demand25_compat_z {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    demand25ZBaseRate p d r + demandCompatRate p d r 1 = demand25ZRate p d r := by
  unfold demand25ZBaseRate demand25ZRate demandCompatRate
  simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide +kernel)]
  have hA : ∀ t : Fin s, d.toPaper.A t r = ((d.A t).prob r : ℝ) := by
    intro t
    simp only [ConstituentSpec.toPaper, demand25_probR_eq_cast_prob]
  simp_rw [hA]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun x : ℝ => Real.log 2 * x)
  apply Finset.sum_congr rfl
  intro t _
  ring_nf

private theorem demand25_rate_le_exponent_x {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    demand25XRate p d r ≤ demandExponent p d r := by
  unfold demand25XRate demandExponent
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.log_pos one_lt_two).le

private theorem demand25_rate_le_exponent_y {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    demand25YRate p d r ≤ demandExponent p d r := by
  unfold demand25YRate demandExponent
  exact mul_le_mul_of_nonneg_left (le_max_of_le_right (le_max_left _ _))
    (Real.log_pos one_lt_two).le

private theorem demand25_rate_le_exponent_z {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :
    demand25ZRate p d r ≤ demandExponent p d r := by
  unfold demand25ZRate demandExponent
  exact mul_le_mul_of_nonneg_left (le_max_of_le_right (le_max_right _ _))
    (Real.log_pos one_lt_two).le

private def demand25ValidPower {w s b : ℕ} (p : ConstituentInput w s) : ℕ :=
  ∑ t : Fin s, (b * p.baseN t) * Fintype.card (ChildShape p t)

private def demand25CoarsePower {w s b : ℕ} (p : ConstituentInput w s) : ℕ :=
  ∑ t : Fin s, (b * p.baseN t) * Fintype.card (Fin (2*w+1))

private theorem demand25_allFactor_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    demand25AllFactor40 (b := b) (m := m) p d r (d.perm r .X) =
      Real.exp ((b*m : ℕ) * demand25XRate p d r) *
        ∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
          Fintype.card (Fin (2*w+1)) := by
  classical
  change (∏ t, Real.exp
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
        (Real.log 2 * (entropy (d.toPaper.alpha t r) +
          constituentPenalty d.toPaper t r -
          entropy (constituentMarginal d.toPaper t r (d.perm r .X))))) *
      ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
        Fintype.card (Fin (2*w+1))) = _
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  unfold demand25XRate
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ConstituentSpec.toPaper, demand25_probR_eq_cast_prob]
  push_cast
  ring

private theorem demand25_targetAllFactor_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) :
    demand25TargetAllFactor40 (b := b) (m := m) p d r (Parent25.side d r W) =
      Real.exp ((b*m : ℕ) *
        (if W = 0 then demand25YBaseRate p d r else demand25ZBaseRate p d r)) *
        ∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
          Fintype.card (Fin (2*w+1)) := by
  classical
  change (∏ t, Real.exp
      (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
        (Real.log 2 * (entropy (d.toPaper.alpha t r) -
          entropy (constituentMarginal d.toPaper t r (Parent25.side d r W))))) *
      ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
        Fintype.card (Fin (2*w+1))) = _
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  by_cases hW : W = 0
  · subst W
    simp only [Fin.isValue, ↓reduceIte, Parent25.side]
    unfold demand25YBaseRate
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [ConstituentSpec.toPaper, demand25_probR_eq_cast_prob]
    push_cast
    ring
  · simp only [hW, ↓reduceIte, Parent25.side]
    unfold demand25ZBaseRate
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [ConstituentSpec.toPaper, demand25_probR_eq_cast_prob]
    push_cast
    ring

private theorem demand25_poly_exp_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    (∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
        Fintype.card (Fin (2*w+1))) ≤
      Real.exp ((demand25CoarsePower (b := b) p : ℝ) *
        Real.log ((m : ℝ) + 1)) := by
  unfold demand25CoarsePower
  rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (m : ℝ) + 1)]
  exact demand25_poly_le_pow p d m hb r
    (fun _ => Fintype.card (Fin (2*w+1)))

private theorem demand25_allFactor_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) :
    (Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) *
        demand25AllFactor40 (b := b) (m := m) p d r (d.perm r .X) ≤
      Real.exp ((b*m : ℕ) * demand25XRate p d r +
        ((demand25ValidPower (b := b) p + demand25CoarsePower (b := b) p : ℕ) : ℝ) *
          Real.log ((m : ℝ) + 1)) := by
  rw [demand25_allFactor_eq p d r]
  have hv := demand25_validTable_card_le p d m hb r
  have hc := demand25_poly_exp_bound p d m hb r
  have hpow : ((m : ℝ) + 1) ^ demand25ValidPower (b := b) p =
      Real.exp ((demand25ValidPower (b := b) p : ℝ) * Real.log ((m : ℝ) + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (m : ℝ) + 1)]
  rw [show (∑ t : Fin s, (b * p.baseN t) * Fintype.card (ChildShape p t)) =
      demand25ValidPower (b := b) p by rfl, hpow] at hv
  calc
    (Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) *
        (Real.exp ((b*m : ℕ) * demand25XRate p d r) *
          ∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
            Fintype.card (Fin (2*w+1))) =
        Real.exp ((b*m : ℕ) * demand25XRate p d r) *
          ((Fintype.card (Demand25ValidTable40 (b := b) (m := m) p d r) : ℝ) *
            ∏ t, ((demand25ParentCount40 p d b m r t : ℝ) + 1) ^
              Fintype.card (Fin (2*w+1))) := by ring
    _ ≤ Real.exp ((b*m : ℕ) * demand25XRate p d r) *
        (Real.exp ((demand25ValidPower (b := b) p : ℝ) * Real.log ((m : ℝ) + 1)) *
          Real.exp ((demand25CoarsePower (b := b) p : ℝ) * Real.log ((m : ℝ) + 1))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hv hc (by positivity) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by
      rw [Nat.cast_add, add_mul, Real.exp_add, Real.exp_add]

private theorem demand25_targetAllFactor_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (W : Fin 2) :
    demand25TargetAllFactor40 (b := b) (m := m) p d r (Parent25.side d r W) ≤
      Real.exp ((b*m : ℕ) *
          (if W = 0 then demand25YBaseRate p d r else demand25ZBaseRate p d r) +
        (demand25CoarsePower (b := b) p : ℝ) * Real.log ((m : ℝ) + 1)) := by
  rw [demand25_targetAllFactor_eq p d r W, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (demand25_poly_exp_bound p d m hb r)
    (Real.exp_pos _).le

private theorem demand25_negMulLog_sum_le {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) (S : Finset α) :
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

private theorem demand25_entropy_map_le {α γ : Type*}
    [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    (p : α → ℝ) (hp : IsProbability p) (g : α → γ) :
    entropy (fun c => ∑ a ∈ (Finset.univ.filter fun a => g a = c), p a) ≤ entropy p := by
  let q := fun c : γ => ∑ a ∈ (Finset.univ.filter fun a => g a = c), p a
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    calc
      p a ≤ ∑ x, p x := Finset.single_le_sum (fun x _ => hp.1 x) (Finset.mem_univ a)
      _ = 1 := hp.2
  have hfiber :
      (∑ c ∈ (Finset.univ : Finset γ),
          ∑ a ∈ (Finset.univ.filter fun a => g a = c), Real.negMulLog (p a)) =
        ∑ a ∈ (Finset.univ : Finset α), Real.negMulLog (p a) := by
    exact Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset γ))
      (g := g) (fun a _ => Finset.mem_univ (g a)) (fun a => Real.negMulLog (p a))
  have hH : Entropy.H (Finset.univ : Finset γ) q ≤
      Entropy.H (Finset.univ : Finset α) p := by
    unfold Entropy.H
    calc
      (∑ c ∈ (Finset.univ : Finset γ), Real.negMulLog (q c)) ≤
          ∑ c ∈ (Finset.univ : Finset γ),
            ∑ a ∈ (Finset.univ.filter fun a => g a = c), Real.negMulLog (p a) := by
        apply Finset.sum_le_sum
        intro c _
        exact demand25_negMulLog_sum_le p hp.1 hp1 _
      _ = ∑ a ∈ (Finset.univ : Finset α), Real.negMulLog (p a) := hfiber
  unfold entropy Entropy.H₂
  exact div_le_div_of_nonneg_right hH (Real.log_pos one_lt_two).le

private theorem demand25_coordFin_val {w : ℕ} (W : Side) (u : Shape w) :
    (Parent25.coordFin W u).val = coord W u := by
  cases W <;> rfl

private theorem demand25_marginal_entropy_le {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (t : Fin s) (W : Side) :
    entropy (constituentMarginal d.toPaper t r W) ≤ entropy (d.toPaper.alpha t r) := by
  let g := fun u : ChildShape p t => Parent25.coordFin W u.val
  have hp : IsProbability (d.toPaper.alpha t r) := by
    constructor
    · intro u
      exact RatDist.probR_nonneg (d.alpha t r) u
    · exact RatDist.sum_probR (d.alpha t r)
  have hmap := demand25_entropy_map_le (d.toPaper.alpha t r) hp g
  have hq : (fun c => ∑ u ∈ (Finset.univ.filter fun u => g u = c),
      d.toPaper.alpha t r u) = constituentMarginal d.toPaper t r W := by
    funext c
    unfold constituentMarginal
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : g u = c
    · rw [if_pos h]
      rw [if_pos]
      exact (demand25_coordFin_val W u.val).symm.trans (congrArg Fin.val h)
    · rw [if_neg h]
      rw [if_neg]
      intro hv
      apply h
      apply Fin.ext
      exact (demand25_coordFin_val W u.val).trans hv
  rwa [hq] at hmap

private theorem demand25_x_term_nonneg {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (t : Fin s) :
    0 ≤ entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r -
      entropy (constituentMarginal d.toPaper t r (d.perm r .X)) := by
  let S : Set ℝ := {h : ℝ | ∃ a' : ChildShape p t → ℝ,
    IsProbability a' ∧ SameConstituentMarginals t (d.toPaper.alpha t r) a' ∧
      h = entropy a'}
  have hp : IsProbability (d.toPaper.alpha t r) := by
    constructor
    · intro u
      exact RatDist.probR_nonneg (d.alpha t r) u
    · exact RatDist.sum_probR (d.alpha t r)
  have hmem : entropy (d.toPaper.alpha t r) ∈ S := by
    exact ⟨d.toPaper.alpha t r, hp, fun W x => rfl, rfl⟩
  letI : Nonempty (ChildShape p t) := RatDist.nonempty (d.alpha t r)
  have hbdd : BddAbove S := by
    refine ⟨Real.log (Fintype.card (ChildShape p t) : ℝ) / Real.log 2, ?_⟩
    intro h hh
    rcases hh with ⟨a', ha', -, rfl⟩
    have hH := Entropy.H_le_log_card (s := (Finset.univ : Finset (ChildShape p t)))
      Finset.univ_nonempty (fun u _ => ha'.1 u) (by simpa using ha'.2)
    have hHn : entropyNats a' ≤ Real.log (Fintype.card (ChildShape p t) : ℝ) := by
      calc
        entropyNats a' = Entropy.H Finset.univ a' :=
          (Entropy.H_eq_neg_sum Finset.univ a').symm
        _ ≤ Real.log ((Finset.univ : Finset (ChildShape p t)).card : ℝ) := hH
        _ = _ := by simp
    rw [entropyNats_eq_log_two_mul_entropy, mul_comm] at hHn
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).2 hHn
  have hsup : entropy (d.toPaper.alpha t r) ≤ sSup S := le_csSup hbdd hmem
  have hmarg := demand25_marginal_entropy_le p d r t (d.perm r .X)
  unfold constituentPenalty
  change 0 ≤ entropy (d.toPaper.alpha t r) +
      (sSup S - entropy (d.toPaper.alpha t r)) - _
  linarith

private theorem demand25_exponent_nonneg {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : 0 ≤ demandExponent p d r := by
  apply (demand25_rate_le_exponent_x p d r).trans'
  unfold demand25XRate
  apply mul_nonneg (Real.log_pos one_lt_two).le
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg
  · apply mul_nonneg (Nat.cast_nonneg _)
    exact RatDist.probR_nonneg (d.A t) r
  · exact demand25_x_term_nonneg p d r t

private theorem demand25_loss_add {L : ℕ → ℕ} {ell₁ ell₂ : ℚ → ℕ → ℝ}
    (h₁ : Loss L ell₁) (h₂ : Loss L ell₂) :
    Loss L (fun ε m => ell₁ ε m + ell₂ ε m) := by
  constructor
  · intro ε m
    exact add_nonneg (h₁.1 ε m) (h₂.1 ε m)
  · intro ε hε δ hδ
    obtain ⟨M₁, hM₁⟩ := h₁.2 ε hε (δ/2) (half_pos hδ)
    obtain ⟨M₂, hM₂⟩ := h₂.2 ε hε (δ/2) (half_pos hδ)
    refine ⟨max M₁ M₂, ?_⟩
    intro m hm
    calc
      |ell₁ ε m + ell₂ ε m| ≤ |ell₁ ε m| + |ell₂ ε m| := abs_add_le _ _
      _ ≤ (δ/2) * (L m : ℝ) + (δ/2) * (L m : ℝ) :=
        add_le_add (hM₁ m ((le_max_left _ _).trans hm))
          (hM₂ m ((le_max_right _ _).trans hm))
      _ = δ * (L m : ℝ) := by ring

private theorem demand25_ratio_le {N K : ℕ} {B : ℝ} (hK : K ≠ 0)
    (h : (N : ℝ) ≤ (K : ℝ) * B) : (N : ℝ) / K ≤ B := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  exact (div_le_iff₀ hKpos).2 (by simpa [mul_comm] using h)

private theorem demand25_ceil_le {x B : ℝ} (hx : 0 ≤ x) (h : x ≤ B) :
    (Nat.ceil x : ℝ) ≤ B + 1 := by
  exact (Nat.ceil_lt_add_one hx).le.trans (by linarith)

private theorem demand25_parent_pcomp_nonneg {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    0 ≤ Parent25.pcomp p d b ε m r W β := by
  classical
  unfold Parent25.pcomp
  dsimp only
  split_ifs <;> positivity

private theorem demand25_parent_pcompMax_nonneg {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) :
    0 ≤ Parent25.pcompMax p d b ε m r W := by
  classical
  unfold Parent25.pcompMax
  dsimp only
  let values := (Finset.univ : Finset (RepresentedLaw p d b ε m r W)).image
    (Parent25.pcomp p d b ε m r W)
  by_cases hv : values.Nonempty
  · rw [dif_pos hv]
    rcases Finset.mem_image.mp (Finset.max'_mem values hv) with ⟨β, -, hβ⟩
    rw [← hβ]
    exact demand25_parent_pcomp_nonneg p d ε m r W β
  · rw [dif_neg hv]

private theorem demand25_log_nat_le_scaled_log_succ (K m : ℕ) (hK : 0 < K)
    (hm : 1 ≤ m) :
    Real.log (K : ℝ) ≤ ((K : ℝ) / Real.log 2) * Real.log ((m : ℝ) + 1) := by
  have hlogK : Real.log (K : ℝ) ≤ (K : ℝ) := by
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
    exact (Real.log_le_sub_one_of_pos hKreal).trans (by linarith)
  have hlog : Real.log 2 ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · simp only [Set.mem_Ioi]
      positivity
    · exact_mod_cast (show 2 ≤ m + 1 by omega)
  calc
    Real.log (K : ℝ) ≤ (K : ℝ) := hlogK
    _ = ((K : ℝ) / Real.log 2) * Real.log 2 := by
      field_simp [ne_of_gt (Real.log_pos one_lt_two)]
    _ ≤ ((K : ℝ) / Real.log 2) * Real.log ((m : ℝ) + 1) := by
      gcongr

private theorem demand25_label_ratio_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (hN : ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
      (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .X))).card ≠ 0) :
    (Fintype.card (stagePopulationAt 0 p d b m r).Label : ℝ) /
        ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
          (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .X))).card ≤
      Real.exp ((b*m : ℕ) * demand25XRate p d r +
        ((demand25ValidPower (b := b) p + demand25CoarsePower (b := b) p : ℕ) : ℝ) *
          Real.log ((m : ℝ) + 1)) := by
  apply demand25_ratio_le hN
  exact (demand25_label_card_le40 p d hb r (d.perm r .X)).trans
    (mul_le_mul_of_nonneg_left (demand25_allFactor_bound p d m hb r)
      (Nat.cast_nonneg _))

private theorem demand25_target_ratio_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (W : Fin 2)
    (hN : ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
      (fun J => (stagePopulationAt 0 p d b m r).coarse J (Parent25.side d r W))).card ≠ 0) :
    ((stagePopulationAt 0 p d b m r).target.card : ℝ) /
        ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
          (fun J => (stagePopulationAt 0 p d b m r).coarse J (Parent25.side d r W))).card ≤
      Real.exp ((b*m : ℕ) *
          (if W = 0 then demand25YBaseRate p d r else demand25ZBaseRate p d r) +
        (demand25CoarsePower (b := b) p : ℝ) * Real.log ((m : ℝ) + 1)) := by
  apply demand25_ratio_le hN
  exact (demand25_target_card_le40 p d hb r (Parent25.side d r W)).trans
    (mul_le_mul_of_nonneg_left (demand25_targetAllFactor_bound p d m hb r W)
      (Nat.cast_nonneg _))

private def demand25CoreExponent {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (ε : ℚ) (m : ℕ) (r : Fin 6) : ℝ :=
  (demandExponent p d r + delta ε) * (b*m : ℝ) + ell ε m +
    ((demand25ValidPower (b := b) p + demand25CoarsePower (b := b) p + 2 : ℕ) : ℝ) *
      Real.log ((m : ℝ) + 1)

private theorem demand25_hole_bound {w s b : ℕ} (p : ConstituentInput w s) (m : ℕ) :
    ((cLength p b m)^2 : ℕ) ≤
      ((constituentBaseTotal p * b + 1)^2) * (m+1)^2 := by
  unfold cLength
  calc
    (constituentBaseTotal p * (b * m)) ^ 2 =
        ((constituentBaseTotal p * b) * m) ^ 2 := by simp only [Nat.mul_assoc]
    _ ≤ ((constituentBaseTotal p * b + 1) * (m + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) 2
    _ = (constituentBaseTotal p * b + 1) ^ 2 * (m + 1) ^ 2 := by rw [mul_pow]

private theorem demand25_x_ceil_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hdelta : VanishesWithTolerance delta) (hell : Loss (fun m => b*m) ell)
    (ε : ℚ) (r : Fin 6) :
    let P := stagePopulationAt 0 p d b m r
    let NX := ((Finset.univ : Finset P.Label).image
      (fun J => P.coarse J (d.perm r .X))).card
    (if NX = 0 then 0 else Nat.ceil (8*(Fintype.card P.Label : ℝ)/NX) : ℝ) ≤
      8 * Real.exp (demand25CoreExponent (b := b) p d delta ell ε m r) + 1 := by
  classical
  dsimp only
  let NX := ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
    (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .X))).card
  by_cases hNX : NX = 0
  · simp only [NX, hNX, if_pos, Nat.cast_zero]
    nlinarith [Real.exp_pos (demand25CoreExponent (b := b) p d delta ell ε m r)]
  · simp only [NX, hNX, ↓reduceIte]
    apply demand25_ceil_le (by positivity)
    calc
      8 * (Fintype.card (stagePopulationAt 0 p d b m r).Label : ℝ) / (NX : ℝ) =
          8 * ((Fintype.card (stagePopulationAt 0 p d b m r).Label : ℝ) / NX) := by ring
      _ ≤ 8 * Real.exp ((b*m : ℕ) * demand25XRate p d r +
          ((demand25ValidPower (b := b) p + demand25CoarsePower (b := b) p : ℕ) : ℝ) *
            Real.log ((m : ℝ) + 1)) := by
        gcongr
        exact demand25_label_ratio_bound p d m hb r hNX
      _ ≤ 8 * Real.exp (demand25CoreExponent (b := b) p d delta ell ε m r) := by
        gcongr 1
        apply Real.exp_le_exp.mpr
        have hr := mul_le_mul_of_nonneg_right (demand25_rate_le_exponent_x p d r)
          (Nat.cast_nonneg (b*m))
        have hd := mul_nonneg (hdelta.1 ε) (Nat.cast_nonneg (b*m))
        have he := hell.1 ε m
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hl : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
        unfold demand25CoreExponent
        push_cast at hr hd ⊢
        nlinarith

private theorem demand25_mul3_exp_bound {H K R P T U V E : ℝ}
    (hH0 : 0 ≤ H) (hK0 : 0 ≤ K) (hR0 : 0 ≤ R) (hP0 : 0 ≤ P)
    (hH : H ≤ K * Real.exp T) (hR : R ≤ Real.exp U)
    (hP : P ≤ Real.exp V) (hE : T + U + V ≤ E) :
    H * R * P ≤ K * Real.exp E := by
  calc
    H * R * P ≤ (K * Real.exp T) * Real.exp U * Real.exp V := by gcongr
    _ = K * Real.exp (T + U + V) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ K * Real.exp E := by gcongr

set_option maxHeartbeats 1000000 in
-- The type contains the full dependent stage population and needs extra normalization budget.
private theorem demand25_target_ceil_bound {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hdelta : VanishesWithTolerance delta) (hell : Loss (fun m => b*m) ell)
    (ε : ℚ) (r : Fin 6) (W : Fin 2)
    (hpcomp : Parent25.pcompMax p d b ε m r W ≤
      Real.exp ((demandCompatRate p d r W + delta ε) * (b*m : ℝ) + ell ε m)) :
    let P := stagePopulationAt 0 p d b m r
    let NW := ((Finset.univ : Finset P.Label).image
      (fun J => P.coarse J (Parent25.side d r W))).card
    (if NW = 0 then 0 else Nat.ceil
      (((cLength p b m)^2 : ℕ) * (P.target.card : ℝ) *
        Parent25.pcompMax p d b ε m r W / NW) : ℝ) ≤
      (((constituentBaseTotal p * b + 1)^2 : ℕ) : ℝ) *
        Real.exp (demand25CoreExponent (b := b) p d delta ell ε m r) + 1 := by
  classical
  dsimp only
  let NW := ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
    (fun J => (stagePopulationAt 0 p d b m r).coarse J (Parent25.side d r W))).card
  by_cases hNW : NW = 0
  · simp only [NW, hNW, if_pos, Nat.cast_zero]
    nlinarith [Real.exp_pos (demand25CoreExponent (b := b) p d delta ell ε m r)]
  · simp only [NW, hNW, ↓reduceIte]
    have hpnonneg := demand25_parent_pcompMax_nonneg (b := b) p d ε m r W
    have hrawnonneg : 0 ≤ (((cLength p b m)^2 : ℕ) : ℝ) *
        ((stagePopulationAt 0 p d b m r).target.card : ℝ) *
          Parent25.pcompMax p d b ε m r W / (NW : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hpnonneg)
        (Nat.cast_nonneg _)
    apply demand25_ceil_le hrawnonneg
    have hratio := demand25_target_ratio_bound p d m hb r W hNW
    have hhole : (((cLength p b m)^2 : ℕ) : ℝ) ≤
        (((constituentBaseTotal p * b + 1)^2 : ℕ) : ℝ) *
          (((m+1)^2 : ℕ) : ℝ) := by
      norm_cast
      exact demand25_hole_bound (b := b) p m
    have hmexp : (((m+1)^2 : ℕ) : ℝ) =
        Real.exp (2 * Real.log ((m : ℝ) + 1)) := by
      push_cast
      rw [show (2 : ℝ) * Real.log ((m : ℝ) + 1) =
          Real.log ((m : ℝ) + 1) + Real.log ((m : ℝ) + 1) by ring,
        Real.exp_add, Real.exp_log (by positivity : 0 < (m : ℝ) + 1)]
      ring
    have hrate :
        (if W = 0 then demand25YBaseRate p d r else demand25ZBaseRate p d r) +
            demandCompatRate p d r W ≤ demandExponent p d r := by
      fin_cases W
      · change demand25YBaseRate p d r + demandCompatRate p d r 0 ≤ _
        rw [demand25_compat_y]
        exact demand25_rate_le_exponent_y p d r
      · change demand25ZBaseRate p d r + demandCompatRate p d r 1 ≤ _
        rw [demand25_compat_z]
        exact demand25_rate_le_exponent_z p d r
    rw [show (((cLength p b m)^2 : ℕ) : ℝ) *
          ((stagePopulationAt 0 p d b m r).target.card : ℝ) *
          Parent25.pcompMax p d b ε m r W / (NW : ℝ) =
        (((cLength p b m)^2 : ℕ) : ℝ) *
          (((stagePopulationAt 0 p d b m r).target.card : ℝ) / NW) *
          Parent25.pcompMax p d b ε m r W by ring]
    apply demand25_mul3_exp_bound
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact hpnonneg
    · rwa [← hmexp]
    · exact hratio
    · exact hpcomp
    · have hr := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg (b*m))
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hl : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
      unfold demand25CoreExponent
      push_cast at hr ⊢
      nlinarith

private theorem demand25_max_four_bound (floor x y z A : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hx : (x : ℝ) ≤ 8 * Real.exp E + 1)
    (hy : (y : ℝ) ≤ (A : ℝ) * Real.exp E + 1)
    (hz : (z : ℝ) ≤ (A : ℝ) * Real.exp E + 1) :
    (max floor (max x (max y z)) : ℝ) ≤
      ((floor + 11 + 2*A : ℕ) : ℝ) * Real.exp E := by
  have hmax : max floor (max x (max y z)) ≤ floor + x + y + z := by omega
  have hmaxR : (max floor (max x (max y z)) : ℝ) ≤
      (floor : ℝ) + x + y + z := by exact_mod_cast hmax
  have hexp : 1 ≤ Real.exp E := (Real.one_le_exp_iff).2 hE
  have hconst : (floor : ℝ) + 3 ≤ ((floor : ℝ) + 3) * Real.exp E := by
    nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (floor : ℝ) + 3)]
  calc
    (max floor (max x (max y z)) : ℝ) ≤ (floor : ℝ) + x + y + z := hmaxR
    _ ≤ (floor : ℝ) + (8 * Real.exp E + 1) +
        ((A : ℝ) * Real.exp E + 1) + ((A : ℝ) * Real.exp E + 1) := by linarith
    _ ≤ ((floor : ℝ) + 11 + 2*(A : ℝ)) * Real.exp E := by nlinarith
    _ = ((floor + 11 + 2*A : ℕ) : ℝ) * Real.exp E := by push_cast; ring

set_option maxHeartbeats 1000000 in
-- Relating the expanded raw demand to its three exact population counts is normalization-heavy.
private theorem demand25_stage_bound {w s b : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (floor : ℕ) (hfloor : 2*(w+w)+3 ≤ floor)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hdelta : VanishesWithTolerance delta) (hell : Loss (fun m => b*m) ell)
    (ε : ℚ) (r : Fin 6)
    (hpY : Parent25.pcompMax p d b ε m r 0 ≤
      Real.exp ((demandCompatRate p d r 0 + delta ε) * (b*m : ℝ) + ell ε m))
    (hpZ : Parent25.pcompMax p d b ε m r 1 ≤
      Real.exp ((demandCompatRate p d r 1 + delta ε) * (b*m : ℝ) + ell ε m)) :
    (stageDemand25 p d b floor ε m r : ℝ) ≤
      ((floor + 11 + 2*((constituentBaseTotal p * b + 1)^2) : ℕ) : ℝ) *
        Real.exp (demand25CoreExponent (b := b) p d delta ell ε m r) := by
  classical
  have hE : 0 ≤ demand25CoreExponent (b := b) p d delta ell ε m r := by
    have hdemand := demand25_exponent_nonneg p d r
    have hdelta0 := hdelta.1 ε
    have hell0 := hell.1 ε m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlog : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
    unfold demand25CoreExponent
    positivity
  have hx := demand25_x_ceil_bound p d m hb delta ell hdelta hell ε r
  have hy := demand25_target_ceil_bound p d m hb delta ell hdelta hell ε r 0 hpY
  have hz := demand25_target_ceil_bound p d m hb delta ell hdelta hell ε r 1 hpZ
  unfold stageDemand25
  dsimp only
  unfold natural_demand
  rw [max_eq_left hfloor]
  simpa only [Nat.cast_max, Parent25.side, if_pos rfl,
    if_neg (show (1 : Fin 2) ≠ 0 by decide +kernel)] using
    demand25_max_four_bound floor
      (if ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
          (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .X))).card = 0
        then 0 else Nat.ceil (8*(Fintype.card (stagePopulationAt 0 p d b m r).Label : ℝ) /
          ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
            (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .X))).card))
      (if ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
          (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .Y))).card = 0
        then 0 else Nat.ceil (((cLength p b m)^2 : ℕ) *
          ((stagePopulationAt 0 p d b m r).target.card : ℝ) *
            Parent25.pcompMax p d b ε m r 0 /
          ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
            (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .Y))).card))
      (if ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
          (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .Z))).card = 0
        then 0 else Nat.ceil (((cLength p b m)^2 : ℕ) *
          ((stagePopulationAt 0 p d b m r).target.card : ℝ) *
            Parent25.pcompMax p d b ε m r 1 /
          ((Finset.univ : Finset (stagePopulationAt 0 p d b m r).Label).image
            (fun J => (stagePopulationAt 0 p d b m r).coarse J (d.perm r .Z))).card))
      ((constituentBaseTotal p * b + 1)^2)
      (demand25CoreExponent (b := b) p d delta ell ε m r) hE
      (by simpa only [Nat.cast_ite, Nat.cast_zero] using hx)
      (by simpa only [Nat.cast_ite, Nat.cast_zero] using hy)
      (by simpa only [Nat.cast_ite, Nat.cast_zero] using hz)

noncomputable def constituentDemandLogLoss40 {w s : ℕ} (p : ConstituentInput w s)
    (b floor m : ℕ) : ℝ :=
  constituentPCompLoss40 p b m +
    (((demand25ValidPower (b := b) p + demand25CoarsePower (b := b) p + 2 : ℕ) : ℝ) +
      ((floor + 11 + 2*((constituentBaseTotal p * b + 1)^2) : ℕ) : ℝ) / Real.log 2) *
        Real.log ((m : ℝ) + 1)

/-- A grid-free polynomial cap: every parameter in it is fixed before the empirical grid. -/
noncomputable def constituentDemandCap40 {w s : ℕ} (p : ConstituentInput w s)
    (b floor m : ℕ) : ℝ := Real.exp (constituentDemandLogLoss40 p b floor m)

set_option maxHeartbeats 1000000 in
-- The expanded finite demand algebra needs a local normalization budget.
/-- The one-scale Parent25 natural-demand bound under empirical-grid integrality.
The continuity modulus is chosen from `p` before the changing specification. -/
theorem constituent_grid_demand_upper40 {w s : ℕ} (p : ConstituentInput w s) :
  ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
    ∀ {b m : ℕ} (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
      (hb : ConstituentIntegral36 d b m) (floor : ℕ) (hfloor : 2*(w+w)+3 ≤ floor)
      (ε : ℚ), 0 < ε → 0 < m → ∀ r : Fin 6,
        Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
          (demandExponent p d r + delta ε) * (b*m : ℝ) +
            constituentDemandLogLoss40 p b floor m := by
  obtain ⟨delta, hdelta, hpcomp⟩ := constituent_pcomp_bound_parent40 p
  refine ⟨delta, hdelta, ?_⟩
  intro b m d hd hb floor hfloor ε hε hmpos r
  let ell : ℚ → ℕ → ℝ := fun _ n => constituentPCompLoss40 p b n
  have hpower : (0 : ℝ) ≤ constituentPCompPower40 p b := Nat.cast_nonneg _
  have hell : Loss (fun n => b*n) ell := by
    simpa only [ell, constituentPCompLoss40] using
      log_succ_loss b hb.bpos (constituentPCompPower40 p b) hpower
  have hpY := hpcomp d hd hb ε hε hmpos r 0
  have hpZ := hpcomp d hd hb ε hε hmpos r 1
  let K : ℕ := floor + 11 + 2*((constituentBaseTotal p * b + 1)^2)
  have hK : 0 < K := by dsimp only [K]; omega
  have hm1 : 1 ≤ m := hmpos
  have hstage := demand25_stage_bound p d m hb floor hfloor delta ell hdelta hell
    ε r hpY hpZ
  have hstageNat : floor ≤ stageDemand25 p d b floor ε m r := by
    unfold stageDemand25 natural_demand
    dsimp only
    exact (le_max_left floor (2*(w+w)+3)).trans (le_max_left _ _)
  have hfloorpos : 0 < floor := by omega
  have hstagepos : (0 : ℝ) < (stageDemand25 p d b floor ε m r : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hfloorpos hstageNat
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
      Real.log (K : ℝ) + demand25CoreExponent (b := b) p d delta ell ε m r := by
    calc
      Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
          Real.log ((K : ℝ) *
            Real.exp (demand25CoreExponent (b := b) p d delta ell ε m r)) :=
        Real.strictMonoOn_log.monotoneOn hstagepos
          (mul_pos hKreal (Real.exp_pos _)) hstage
      _ = Real.log (K : ℝ) + demand25CoreExponent (b := b) p d delta ell ε m r := by
        rw [Real.log_mul (ne_of_gt hKreal) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hlogK := demand25_log_nat_le_scaled_log_succ K m hK hm1
  calc
    Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
        Real.log (K : ℝ) + demand25CoreExponent (b := b) p d delta ell ε m r := hlog
    _ ≤ (demandExponent p d r + delta ε) * (b*m : ℝ) +
        constituentDemandLogLoss40 p b floor m := by
      dsimp only [demand25CoreExponent, constituentDemandLogLoss40,
        constituentPCompLoss40, constituentPCompPower40, ell, K] at hlogK ⊢
      push_cast at hlogK ⊢
      ring_nf at hlogK ⊢
      linarith

set_option maxHeartbeats 1000000 in
-- Exponentiating the expanded logarithmic cap needs a local normalization budget.
/-- Multiplicative grid-uniform demand cap, in the same finite shape as
`globalDemand_paper_cap27`. -/
theorem constituent_grid_demand_paper_cap40 {w s : ℕ} (p : ConstituentInput w s) :
  ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
    ∀ {b m : ℕ} (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
      (hb : ConstituentIntegral36 d b m) (floor : ℕ) (hfloor : 2*(w+w)+3 ≤ floor)
      (ε : ℚ), 0 < ε → 0 < m → ∀ r : Fin 6,
        (stageDemand25 p d b floor ε m r : ℝ) ≤
          constituentDemandCap40 p b floor m *
            Real.exp ((demandExponent p d r + delta ε) * (b*m : ℝ)) := by
  obtain ⟨delta, hdelta, hlog⟩ := constituent_grid_demand_upper40 p
  refine ⟨delta, hdelta, ?_⟩
  intro b m d hd hb floor hfloor ε hε hm r
  have hlog' := hlog d hd hb floor hfloor ε hε hm r
  have hfloorpos : 0 < floor := by omega
  have hstageNat : floor ≤ stageDemand25 p d b floor ε m r := by
    unfold stageDemand25 natural_demand
    dsimp only
    exact (le_max_left floor (2*(w+w)+3)).trans (le_max_left _ _)
  have hstagepos : (0 : ℝ) < (stageDemand25 p d b floor ε m r : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hfloorpos hstageNat
  calc
    (stageDemand25 p d b floor ε m r : ℝ) =
        Real.exp (Real.log (stageDemand25 p d b floor ε m r : ℝ)) :=
      (Real.exp_log hstagepos).symm
    _ ≤ Real.exp ((demandExponent p d r + delta ε) * (b*m : ℝ) +
        constituentDemandLogLoss40 p b floor m) := Real.exp_le_exp.mpr hlog'
    _ = constituentDemandCap40 p b floor m *
        Real.exp ((demandExponent p d r + delta ε) * (b*m : ℝ)) := by
      rw [Real.exp_add]
      unfold constituentDemandCap40
      ring

set_option maxHeartbeats 1000000 in
-- The expanded finite demand algebra needs a local normalization budget.
/-- The logarithmic demand cap with the canonical pre-grid modulus exposed. -/
theorem constituent_grid_demand_upper40_at_delta {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (floor : ℕ) (hfloor : 2 * (w + w) + 3 ≤ floor)
    (ε : ℚ) (hε : 0 < ε) (hmpos : 0 < m) (r : Fin 6) :
    Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
      (demandExponent p d r + constituentPCompDelta40 p ε) * (b * m : ℝ) +
        constituentDemandLogLoss40 p b floor m := by
  let ell : ℚ → ℕ → ℝ := fun _ n => constituentPCompLoss40 p b n
  have hpower : (0 : ℝ) ≤ constituentPCompPower40 p b := Nat.cast_nonneg _
  have hell : Loss (fun n => b * n) ell := by
    simpa only [ell, constituentPCompLoss40] using
      log_succ_loss b hb.bpos (constituentPCompPower40 p b) hpower
  have hpY := constituent_pcomp_bound_parent40_at_delta p d hd hb ε hε hmpos r 0
  have hpZ := constituent_pcomp_bound_parent40_at_delta p d hd hb ε hε hmpos r 1
  let K : ℕ := floor + 11 + 2 * ((constituentBaseTotal p * b + 1) ^ 2)
  have hK : 0 < K := by dsimp only [K]; omega
  have hm1 : 1 ≤ m := hmpos
  have hstage := demand25_stage_bound p d m hb floor hfloor
    (constituentPCompDelta40 p) ell (constituentPCompDelta40_vanishes p) hell
    ε r hpY hpZ
  have hstageNat : floor ≤ stageDemand25 p d b floor ε m r := by
    unfold stageDemand25 natural_demand
    dsimp only
    exact (le_max_left floor (2 * (w + w) + 3)).trans (le_max_left _ _)
  have hfloorpos : 0 < floor := by omega
  have hstagepos : (0 : ℝ) < (stageDemand25 p d b floor ε m r : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hfloorpos hstageNat
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
      Real.log (K : ℝ) + demand25CoreExponent (b := b) p d
        (constituentPCompDelta40 p) ell ε m r := by
    calc
      Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
          Real.log ((K : ℝ) * Real.exp (demand25CoreExponent (b := b) p d
            (constituentPCompDelta40 p) ell ε m r)) :=
        Real.strictMonoOn_log.monotoneOn hstagepos
          (mul_pos hKreal (Real.exp_pos _)) hstage
      _ = Real.log (K : ℝ) + demand25CoreExponent (b := b) p d
          (constituentPCompDelta40 p) ell ε m r := by
        rw [Real.log_mul (ne_of_gt hKreal) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hlogK := demand25_log_nat_le_scaled_log_succ K m hK hm1
  calc
    Real.log (stageDemand25 p d b floor ε m r : ℝ) ≤
        Real.log (K : ℝ) + demand25CoreExponent (b := b) p d
          (constituentPCompDelta40 p) ell ε m r := hlog
    _ ≤ (demandExponent p d r + constituentPCompDelta40 p ε) * (b * m : ℝ) +
        constituentDemandLogLoss40 p b floor m := by
      dsimp only [demand25CoreExponent, constituentDemandLogLoss40,
        constituentPCompLoss40, constituentPCompPower40, ell, K] at hlogK ⊢
      push_cast at hlogK ⊢
      ring_nf at hlogK ⊢
      linarith

/-- The multiplicative demand cap with its canonical pre-grid modulus exposed. -/
theorem constituent_grid_demand_paper_cap40_at_delta {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : ConstituentIntegral36 d b m)
    (floor : ℕ) (hfloor : 2 * (w + w) + 3 ≤ floor)
    (ε : ℚ) (hε : 0 < ε) (hm : 0 < m) (r : Fin 6) :
    (stageDemand25 p d b floor ε m r : ℝ) ≤
      constituentDemandCap40 p b floor m *
        Real.exp ((demandExponent p d r + constituentPCompDelta40 p ε) *
          (b * m : ℝ)) := by
  have hlog' := constituent_grid_demand_upper40_at_delta
    p d hd hb floor hfloor ε hε hm r
  have hfloorpos : 0 < floor := by omega
  have hstageNat : floor ≤ stageDemand25 p d b floor ε m r := by
    unfold stageDemand25 natural_demand
    dsimp only
    exact (le_max_left floor (2 * (w + w) + 3)).trans (le_max_left _ _)
  have hstagepos : (0 : ℝ) < (stageDemand25 p d b floor ε m r : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hfloorpos hstageNat
  calc
    (stageDemand25 p d b floor ε m r : ℝ) =
        Real.exp (Real.log (stageDemand25 p d b floor ε m r : ℝ)) :=
      (Real.exp_log hstagepos).symm
    _ ≤ Real.exp ((demandExponent p d r + constituentPCompDelta40 p ε) *
        (b * m : ℝ) + constituentDemandLogLoss40 p b floor m) :=
      Real.exp_le_exp.mpr hlog'
    _ = constituentDemandCap40 p b floor m *
        Real.exp ((demandExponent p d r + constituentPCompDelta40 p ε) *
          (b * m : ℝ)) := by
      rw [Real.exp_add]
      unfold constituentDemandCap40
      ring

end
end OmegaBound.ADVXXZGeneral
end
