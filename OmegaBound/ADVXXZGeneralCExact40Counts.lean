import OmegaBound.ADVXXZGeneralPQExponentsParent25
import OmegaBound.ADVXXZConstituentPairing
import OmegaBound.ADVXXZGeneralCExact36Defs

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private noncomputable abbrev DemandPop {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : RawPopulation :=
  stagePopulationAt 0 p d b m r

private def demandAlphaCount {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) : ℕ :=
  (((b * m * p.baseN t : ℕ) : ℚ) *
    (d.A t).prob r * (d.alpha t r).prob u).floor.toNat

private def demandParentCount {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (t : Fin s) : ℕ :=
  ∑ u : ChildShape p t, demandAlphaCount p d b m r t u

private abbrev DemandPos {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :=
  (t : Fin s) × (Fin (demandParentCount p d b m r t) × Fin 2)

private def demandFirstWord {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (J : (DemandPop p d b m r).Label)
    (t : Fin s) (i : Fin (demandParentCount p d b m r t)) : ChildShape p t :=
  J.val ⟨t, i, 0⟩

private theorem demandLabel_complementary {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : (DemandPop p d b m r).Label) (t : Fin s)
    (i : Fin (demandParentCount p d b m r t)) :
    J.val ⟨t, i, 1⟩ = complement p t (J.val ⟨t, i, 0⟩) := by
  exact J.property.2 t i

private theorem demandFirstWord_injective {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    Function.Injective (fun J : (DemandPop p d b m r).Label =>
      fun t i => demandFirstWord p d r J t i) := by
  intro J K h
  apply Subtype.ext
  funext z
  rcases z with ⟨t, i, h⟩
  fin_cases h
  · change J.val ⟨t, i, 0⟩ = K.val ⟨t, i, 0⟩
    exact congrFun (congrFun h t) i
  · change J.val ⟨t, i, 1⟩ = K.val ⟨t, i, 1⟩
    rw [demandLabel_complementary p d r J t i,
      demandLabel_complementary p d r K t i]
    exact congrArg (complement p t) (congrFun (congrFun h t) i)

private def demandCoarseWord {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (J : (DemandPop p d b m r).Label) (t : Fin s)
    (i : Fin (demandParentCount p d b m r t)) : Fin (2*w+1) :=
  Parent25.coordFin W (demandFirstWord p d r J t i).val

private theorem demand_cancel_surjective {ι α β : Type*} {f : ι → α}
    {g k : α → β} (h : g ∘ f = k ∘ f) (hf : Function.Surjective f) : g = k :=
  hf.injective_comp_right h

private theorem demandCoarseWord_eq_of_coarse_eq {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (J K : (DemandPop p d b m r).Label)
    (h : (DemandPop p d b m r).coarse J W = (DemandPop p d b m r).coarse K W)
    (t : Fin s) (i : Fin (demandParentCount p d b m r t)) :
    demandCoarseWord p d r W J t i = demandCoarseWord p d r W K t i := by
  dsimp only [DemandPop, stagePopulationAt] at h
  have hraw :
      (fun z : DemandPos p d b m r => Parent25.coordFin W (J.val z).val) =
      (fun z : DemandPos p d b m r => Parent25.coordFin W (K.val z).val) := by
    apply demand_cancel_surjective h
    exact Equiv.surjective _
  exact congrFun hraw ⟨t, i, 0⟩

private theorem demand_floor_nat (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem demand_alphaCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (demandAlphaCount p d b m r t v : ℚ) =
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
  unfold demandAlphaCount
  rw [hscaled, demand_floor_nat]

private theorem demand_alphaCount_cast_real {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (demandAlphaCount p d b m r t v : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
        ((d.alpha t r).prob v : ℝ) := by
  exact_mod_cast demand_alphaCount_cast p d m hb r t v

private theorem demandTargetCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : (DemandPop p d b m r).Label) (hJ : J ∈ (DemandPop p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    typeCnt (demandFirstWord p d r J t) u = demandAlphaCount p d b m r t u := by
  let A : AlphaLabel p d b m r := ⟨J, hJ⟩
  simpa only [typeCnt, demandFirstWord, A, demandParentCount, demandAlphaCount,
    Parent25.parentCount, Parent25.alphaCount] using
    parent25_alphaLabel_target_count p d r A t u

private theorem demandMarginalCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : (DemandPop p d b m r).Label) (t : Fin s) (W : Side)
    (a : Fin (2 * w + 1)) :
    typeCnt (demandCoarseWord p d r W J t) a =
      ∑ u : ChildShape p t,
        if Parent25.coordFin W u.val = a then demandAlphaCount p d b m r t u else 0 := by
  simpa only [DemandPop, stagePopulationAt, Parent25.Pop, Parent25.Pos,
    Parent25.parentCount, Parent25.alphaCount, demandParentCount, demandAlphaCount,
    demandFirstWord,
    typeCnt] using J.property.1 t 0 W a

private def demandTable {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (J : (DemandPop p d b m r).Label)
    (t : Fin s) (u : ChildShape p t) : Fin (demandParentCount p d b m r t + 1) := by
  classical
  refine ⟨typeCnt (demandFirstWord p d r J t) u, ?_⟩
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin (demandParentCount p d b m r t)))
    (fun i => demandFirstWord p d r J t i = u)
  simpa only [typeCnt, Finset.card_univ, Fintype.card_fin, Nat.lt_succ_iff] using h

private abbrev DemandTable {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :=
  (t : Fin s) → ChildShape p t → Fin (demandParentCount p d b m r t + 1)

private def DemandValidTable {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) :=
  {q : DemandTable (b := b) (m := m) p d r //
    ∀ t W a, projectedCount (fun u : ChildShape p t => Parent25.coordFin W u.val)
      (fun u => (q t u).val) a =
        ∑ u : ChildShape p t,
          if Parent25.coordFin W u.val = a then demandAlphaCount p d b m r t u else 0}

private noncomputable instance demandValidTableFintype {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    Fintype (DemandValidTable (b := b) (m := m) p d r) := by
  classical
  unfold DemandValidTable DemandTable
  infer_instance

private theorem demandTable_valid {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (J : (DemandPop p d b m r).Label) :
    ∀ t W a, projectedCount (fun u : ChildShape p t => Parent25.coordFin W u.val)
      (fun u => (demandTable p d r J t u).val) a =
        ∑ u : ChildShape p t,
          if Parent25.coordFin W u.val = a then demandAlphaCount p d b m r t u else 0 := by
  classical
  intro t W a
  let x : {x : Fin (demandParentCount p d b m r t) → ChildShape p t //
      ∀ u, typeCnt x u = (demandTable p d r J t u).val} :=
    ⟨demandFirstWord p d r J t, fun _ => rfl⟩
  let y := projectTypeWord
    (fun u : ChildShape p t => Parent25.coordFin W u.val)
    (fun u => (demandTable p d r J t u).val) x
  rw [← y.property a]
  simpa only [y, projectTypeWord, x] using demandMarginalCount p d r J t W a

private abbrev DemandLabelFiber {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1)) :=
  {J : (DemandPop p d b m r).Label // (DemandPop p d b m r).coarse J W = y}

private abbrev DemandTargetFiber {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1)) :=
  {J : DemandLabelFiber p d r W y // J.val ∈ (DemandPop p d b m r).target}

private noncomputable instance demandTargetFiberFintype {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1)) :
    Fintype (DemandTargetFiber p d r W y) := by
  classical
  unfold DemandTargetFiber DemandLabelFiber
  infer_instance

private abbrev DemandFiberCode {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (K : (DemandPop p d b m r).Label) :=
  (q : DemandValidTable (b := b) (m := m) p d r) × ((t : Fin s) →
    ProjectionFiber (demandParentCount p d b m r t)
      (fun u : ChildShape p t => Parent25.coordFin W u.val)
      (fun u => (q.val t u).val) (demandCoarseWord p d r W K t))

private abbrev DemandTargetCode {w s b m : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (K : (DemandPop p d b m r).Label) :=
  (t : Fin s) → ProjectionFiber (demandParentCount p d b m r t)
    (fun u : ChildShape p t => Parent25.coordFin W u.val)
    (demandAlphaCount p d b m r t) (demandCoarseWord p d r W K t)

private noncomputable def demandFiberCode {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y)
    (J : DemandLabelFiber p d r W y) : DemandFiberCode p d r W K := by
  classical
  refine ⟨⟨demandTable p d r J.val, demandTable_valid p d r J.val⟩,
    fun t => ⟨demandFirstWord p d r J.val t, fun _ => rfl, ?_⟩⟩
  · intro i
    exact demandCoarseWord_eq_of_coarse_eq p d r W J.val K
      (J.property.trans hK.symm) t i

private theorem demandFiberCode_injective {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y) :
    Function.Injective (demandFiberCode p d r W y K hK) := by
  intro J L h
  apply Subtype.ext
  apply demandFirstWord_injective p d r
  have hv := congrArg (fun z : DemandFiberCode p d r W K =>
    fun (t : Fin s) (i : Fin (demandParentCount p d b m r t)) => (z.2 t).val i) h
  exact hv

private noncomputable def demandTargetCode {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y)
    (J : DemandTargetFiber p d r W y) : DemandTargetCode p d r W K := by
  classical
  refine fun t => ⟨demandFirstWord p d r J.val.val t, ?_, ?_⟩
  · exact fun u => demandTargetCount p d r J.val.val J.property t u
  · intro i
    exact demandCoarseWord_eq_of_coarse_eq p d r W J.val.val K
      (J.val.property.trans hK.symm) t i

private theorem demandTargetCode_injective {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y) :
    Function.Injective (demandTargetCode p d r W y K hK) := by
  intro J L h
  apply Subtype.ext
  apply Subtype.ext
  apply demandFirstWord_injective p d r
  exact congrArg (fun z : DemandTargetCode p d r W K => fun t i => (z t).val i) h

private theorem demand_probR_eq_cast_prob {α : Type*} [Fintype α]
    (P : RatDist α) (a : α) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem demand_coordFin_val {w : ℕ} (W : Side) (u : Shape w) :
    (Parent25.coordFin W u).val = coord W u := by
  cases W <;> rfl

private theorem demand_parentCount_cast_real {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (t : Fin s) :
    (demandParentCount p d b m r t : ℝ) =
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) := by
  exact_mod_cast (show (demandParentCount p d b m r t : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r by
    rw [demandParentCount, Nat.cast_sum]
    simp_rw [demand_alphaCount_cast p d m hb r t]
    rw [← Finset.mul_sum, (d.alpha t r).sum_prob, mul_one])

private theorem demand_validTable_normalized {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (q : DemandValidTable (b := b) (m := m) p d r)
    (t : Fin s) (hn : demandParentCount p d b m r t ≠ 0) (W : Side) :
    (fun a => (projectedCount
        (fun u : ChildShape p t => Parent25.coordFin W u.val)
        (fun u => (q.val t u).val) a : ℝ) / demandParentCount p d b m r t) =
      constituentMarginal d.toPaper t r W := by
  funext a
  rw [q.property t W a]
  unfold constituentMarginal
  have hscale := demand_parentCount_cast_real p d m hb r t
  have hscale0 :
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) ≠ 0 := by
    rw [← hscale]
    exact_mod_cast hn
  rw [Nat.cast_sum, hscale, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : Parent25.coordFin W u.val = a
  · have hcoord : coord W u.val = a.val := by
      simpa only [demand_coordFin_val] using congrArg Fin.val hu
    rw [if_pos hu, if_pos hcoord]
    rw [demand_alphaCount_cast_real p d m hb r t]
    simp only [ConstituentSpec.toPaper, demand_probR_eq_cast_prob]
    exact mul_div_cancel_left₀ _ hscale0
  · have hcoord : ¬coord W u.val = a.val := by
      intro h
      apply hu
      apply Fin.ext
      simpa only [demand_coordFin_val] using h
    rw [if_neg hu, if_neg hcoord]
    norm_num

private theorem demand_table_isProbability {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (q : DemandValidTable (b := b) (m := m) p d r) (t : Fin s)
    (hn : demandParentCount p d b m r t ≠ 0)
    (hk : ∑ u, (q.val t u).val = demandParentCount p d b m r t) :
    IsProbability (fun u => ((q.val t u).val : ℝ) /
      demandParentCount p d b m r t) := by
  constructor
  · intro u
    positivity
  · rw [← Finset.sum_div, ← Nat.cast_sum, hk]
    field_simp

private theorem demand_table_sameMarginals {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (q : DemandValidTable (b := b) (m := m) p d r)
    (t : Fin s) (hn : demandParentCount p d b m r t ≠ 0) :
    SameConstituentMarginals t (d.toPaper.alpha t r)
      (fun u => ((q.val t u).val : ℝ) / demandParentCount p d b m r t) := by
  intro W x
  have halpha : ∀ u, d.toPaper.alpha t r u = ((d.alpha t r).prob u : ℝ) := by
    intro u
    simp only [ConstituentSpec.toPaper, demand_probR_eq_cast_prob]
  simp_rw [halpha]
  by_cases hx : x < 2 * w + 1
  · let a : Fin (2 * w + 1) := ⟨x, hx⟩
    have h := congrFun (demand_validTable_normalized p d hb r q t hn W) a
    unfold constituentMarginal projectedCount at h
    rw [Nat.cast_sum] at h
    simp only [ConstituentSpec.toPaper, demand_probR_eq_cast_prob,
      demand_coordFin_val] at h
    have hfilter :
        (Finset.univ.filter fun u : ChildShape p t => Parent25.coordFin W u.val = a) =
          Finset.univ.filter fun u : ChildShape p t => coord W u.val = x := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
      constructor
      · intro hu
        simpa only [demand_coordFin_val] using congrArg Fin.val hu
      · intro hu
        apply Fin.ext
        simpa only [demand_coordFin_val] using hu
    calc
      (∑ u, if coord W u.val = x then ((d.alpha t r).prob u : ℝ) else 0) =
          ((∑ u ∈ Finset.univ.filter (fun u : ChildShape p t => coord W u.val = x),
            ((q.val t u).val : ℝ)) / demandParentCount p d b m r t) := by
        rw [← hfilter]
        simpa only [a] using h.symm
      _ = ∑ u ∈ Finset.univ.filter (fun u : ChildShape p t => coord W u.val = x),
          ((q.val t u).val : ℝ) / demandParentCount p d b m r t :=
        by rw [Finset.sum_div]
      _ = ∑ u, if coord W u.val = x then
          ((q.val t u).val : ℝ) / demandParentCount p d b m r t else 0 := by
        rw [Finset.sum_filter]
  · apply Finset.sum_congr rfl
    intro u _
    have hcoord : ¬coord W u.val = x := by
      intro h
      apply hx
      rw [← h]
      simpa only [demand_coordFin_val] using (Parent25.coordFin W u.val).isLt
    rw [if_neg hcoord, if_neg hcoord]

private theorem demand_entropy_le_penalty {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (q : DemandValidTable (b := b) (m := m) p d r)
    (t : Fin s) (hn : demandParentCount p d b m r t ≠ 0)
    (hk : ∑ u, (q.val t u).val = demandParentCount p d b m r t) :
    entropyNats (fun u => ((q.val t u).val : ℝ) /
        demandParentCount p d b m r t) ≤
      Real.log 2 * (entropy (d.toPaper.alpha t r) +
        constituentPenalty d.toPaper t r) := by
  let rho := fun u => ((q.val t u).val : ℝ) / demandParentCount p d b m r t
  have hrho := demand_table_isProbability p d r q t hn hk
  have hsame := demand_table_sameMarginals p d hb r q t hn
  have hnonempty : Nonempty (ChildShape p t) := by
    by_contra hempty
    letI : IsEmpty (ChildShape p t) := not_nonempty_iff.mp hempty
    have : demandParentCount p d b m r t = 0 := by simpa using hk.symm
    exact hn this
  letI : Nonempty (ChildShape p t) := hnonempty
  let S : Set ℝ := {h : ℝ | ∃ a' : ChildShape p t → ℝ,
    IsProbability a' ∧ SameConstituentMarginals t (d.toPaper.alpha t r) a' ∧
      h = entropy a'}
  have hmem : entropy rho ∈ S := ⟨rho, hrho, hsame, rfl⟩
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
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
    rw [entropyNats_eq_log_two_mul_entropy] at hHn
    rw [mul_comm] at hHn
    exact (le_div_iff₀ hlog).2 hHn
  have hs : entropy rho ≤ sSup S := le_csSup hbdd hmem
  rw [entropyNats_eq_log_two_mul_entropy]
  apply mul_le_mul_of_nonneg_left _ hlog.le
  calc
    entropy rho ≤ sSup S := hs
    _ = entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r := by
      unfold constituentPenalty
      change sSup S = _
      ring

private noncomputable def demandParentFactor {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (t : Fin s) : ℝ :=
  Real.exp (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
    (Real.log 2 * (entropy (d.toPaper.alpha t r) +
      constituentPenalty d.toPaper t r - entropy (constituentMarginal d.toPaper t r W)))) *
    ((demandParentCount p d b m r t : ℝ) + 1) ^ Fintype.card (Fin (2*w+1))

set_option maxHeartbeats 1000000 in
-- The dependent projection-fibre type requires extra reduction through `stagePopulationAt`.
private theorem demand_projectionFiber_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) (q : DemandValidTable (b := b) (m := m) p d r)
    (K : (DemandPop p d b m r).Label) (t : Fin s) :
    (Fintype.card (ProjectionFiber (demandParentCount p d b m r t)
      (fun u : ChildShape p t => Parent25.coordFin W u.val)
      (fun u => (q.val t u).val) (demandCoarseWord p d r W K t)) : ℝ) ≤
      demandParentFactor (b := b) (m := m) p d r W t := by
  classical
  let n := demandParentCount p d b m r t
  let g := fun u : ChildShape p t => Parent25.coordFin W u.val
  let k := fun u : ChildShape p t => (q.val t u).val
  let y := demandCoarseWord p d r W K t
  by_cases hn : n = 0
  · have hcard : Fintype.card (ProjectionFiber n g k y) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro x z
      apply Subtype.ext
      funext i
      exact Fin.elim0 (hn ▸ i)
    have hscale :
        ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) = 0 := by
      rw [← demand_parentCount_cast_real p d m hb r t]
      have hn' : demandParentCount p d b m r t = 0 := by simpa only [n] using hn
      rw [hn']
      norm_num
    unfold demandParentFactor
    simp only [hscale, zero_mul, Real.exp_zero, n, hn, Nat.cast_zero, zero_add,
      one_pow, mul_one]
    exact_mod_cast hcard
  · by_cases hx : Nonempty (ProjectionFiber n g k y)
    · let x := Classical.choice hx
      have hk : ∑ u, k u = n := by
        calc
          ∑ u, k u = ∑ u, typeCnt x.val u := by
            apply Finset.sum_congr rfl
            intro u _
            exact (x.property.1 u).symm
          _ = n := OmegaBound.ADVXXZ.sum_typeCnt x.val
      let yy := projectTypeWord g k ⟨x.val, x.property.1⟩
      have hyy : yy.val = y := by
        funext i
        exact x.property.2 i
      let ys : {z : Fin n → Fin (2*w+1) // ∀ c, typeCnt z c = projectedCount g k c} :=
        ⟨y, fun c => by rw [← hyy]; exact yy.property c⟩
      have hu := projectionFiber_entropy_upper g k hk ys
      have hq := demand_entropy_le_penalty p d hb r q t hn hk
      have hmarg : entropyNats (fun c => (projectedCount g k c : ℝ) / n) =
          Real.log 2 * entropy (constituentMarginal d.toPaper t r W) := by
        rw [demand_validTable_normalized p d hb r q t hn W,
          entropyNats_eq_log_two_mul_entropy]
      have hexponent :
          (n : ℝ) * (entropyNats (fun u => (k u : ℝ) / n) -
            entropyNats (fun c => (projectedCount g k c : ℝ) / n)) ≤
          ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
            (Real.log 2 * (entropy (d.toPaper.alpha t r) +
              constituentPenalty d.toPaper t r -
                entropy (constituentMarginal d.toPaper t r W))) := by
        rw [hmarg, ← demand_parentCount_cast_real p d m hb r t]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        linarith
      unfold demandParentFactor
      dsimp only [n, g, k, y] at hu hexponent ⊢
      exact hu.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
        (by positivity))
    · have hi : IsEmpty (ProjectionFiber n g k y) := not_nonempty_iff.mp hx
      have hc : Fintype.card (ProjectionFiber n g k y) = 0 :=
        Fintype.card_eq_zero_iff.mpr hi
      rw [hc]
      unfold demandParentFactor
      norm_num only [Nat.cast_zero]
      have hbase : 0 ≤ (demandParentCount p d b m r t : ℝ) + 1 :=
        add_nonneg (Nat.cast_nonneg _) zero_le_one
      exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hbase _)

private noncomputable def demandAllFactor {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) : ℝ := ∏ t, demandParentFactor (b := b) (m := m) p d r W t

set_option maxHeartbeats 1000000 in
-- Expanding the dependent sigma/pi cardinalities needs extra reduction.
private theorem demand_fiber_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y) :
    (Fintype.card (DemandLabelFiber p d r W y) : ℝ) ≤
      (Fintype.card (DemandValidTable (b := b) (m := m) p d r) : ℝ) *
        demandAllFactor (b := b) (m := m) p d r W := by
  classical
  have hinj := demandFiberCode_injective p d r W y K hK
  have hcard : Fintype.card (DemandLabelFiber p d r W y) ≤
      Fintype.card (DemandFiberCode p d r W K) := Fintype.card_le_of_injective _ hinj
  have hcast : (Fintype.card (DemandLabelFiber p d r W y) : ℝ) ≤
      (Fintype.card (DemandFiberCode p d r W K) : ℝ) := by exact_mod_cast hcard
  refine hcast.trans ?_
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    (∑ q : DemandValidTable (b := b) (m := m) p d r,
        (Fintype.card ((t : Fin s) → ProjectionFiber
          (demandParentCount p d b m r t)
          (fun u : ChildShape p t => Parent25.coordFin W u.val)
          (fun u => (q.val t u).val) (demandCoarseWord p d r W K t)) : ℕ) : ℝ) ≤
      ∑ _q : DemandValidTable (b := b) (m := m) p d r,
        demandAllFactor (b := b) (m := m) p d r W := by
      apply Finset.sum_le_sum
      intro q _
      rw [Fintype.card_pi, Nat.cast_prod]
      unfold demandAllFactor
      exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun t _ => demand_projectionFiber_card_le p d hb r W q K t)
    _ = (Fintype.card (DemandValidTable (b := b) (m := m) p d r) : ℝ) *
        demandAllFactor (b := b) (m := m) p d r W := by simp

private theorem demand_card_le_image_mul {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (f : α → β) (B : ℝ)
    (h : ∀ y ∈ (Finset.univ.image f),
      ((Finset.univ.filter fun x : α => f x = y).card : ℝ) ≤ B) :
    (Fintype.card α : ℝ) ≤ ((Finset.univ.image f).card : ℝ) * B := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image f, Nat.cast_sum]
  calc
    (∑ y ∈ Finset.univ.image f,
        ((Finset.univ.filter fun x : α => f x = y).card : ℝ)) ≤
        ∑ _y ∈ Finset.univ.image f, B := by
      apply Finset.sum_le_sum
      intro y hy
      exact h y hy
    _ = ((Finset.univ.image f).card : ℝ) * B := by simp

private theorem demand_label_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) :
    (Fintype.card (DemandPop p d b m r).Label : ℝ) ≤
      (((Finset.univ : Finset (DemandPop p d b m r).Label).image
        (fun J => (DemandPop p d b m r).coarse J W)).card : ℝ) *
      ((Fintype.card (DemandValidTable (b := b) (m := m) p d r) : ℝ) *
        demandAllFactor (b := b) (m := m) p d r W) := by
  classical
  apply demand_card_le_image_mul
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨K, -, hK⟩
  have hf := demand_fiber_card_le p d hb r W y K hK
  rw [Fintype.card_subtype] at hf
  simpa only using hf

private theorem demand_alpha_normalized {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (t : Fin s) (hn : demandParentCount p d b m r t ≠ 0) :
    (fun u => (demandAlphaCount p d b m r t u : ℝ) /
      demandParentCount p d b m r t) = d.toPaper.alpha t r := by
  funext u
  rw [demand_alphaCount_cast_real p d m hb r t,
    demand_parentCount_cast_real p d m hb r t]
  have hscale :
      ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) ≠ 0 := by
    rw [← demand_parentCount_cast_real p d m hb r t]
    exact_mod_cast hn
  simp only [ConstituentSpec.toPaper, demand_probR_eq_cast_prob]
  exact mul_div_cancel_left₀ _ hscale

private noncomputable def demandTargetParentFactor {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) (t : Fin s) : ℝ :=
  Real.exp (((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
    (Real.log 2 * (entropy (d.toPaper.alpha t r) -
      entropy (constituentMarginal d.toPaper t r W)))) *
    ((demandParentCount p d b m r t : ℝ) + 1) ^ Fintype.card (Fin (2*w+1))

set_option maxHeartbeats 1000000 in
-- As above, the exact target fibre reduces through the full population constructor.
private theorem demand_targetProjectionFiber_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) (K : (DemandPop p d b m r).Label)
    (hK : K ∈ (DemandPop p d b m r).target) (t : Fin s) :
    (Fintype.card (ProjectionFiber (demandParentCount p d b m r t)
      (fun u : ChildShape p t => Parent25.coordFin W u.val)
      (demandAlphaCount p d b m r t) (demandCoarseWord p d r W K t)) : ℝ) ≤
      demandTargetParentFactor (b := b) (m := m) p d r W t := by
  classical
  let n := demandParentCount p d b m r t
  let g := fun u : ChildShape p t => Parent25.coordFin W u.val
  let k := demandAlphaCount p d b m r t
  let x : ProjectionFiber n g k (demandCoarseWord p d r W K t) :=
    ⟨demandFirstWord p d r K t, demandTargetCount p d r K hK t,
      fun _ => rfl⟩
  have hk : ∑ u, k u = n := by
    calc
      ∑ u, k u = ∑ u, typeCnt x.val u := by
        apply Finset.sum_congr rfl
        intro u _
        exact (x.property.1 u).symm
      _ = n := OmegaBound.ADVXXZ.sum_typeCnt x.val
  let yy := projectTypeWord g k ⟨x.val, x.property.1⟩
  let ys : {z : Fin n → Fin (2*w+1) // ∀ c, typeCnt z c = projectedCount g k c} :=
    ⟨demandCoarseWord p d r W K t, fun c => yy.property c⟩
  by_cases hn : n = 0
  · have hcard : Fintype.card (ProjectionFiber n g k
        (demandCoarseWord p d r W K t)) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro z z'
      apply Subtype.ext
      funext i
      exact Fin.elim0 (hn ▸ i)
    have hscale :
        ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) = 0 := by
      rw [← demand_parentCount_cast_real p d m hb r t]
      simp only [n] at hn
      rw [hn]
      norm_num
    unfold demandTargetParentFactor
    simp only [hscale, zero_mul, Real.exp_zero, n, hn, Nat.cast_zero, zero_add,
      one_pow, mul_one]
    exact_mod_cast hcard
  · let q : DemandValidTable (b := b) (m := m) p d r :=
      ⟨demandTable p d r K, demandTable_valid p d r K⟩
    have hfine : entropyNats (fun u => (k u : ℝ) / n) =
        Real.log 2 * entropy (d.toPaper.alpha t r) := by
      rw [demand_alpha_normalized p d hb r t hn, entropyNats_eq_log_two_mul_entropy]
    have hcoarse : entropyNats (fun c => (projectedCount g k c : ℝ) / n) =
        Real.log 2 * entropy (constituentMarginal d.toPaper t r W) := by
      have hkq : k = fun u => (q.val t u).val := by
        funext u
        exact (demandTargetCount p d r K hK t u).symm
      rw [hkq, demand_validTable_normalized p d hb r q t hn W,
        entropyNats_eq_log_two_mul_entropy]
    have hexponent :
        (n : ℝ) * (entropyNats (fun u => (k u : ℝ) / n) -
          entropyNats (fun c => (projectedCount g k c : ℝ) / n)) =
        ((b * m * p.baseN t : ℕ) : ℝ) * ((d.A t).prob r : ℝ) *
          (Real.log 2 * (entropy (d.toPaper.alpha t r) -
            entropy (constituentMarginal d.toPaper t r W))) := by
      rw [hfine, hcoarse, demand_parentCount_cast_real p d m hb r t]
      ring
    have hu := projectionFiber_entropy_upper g k hk ys
    rw [hexponent] at hu
    simpa only [demandTargetParentFactor, n, g, k] using hu

private noncomputable def demandTargetAllFactor {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (W : Side) : ℝ := ∏ t, demandTargetParentFactor (b := b) (m := m) p d r W t

set_option maxHeartbeats 1000000 in
-- The target code is a dependent product of the exact parent fibres.
private theorem demand_targetFiber_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side)
    (y : Fin (DemandPop p d b m r).n → Fin ((DemandPop p d b m r).grade + 1))
    (K : (DemandPop p d b m r).Label)
    (hK : (DemandPop p d b m r).coarse K W = y)
    (hKt : K ∈ (DemandPop p d b m r).target) :
    (Fintype.card (DemandTargetFiber p d r W y) : ℝ) ≤
      demandTargetAllFactor (b := b) (m := m) p d r W := by
  classical
  have hinj := demandTargetCode_injective p d r W y K hK
  have hcard : Fintype.card (DemandTargetFiber p d r W y) ≤
      Fintype.card (DemandTargetCode p d r W K) := Fintype.card_le_of_injective _ hinj
  have hcast : (Fintype.card (DemandTargetFiber p d r W y) : ℝ) ≤
      (Fintype.card (DemandTargetCode p d r W K) : ℝ) := by exact_mod_cast hcard
  refine hcast.trans ?_
  rw [Fintype.card_pi, Nat.cast_prod]
  unfold demandTargetAllFactor
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun t _ => demand_targetProjectionFiber_card_le p d hb r W K hKt t)

private theorem demand_target_card_le {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Side) :
    ((DemandPop p d b m r).target.card : ℝ) ≤
      (((Finset.univ : Finset (DemandPop p d b m r).Label).image
        (fun J => (DemandPop p d b m r).coarse J W)).card : ℝ) *
      demandTargetAllFactor (b := b) (m := m) p d r W := by
  classical
  let T := {J : (DemandPop p d b m r).Label // J ∈ (DemandPop p d b m r).target}
  let f : T → (Fin (DemandPop p d b m r).n →
      Fin ((DemandPop p d b m r).grade + 1)) := fun J =>
    (DemandPop p d b m r).coarse J.val W
  have hsmall : ((Finset.univ.image f).card : ℝ) ≤
      (((Finset.univ : Finset (DemandPop p d b m r).Label).image
        (fun J => (DemandPop p d b m r).coarse J W)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨J, -, rfl⟩
      exact Finset.mem_image.mpr ⟨J.val, Finset.mem_univ _, rfl⟩)
  have hmain : (Fintype.card T : ℝ) ≤
      ((Finset.univ.image f).card : ℝ) *
        demandTargetAllFactor (b := b) (m := m) p d r W := by
    apply demand_card_le_image_mul
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨K, -, hK⟩
    have hfib := demand_targetFiber_card_le p d hb r W y K.val hK K.property
    let e : {J : T // f J = y} ≃ DemandTargetFiber p d r W y := {
      toFun J := ⟨⟨J.val.val, J.property⟩, J.val.property⟩
      invFun J := ⟨⟨J.val.val, J.property⟩, J.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have he : Fintype.card {J : T // f J = y} =
        Fintype.card (DemandTargetFiber p d r W y) := Fintype.card_congr e
    rw [← he, Fintype.card_subtype] at hfib
    simpa only using hfib
  have hTcard : Fintype.card T = (DemandPop p d b m r).target.card := by
    simp only [T, Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hTcard] at hmain
  refine hmain.trans ?_
  exact mul_le_mul_of_nonneg_right hsmall (by
    unfold demandTargetAllFactor demandTargetParentFactor
    positivity)

end OmegaBound.ADVXXZGeneral
end
