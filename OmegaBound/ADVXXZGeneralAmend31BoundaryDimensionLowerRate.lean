import OmegaBound.ADVXXZGeneralAmend31BoundaryDimensionPos
import OmegaBound.ADVXXZGeneralCounts

set_option autoImplicit false
set_option maxRecDepth 10000

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Asymptotics

private theorem rat_floor_toNat_nat31_rate (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem boundary_mass_floor_eq31 (b m : ℕ) (a : ℚ × AtomKey)
    (hI : BoundaryInventoryAdmissible [a] b) :
    ∃ K : ℕ, (b : ℚ) * a.1 = K ∧
      (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = K*m := by
  have ha := hI a (by simp)
  rcases ha.2.2.2.2.2.2.1 with ⟨K, hK⟩
  refine ⟨K, hK, ?_⟩
  have hq : a.1 * (((b*m : ℕ) : ℚ)) = ((K*m : ℕ) : ℚ) := by
    calc
      a.1 * (((b*m : ℕ) : ℚ)) = ((b : ℚ) * a.1) * (m : ℚ) := by
        push_cast
        ring
      _ = (K : ℚ) * (m : ℚ) := by rw [hK]
      _ = ((K*m : ℕ) : ℚ) := by push_cast; rfl
  rw [hq]
  exact rat_floor_toNat_nat31_rate _

private theorem boundary_count_cast31_rate (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) (σ : Chunk a.2.1) :
    (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
  rcases boundary_mass_floor_eq31 b m a hI with ⟨K, hK, hk⟩
  have ha := hI a (by simp)
  rcases ha.2.2.2.2.2.2.2 W σ with ⟨C, hC⟩
  have hcmul : (((K*m : ℕ) : ℚ) * a.2.2.2 W σ) = ((C*m : ℕ) : ℚ) := by
    calc
      ((K*m : ℕ) : ℚ) * a.2.2.2 W σ =
          (m : ℚ) * ((b : ℚ) * a.1 * a.2.2.2 W σ) := by
            push_cast
            rw [hK]
            ring
      _ = (m : ℚ) * (C : ℚ) := by rw [hC]
      _ = ((C*m : ℕ) : ℚ) := by push_cast; ring
  unfold boundaryTypeCounts31
  rw [hk, hcmul, rat_floor_toNat_nat31_rate]

private theorem boundary_type_counts_sum31_rate (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) :
    ∑ σ, boundaryTypeCounts31 a (b*m) W σ =
      (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat := by
  have ha := hI a (by simp)
  have hsum := ha.2.2.1 W
  have hq : ((∑ σ, boundaryTypeCounts31 a (b*m) W σ : ℕ) : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by
    rw [Nat.cast_sum]
    calc
      ∑ σ : Chunk a.2.1, (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
          ∑ σ : Chunk a.2.1,
            ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
        apply Finset.sum_congr rfl
        intro σ _hσ
        exact boundary_count_cast31_rate b m a W hI σ
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) *
          ∑ σ : Chunk a.2.1, a.2.2.2 W σ := by rw [Finset.mul_sum]
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by rw [hsum, mul_one]
  exact_mod_cast hq

private theorem boundary_word_log_lower31 (q b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hq : 0 < q) (hb : 0 < b) (hI : BoundaryInventoryAdmissible [a] b)
    (hactive : boundaryActive31 a W) :
    boundaryRate q [a] W * ((b*m : ℕ) : ℝ) -
        (Fintype.card (Chunk a.2.1) : ℝ) *
          Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) ≤
      Real.log ((boundaryWords31 q a (b*m) (boundaryReadingSide31 W)).card : ℝ) := by
  let V := boundaryReadingSide31 W
  let k := (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat
  let c := boundaryTypeCounts31 a (b*m) V
  have hsumc : ∑ σ, c σ = k := boundary_type_counts_sum31_rate b m a V hI
  by_cases hk : k = 0
  · have hwordpos := boundary_dimension_pos31 q b m [a] W hq hI
    have hcardpos : 1 ≤ (boundaryWords31 q a (b*m) V).card := by
      simpa [boundaryDimension31, hactive, V] using hwordpos
    have hlognonneg : 0 ≤ Real.log ((boundaryWords31 q a (b*m) V).card : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hcardpos)
    have hmzero : m = 0 ∨ a.1 = 0 := by
      rcases boundary_mass_floor_eq31 b m a hI with ⟨K, hK, hkK⟩
      change k = K*m at hkK
      rw [hk] at hkK
      by_cases hm : m = 0
      · exact Or.inl hm
      · have hK0 : K = 0 := (Nat.mul_eq_zero.mp hkK.symm).resolve_right hm
        right
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        rw [hK0, Nat.cast_zero] at hK
        nlinarith [hbq]
    rcases hmzero with hm | ha0
    · subst m
      simpa [V] using hlognonneg
    · have hrate : boundaryRate q [a] W = 0 := by
        simp [boundaryRate, boundaryActive31, hactive, ha0]
      rw [hrate, zero_mul]
      change 0 - (Fintype.card (Chunk a.2.1) : ℝ) * Real.log ((k : ℝ) + 1) ≤
        Real.log ((boundaryWords31 q a (b*m) V).card : ℝ)
      rw [hk]
      norm_num at hlognonneg ⊢
      exact hlognonneg
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have htc := type_class_bounds k c hsumc
    let T := {x : Fin k → Chunk a.2.1 // ∀ σ, typeCnt x σ = c σ}
    obtain ⟨s, hs⟩ := ADVXXZEps.exists_typeCnt_eq c hsumc
    have hTpos : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨⟨s, hs⟩⟩
    have hlogT : (k : ℝ) * entropyNats (fun σ => (c σ : ℝ) / k) -
          (Fintype.card (Chunk a.2.1) : ℝ) * Real.log ((k : ℝ) + 1) ≤
        Real.log (Fintype.card T : ℝ) := by
      have hlog := Real.log_le_log (by positivity) htc.1
      rw [Real.log_div (by positivity) (by positivity), Real.log_exp,
        Real.log_pow] at hlog
      exact hlog
    have hcbeta : ∀ σ, (c σ : ℝ) / (k : ℝ) = (a.2.2.2 V σ : ℚ) := by
      intro σ
      have hc := boundary_count_cast31_rate b m a V hI σ
      change (c σ : ℚ) = (k : ℚ) * a.2.2.2 V σ at hc
      have hcR : (c σ : ℝ) = (k : ℝ) * (a.2.2.2 V σ : ℚ) := by
        exact_mod_cast hc
      rw [hcR]
      field_simp
    have hentropy : entropyNats (fun σ => (c σ : ℝ) / k) =
        entropyNats (fun σ => (a.2.2.2 V σ : ℚ)) := by
      unfold entropyNats
      simp_rw [hcbeta]
    have hones :
        (∑ σ : Chunk a.2.1, c σ *
          (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℕ) =
        (k : ℝ) * ∑ σ : Chunk a.2.1, (a.2.2.2 V σ : ℚ) *
          ((Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℝ) := by
      rw [Nat.cast_sum]
      calc
        ∑ σ : Chunk a.2.1,
            ((c σ * (Finset.univ.filter
              (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℕ) : ℝ) =
            ∑ σ : Chunk a.2.1, (c σ : ℝ) *
              ((Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℝ) := by
                simp only [Nat.cast_mul]
        _ = ∑ σ : Chunk a.2.1, (k : ℝ) * (a.2.2.2 V σ : ℚ) *
              ((Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℝ) := by
                apply Finset.sum_congr rfl
                intro σ _hσ
                have hc := boundary_count_cast31_rate b m a V hI σ
                change (c σ : ℚ) = (k : ℚ) * a.2.2.2 V σ at hc
                exact_mod_cast congrArg (fun z : ℚ => z *
                  (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card) hc
        _ = (k : ℝ) * ∑ σ : Chunk a.2.1, (a.2.2.2 V σ : ℚ) *
              ((Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℝ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro σ _hσ
                ring
    have hmassR : (k : ℝ) = (a.1 : ℝ) * ((b*m : ℕ) : ℝ) := by
      rcases boundary_mass_floor_eq31 b m a hI with ⟨K, hK, hkK⟩
      change k = K*m at hkK
      have hK : (K : ℝ) = (b : ℝ) * (a.1 : ℝ) := by exact_mod_cast hK.symm
      rw [hkK]
      push_cast
      rw [hK]
      ring
    have hrate : boundaryRate q [a] W * ((b*m : ℕ) : ℝ) =
        (k : ℝ) * entropyNats (fun σ => (c σ : ℝ) / k) +
          (∑ σ : Chunk a.2.1, c σ *
            (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℕ) *
            Real.log (q : ℝ) := by
      rw [hentropy, hones, hmassR]
      rcases W with _ | _ | _ <;>
        simp_all [boundaryRate, boundaryActive31, boundaryReadingSide31, V] <;> ring
    rw [boundary_words_card31 q b m a V hI]
    change boundaryRate q [a] W * ((b*m : ℕ) : ℝ) -
        (Fintype.card (Chunk a.2.1) : ℝ) * Real.log ((k : ℝ) + 1) ≤
      Real.log (((Fintype.card T) * q ^
        (∑ σ : Chunk a.2.1, c σ *
          (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card) : ℕ) : ℝ)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hrate' : boundaryRate q [a] W * ((b : ℝ) * (m : ℝ)) =
        (k : ℝ) * entropyNats (fun σ => (c σ : ℝ) / k) +
          (∑ σ : Chunk a.2.1, c σ *
            (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card : ℕ) *
            Real.log (q : ℝ) := by
      simpa only [Nat.cast_mul] using hrate
    rw [hrate']
    linarith

private def boundaryLogLoss31 (I : Inventory) (b m : ℕ) (W : Side) : ℝ :=
  (I.map fun a => if boundaryActive31 a W then
    (Fintype.card (Chunk a.2.1) : ℝ) *
      Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) else 0).sum

private theorem boundary_dimension_log_lower31 (q b m : ℕ) (I : Inventory) (W : Side)
    (hq : 0 < q) (hb : 0 < b) (hI : BoundaryInventoryAdmissible I b) :
    boundaryRate q I W * ((b*m : ℕ) : ℝ) - boundaryLogLoss31 I b m W ≤
      Real.log (boundaryDimension31 q I (b*m) W : ℝ) := by
  induction I with
  | nil => simp [boundaryRate, boundaryLogLoss31, boundaryDimension31]
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have htail : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have htailbound := ih htail
      have htailpos := boundary_dimension_pos31 q b m I W hq htail
      let factor := if boundaryActive31 a W then
        (boundaryWords31 q a (b*m) (boundaryReadingSide31 W)).card else 1
      have hfactorpos : 0 < factor := by
        dsimp only [factor]
        split_ifs with hactive
        · exact Nat.lt_of_lt_of_le Nat.zero_lt_one
            (by
              have h := boundary_dimension_pos31 q b m [a] W hq ha
              simpa [boundaryDimension31, hactive] using h)
        · exact Nat.zero_lt_one
      have hatom : boundaryRate q [a] W * ((b*m : ℕ) : ℝ) -
          (if boundaryActive31 a W then
            (Fintype.card (Chunk a.2.1) : ℝ) *
              Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) else 0) ≤
          Real.log (factor : ℝ) := by
        dsimp only [factor]
        split_ifs with hactive
        · exact boundary_word_log_lower31 q b m a W hq hb ha hactive
        · have hrate0 : boundaryRate q [a] W = 0 := by
            rcases W with _ | _ | _ <;>
              simp_all [boundaryRate, boundaryActive31]
          simp [hrate0]
      have hrate : boundaryRate q (a :: I) W =
          boundaryRate q [a] W + boundaryRate q I W := by
        simp [boundaryRate]
      have hloss : boundaryLogLoss31 (a :: I) b m W =
          (if boundaryActive31 a W then
            (Fintype.card (Chunk a.2.1) : ℝ) *
              Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) else 0) +
            boundaryLogLoss31 I b m W := by
        rfl
      have hdim : boundaryDimension31 q (a :: I) (b*m) W =
          factor * boundaryDimension31 q I (b*m) W := by
        rfl
      rw [hrate, hloss, hdim]
      have hlogprod : Real.log ((factor * boundaryDimension31 q I (b*m) W : ℕ) : ℝ) =
          Real.log (factor : ℝ) + Real.log (boundaryDimension31 q I (b*m) W : ℝ) := by
        rw [show ((factor * boundaryDimension31 q I (b*m) W : ℕ) : ℝ) =
            (factor : ℝ) * (boundaryDimension31 q I (b*m) W : ℝ) by norm_cast]
        rw [Real.log_mul (by exact_mod_cast hfactorpos.ne')
          (by exact_mod_cast (Nat.ne_of_gt htailpos))]
      rw [hlogprod]
      have hatom' : boundaryRate q [a] W * ((b : ℝ) * (m : ℝ)) -
          (if boundaryActive31 a W then
            (Fintype.card (Chunk a.2.1) : ℝ) *
              Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) else 0) ≤
          Real.log (factor : ℝ) := by
        simpa only [Nat.cast_mul] using hatom
      have htailbound' : boundaryRate q I W * ((b : ℝ) * (m : ℝ)) -
          boundaryLogLoss31 I b m W ≤
          Real.log (boundaryDimension31 q I (b*m) W : ℝ) := by
        simpa only [Nat.cast_mul] using htailbound
      linarith

private theorem sublinear_of_isLittleO31 {L : ℕ → ℕ} {f : ℕ → ℝ}
    (h : f =o[Filter.atTop] (fun m => (L m : ℝ))) : Sublinear L f := by
  intro δ hδ
  have heventually := h.bound hδ
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨M, hM⟩ := heventually
  refine ⟨M, fun m hm => ?_⟩
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (L m : ℝ) from Nat.cast_nonneg _)] using hM m hm

private theorem cast_Kmul_succ_isBigO_bmul31 (b K : ℕ) (hb : 0 < b) :
    (fun m : ℕ => ((K*m : ℕ) : ℝ) + 1) =O[Filter.atTop]
      (fun m : ℕ => ((b*m : ℕ) : ℝ)) := by
  apply IsBigO.of_bound (K + 1)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with m hm
  have hb1 : 1 ≤ b := hb
  have hnat : K*m + 1 ≤ (K+1) * (b*m) := by
    have hmle : m ≤ b*m := by
      simpa only [one_mul] using Nat.mul_le_mul_right m hb1
    have hone : 1 ≤ b*m := le_trans hm hmle
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((K*m : ℕ) : ℝ) + 1),
    abs_of_nonneg (Nat.cast_nonneg (b*m))]
  exact_mod_cast hnat

private theorem log_Kmul_succ_isLittleO_bmul31 (b K : ℕ) (hb : 0 < b) :
    (fun m : ℕ => Real.log (((K*m : ℕ) : ℝ) + 1)) =o[Filter.atTop]
      (fun m : ℕ => ((b*m : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using (isLittleO_zero (fun m : ℕ => ((b*m : ℕ) : ℝ)) Filter.atTop)
  · have harg : Filter.Tendsto (fun m : ℕ => ((K*m : ℕ) : ℝ) + 1)
        Filter.atTop Filter.atTop := by
      have hmul := tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < K by
        exact_mod_cast hK)
      have hadd := Filter.tendsto_atTop_add_const_right Filter.atTop 1 hmul
      simpa only [Nat.cast_mul, mul_comm] using hadd
    have hlog : (fun m : ℕ => Real.log (((K*m : ℕ) : ℝ) + 1)) =o[Filter.atTop]
        (fun m : ℕ => ((K*m : ℕ) : ℝ) + 1) := by
      simpa only [Function.comp_apply] using Real.isLittleO_log_id_atTop.comp_tendsto harg
    exact hlog.trans_isBigO (cast_Kmul_succ_isBigO_bmul31 b K hb)

private theorem boundaryLogLoss_isLittleO31 (I : Inventory) (b : ℕ) (W : Side)
    (hb : 0 < b) (hI : BoundaryInventoryAdmissible I b) :
    (fun m => boundaryLogLoss31 I b m W) =o[Filter.atTop]
      (fun m => ((b*m : ℕ) : ℝ)) := by
  induction I with
  | nil => simpa [boundaryLogLoss31] using
      (isLittleO_zero (fun m : ℕ => ((b*m : ℕ) : ℝ)) Filter.atTop)
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have htail : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have htailO := ih htail
      rcases boundary_mass_floor_eq31 b 1 a ha with ⟨K, hK, _hkone⟩
      have hfloor : ∀ m,
          (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = K*m := by
        intro m
        rcases boundary_mass_floor_eq31 b m a ha with ⟨K', hK', hfloor'⟩
        have hKK : K' = K := by
          exact_mod_cast hK'.symm.trans hK
        simpa [hKK] using hfloor'
      have hatom : (fun m => if boundaryActive31 a W then
          (Fintype.card (Chunk a.2.1) : ℝ) *
            Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1) else 0) =o[Filter.atTop]
          (fun m => ((b*m : ℕ) : ℝ)) := by
        split_ifs with hactive
        · have hlog := log_Kmul_succ_isLittleO_bmul31 b K hb
          have heq : (fun m => (Fintype.card (Chunk a.2.1) : ℝ) *
              Real.log (((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) + 1)) =
              fun m => (Fintype.card (Chunk a.2.1) : ℝ) *
                Real.log (((K*m : ℕ) : ℝ) + 1) := by
            funext m
            rw [hfloor m]
          rw [heq]
          exact hlog.const_mul_left _
        · simpa using (isLittleO_zero (fun m : ℕ => ((b*m : ℕ) : ℝ)) Filter.atTop)
      have hadd := hatom.add htailO
      simpa only [boundaryLogLoss31, List.map_cons, List.sum_cons] using hadd

/-- Paper clauses:
`P/prelim.tex:267–278` and `P/constituent.tex:35–39`. -/
theorem boundary_dimension_lowerRate31 (q b : ℕ) (I : Inventory) (W : Side)
    (hq : 0 < q) (hb : 0 < b) (hI : BoundaryInventoryAdmissible I b) :
  LowerRate (fun m => b*m) (fun _ m => boundaryDimension31 q I (b*m) W)
    (boundaryRate q I W) := by
  intro δ hδ
  refine ⟨1, by norm_num, fun ε hε _hεle => ?_⟩
  have hloss := sublinear_of_isLittleO31 (boundaryLogLoss_isLittleO31 I b W hb hI)
  rcases hloss δ hδ with ⟨M, hM⟩
  refine ⟨M, fun m hm => ?_⟩
  constructor
  · exact boundary_dimension_pos31 q b m I W hq hI
  · have hbound := boundary_dimension_log_lower31 q b m I W hq hb hI
    have hloss_nonneg : 0 ≤ boundaryLogLoss31 I b m W := by
      unfold boundaryLogLoss31
      apply List.sum_nonneg
      intro x hx
      rcases List.mem_map.mp hx with ⟨a, _ha, rfl⟩
      split_ifs
      · apply mul_nonneg (Nat.cast_nonneg _)
        apply Real.log_nonneg
        have hn : (0 : ℝ) ≤ ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℝ) :=
          Nat.cast_nonneg _
        linarith
      · rfl
    have hloss_le : boundaryLogLoss31 I b m W ≤ δ * ((b*m : ℕ) : ℝ) := by
      have habs := hM m hm
      rw [abs_of_nonneg hloss_nonneg] at habs
      exact habs
    have hbound' : boundaryRate q I W * ((b : ℝ) * (m : ℝ)) -
        boundaryLogLoss31 I b m W ≤
          Real.log (boundaryDimension31 q I (b*m) W : ℝ) := by
      simpa only [Nat.cast_mul] using hbound
    have hloss_le' : boundaryLogLoss31 I b m W ≤
        δ * ((b : ℝ) * (m : ℝ)) := by
      simpa only [Nat.cast_mul] using hloss_le
    nlinarith

end
end OmegaBound.ADVXXZGeneral
end
