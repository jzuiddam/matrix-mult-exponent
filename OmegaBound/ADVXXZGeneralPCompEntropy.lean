import OmegaBound.ADVXXZGeneralPopulationFiniteAPI
import OmegaBound.ADVXXZGeneralCounts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic glue for the constituent compatibility bound

This module isolates the analytic bookkeeping that follows the finite `P/Q` count in
`constituent.tex:397-439`.  The finite counting argument leaves a fixed power of `m+1`; its
logarithm is `o(b*m)`.  The empirical entropy replacement at `:439` leaves a nonnegative
multiple of the modulus supplied by `entropy_uniform_continuity`.

The fixed-projection `P` lower and `Q` upper estimates below are proved from type classes and
constant fibres.  Their application to the constituent population, which identifies the raw compatibility cells
with the paper's projections, is made downstream (`ADVXXZGeneralCExact40PCompBound`).
-/

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators Topology
namespace OmegaBound.ADVXXZGeneral

open Filter Asymptotics

/-- Histogram obtained by pushing a finite alphabet count through a coarse labelling. -/
def projectedCount {α γ : Type*} [Fintype α] [DecidableEq γ]
    (g : α → γ) (k : α → ℕ) (c : γ) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a => g a = c), k a

/-- Words of a fixed fine type whose coordinatewise coarse projection is a specified word. -/
abbrev ProjectionFiber {α γ : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq γ] (n : ℕ) (g : α → γ) (k : α → ℕ)
    (y : Fin n → γ) :=
  {x : Fin n → α // (∀ a, typeCnt x a = k a) ∧ ∀ i, g (x i) = y i}

private theorem typeCnt_comp_eq_projectedCount
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ) (x : Fin n → α)
    (hx : ∀ a, typeCnt x a = k a) (c : γ) :
    typeCnt (fun i => g (x i)) c = projectedCount g k c := by
  classical
  rw [typeCnt, projectedCount,
    Finset.card_eq_sum_card_fiberwise (f := x)
      (s := (Finset.univ : Finset (Fin n)).filter (fun i => g (x i) = c))
      (t := (Finset.univ : Finset α).filter (fun a => g a = c))]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [← hx a, typeCnt]
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

/-- Coarse projection maps a fine type class to its pushed-forward type class. -/
def projectTypeWord {α γ : Type*} [Fintype α] [Fintype γ]
    [DecidableEq α] [DecidableEq γ] {n : ℕ} (g : α → γ) (k : α → ℕ)
    (x : {x : Fin n → α // ∀ a, typeCnt x a = k a}) :
    {y : Fin n → γ // ∀ c, typeCnt y c = projectedCount g k c} :=
  ⟨fun i => g (x.1 i), typeCnt_comp_eq_projectedCount g k x.1 x.2⟩

private theorem filter_card_eq_of_perm {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ => e i) (fun i _ => e.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (h (e.symm i)).mpr (by simpa using (Finset.mem_filter.mp hi).2)
  · intro i _
    exact e.symm_apply_apply i
  · intro i _
    exact e.apply_symm_apply i

private theorem typeCnt_comp_perm {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → α) (a : α) :
    typeCnt (fun i => x (e i)) a = typeCnt x a := by
  unfold typeCnt
  exact filter_card_eq_of_perm e
    (fun i => x (e i) = a) (fun i => x i = a) (fun _ => Iff.rfl)

private theorem exists_perm_of_typeCnt
    {γ : Type*} [Fintype γ] [DecidableEq γ] {n : ℕ}
    (y z : Fin n → γ) (h : ∀ c, typeCnt y c = typeCnt z c) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, z (e i) = y i := by
  obtain ⟨e⟩ : Nonempty (∀ c : γ, {i // y i = c} ≃ {i // z i = c}) :=
    ⟨fun c => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h c)⟩
  refine ⟨(Equiv.sigmaFiberEquiv y).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv z)), fun i => ?_⟩
  exact (e (y i) ⟨i, rfl⟩).2

private noncomputable def projectionFiberEquiv
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ) (y z : Fin n → γ)
    (hyz : ∀ c, typeCnt y c = typeCnt z c) :
    ProjectionFiber n g k y ≃ ProjectionFiber n g k z := by
  classical
  let e := Classical.choose (exists_perm_of_typeCnt y z hyz)
  have he : ∀ i, z (e i) = y i :=
    Classical.choose_spec (exists_perm_of_typeCnt y z hyz)
  refine
    { toFun := fun x => by
        refine ⟨fun j => x.1 (e.symm j), ?_, ?_⟩
        · intro a
          rw [typeCnt_comp_perm]
          exact x.2.1 a
        · intro j
          exact (x.2.2 (e.symm j)).trans (by
            simpa only [e.apply_symm_apply] using (he (e.symm j)).symm)
      invFun := fun x => by
        refine ⟨fun i => x.1 (e i), ?_, ?_⟩
        · intro a
          rw [typeCnt_comp_perm]
          exact x.2.1 a
        · intro i
          exact (x.2.2 (e i)).trans (he i)
      left_inv := fun x => by
        apply Subtype.ext
        funext i
        simp only [e.symm_apply_apply]
      right_inv := fun x => by
        apply Subtype.ext
        funext i
        simp only [e.apply_symm_apply] }

private def projectTypeWordFiberEquiv
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ)
    (y : {y : Fin n → γ // ∀ c, typeCnt y c = projectedCount g k c}) :
    {x : {x : Fin n → α // ∀ a, typeCnt x a = k a} //
      projectTypeWord g k x = y} ≃ ProjectionFiber n g k y.1 where
  toFun x := by
    refine ⟨x.1.1, x.1.2, ?_⟩
    intro i
    exact congrFun (congrArg Subtype.val x.2) i
  invFun x := by
    refine ⟨⟨x.1, x.2.1⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact x.2.2 i
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Exact constant-fibre factorization behind the `P` count at
`constituent.tex:397-400`: a fine type class is its projected coarse type class times the
number of fine words above any one coarse word. -/
theorem typeWords_card_eq_mul_projectionFiber
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ)
    (y : {y : Fin n → γ // ∀ c, typeCnt y c = projectedCount g k c}) :
    Fintype.card {x : Fin n → α // ∀ a, typeCnt x a = k a} =
      Fintype.card {z : Fin n → γ // ∀ c, typeCnt z c = projectedCount g k c} *
        Fintype.card (ProjectionFiber n g k y.1) := by
  classical
  let Fine := {x : Fin n → α // ∀ a, typeCnt x a = k a}
  let Coarse := {z : Fin n → γ // ∀ c, typeCnt z c = projectedCount g k c}
  let project : Fine → Coarse := projectTypeWord g k
  calc
    Fintype.card Fine =
      Fintype.card ((z : Coarse) × {x : Fine // project x = z}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv project).symm
    _ = ∑ z : Coarse, Fintype.card {x : Fine // project x = z} :=
      Fintype.card_sigma
    _ = ∑ _z : Coarse, Fintype.card (ProjectionFiber n g k y.1) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Fintype.card_congr (projectTypeWordFiberEquiv g k z)]
      exact Fintype.card_congr (projectionFiberEquiv g k z.1 y.1
        (fun c => (z.2 c).trans (y.2 c).symm))
    _ = Fintype.card Coarse * Fintype.card (ProjectionFiber n g k y.1) := by
      simp

/-- Entropy lower bound for the fixed coarse-word fibre in
`constituent.tex:397-400`.  It is the fine type-class lower bound divided by the coarse
type-class upper bound; constant fibres make the division valid for the particular coarse word,
not merely for an average fibre. -/
theorem projectionFiber_entropy_lower
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ) (hk : ∑ a, k a = n)
    (y : {y : Fin n → γ // ∀ c, typeCnt y c = projectedCount g k c}) :
    Real.exp ((n : ℝ) *
        (entropyNats (fun a => (k a : ℝ) / n) -
          entropyNats (fun c => (projectedCount g k c : ℝ) / n))) /
      ((n : ℝ) + 1) ^ Fintype.card α ≤
        (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
  classical
  let kγ : γ → ℕ := projectedCount g k
  let Hα := entropyNats (fun a => (k a : ℝ) / n)
  let Hγ := entropyNats (fun c => (kγ c : ℝ) / n)
  have hkγ : ∑ c, kγ c = n := by
    calc
      ∑ c, kγ c = ∑ c, typeCnt y.1 c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (y.2 c).symm
      _ = n := OmegaBound.ADVXXZ.sum_typeCnt y.1
  have hfine := type_class_bounds n k hk
  have hcoarse := type_class_bounds n kγ hkγ
  dsimp only at hfine hcoarse
  have hfactor := typeWords_card_eq_mul_projectionFiber g k y
  have hprod :
      Real.exp ((n : ℝ) * Hα) / ((n : ℝ) + 1) ^ Fintype.card α ≤
        Real.exp ((n : ℝ) * Hγ) *
          (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
    calc
      Real.exp ((n : ℝ) * Hα) / ((n : ℝ) + 1) ^ Fintype.card α ≤
          (Fintype.card {x : Fin n → α // ∀ a, typeCnt x a = k a} : ℝ) :=
        hfine.1
      _ = (Fintype.card
            {z : Fin n → γ // ∀ c, typeCnt z c = projectedCount g k c} : ℝ) *
          (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
        exact_mod_cast hfactor
      _ ≤ Real.exp ((n : ℝ) * Hγ) *
          (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoarse.2 (Nat.cast_nonneg _)
  have hexp : 0 < Real.exp ((n : ℝ) * Hγ) := Real.exp_pos _
  have hdiv :
      (Real.exp ((n : ℝ) * Hα) /
          ((n : ℝ) + 1) ^ Fintype.card α) /
          Real.exp ((n : ℝ) * Hγ) ≤
        (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
    rw [div_le_iff₀ hexp]
    simpa only [mul_comm] using hprod
  have hrearrange :
      Real.exp ((n : ℝ) * (Hα - Hγ)) /
          ((n : ℝ) + 1) ^ Fintype.card α =
        (Real.exp ((n : ℝ) * Hα) /
          ((n : ℝ) + 1) ^ Fintype.card α) /
            Real.exp ((n : ℝ) * Hγ) := by
    rw [show (n : ℝ) * (Hα - Hγ) =
      (n : ℝ) * Hα - (n : ℝ) * Hγ by ring, Real.exp_sub]
    ring
  simpa only [Hα, Hγ, kγ] using hrearrange.trans_le hdiv

/-- Entropy upper bound for the same fixed projection fibre.  This is the complementary
type-class division used for the compatible numerator in `constituent.tex:401-425`: the
fine type-class upper bound is divided by the coarse type-class lower bound, leaving only
the displayed polynomial factor. -/
theorem projectionFiber_entropy_upper
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    {n : ℕ} (g : α → γ) (k : α → ℕ) (hk : ∑ a, k a = n)
    (y : {y : Fin n → γ // ∀ c, typeCnt y c = projectedCount g k c}) :
    (Fintype.card (ProjectionFiber n g k y.1) : ℝ) ≤
      Real.exp ((n : ℝ) *
        (entropyNats (fun a => (k a : ℝ) / n) -
          entropyNats (fun c => (projectedCount g k c : ℝ) / n))) *
        ((n : ℝ) + 1) ^ Fintype.card γ := by
  classical
  let kγ : γ → ℕ := projectedCount g k
  let Hα := entropyNats (fun a => (k a : ℝ) / n)
  let Hγ := entropyNats (fun c => (kγ c : ℝ) / n)
  have hkγ : ∑ c, kγ c = n := by
    calc
      ∑ c, kγ c = ∑ c, typeCnt y.1 c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (y.2 c).symm
      _ = n := OmegaBound.ADVXXZ.sum_typeCnt y.1
  have hfine := type_class_bounds n k hk
  have hcoarse := type_class_bounds n kγ hkγ
  dsimp only at hfine hcoarse
  have hfactor := typeWords_card_eq_mul_projectionFiber g k y
  have hprod :
      Real.exp ((n : ℝ) * Hγ) /
          ((n : ℝ) + 1) ^ Fintype.card γ *
          (Fintype.card (ProjectionFiber n g k y.1) : ℝ) ≤
        Real.exp ((n : ℝ) * Hα) := by
    calc
      Real.exp ((n : ℝ) * Hγ) /
            ((n : ℝ) + 1) ^ Fintype.card γ *
            (Fintype.card (ProjectionFiber n g k y.1) : ℝ) ≤
          (Fintype.card
            {z : Fin n → γ // ∀ c, typeCnt z c = projectedCount g k c} : ℝ) *
            (Fintype.card (ProjectionFiber n g k y.1) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoarse.1 (Nat.cast_nonneg _)
      _ = (Fintype.card
            {x : Fin n → α // ∀ a, typeCnt x a = k a} : ℝ) := by
        exact_mod_cast hfactor.symm
      _ ≤ Real.exp ((n : ℝ) * Hα) := hfine.2
  have hpoly : 0 < ((n : ℝ) + 1) ^ Fintype.card γ := by positivity
  have hden :
      0 < Real.exp ((n : ℝ) * Hγ) /
        ((n : ℝ) + 1) ^ Fintype.card γ := div_pos (Real.exp_pos _) hpoly
  have hdiv :
      (Fintype.card (ProjectionFiber n g k y.1) : ℝ) ≤
        Real.exp ((n : ℝ) * Hα) /
          (Real.exp ((n : ℝ) * Hγ) /
            ((n : ℝ) + 1) ^ Fintype.card γ) := by
    rw [le_div_iff₀ hden]
    simpa only [mul_comm] using hprod
  have hrearrange :
      Real.exp ((n : ℝ) * Hα) /
          (Real.exp ((n : ℝ) * Hγ) /
            ((n : ℝ) + 1) ^ Fintype.card γ) =
        Real.exp ((n : ℝ) * (Hα - Hγ)) *
          ((n : ℝ) + 1) ^ Fintype.card γ := by
    rw [show (n : ℝ) * (Hα - Hγ) =
      (n : ℝ) * Hα - (n : ℝ) * Hγ by ring, Real.exp_sub]
    field_simp [ne_of_gt (Real.exp_pos _), ne_of_gt hpoly]
  simpa only [Hα, Hγ, kγ] using hdiv.trans_eq hrearrange

/-- An `o(L)` estimate in Mathlib's filter notation gives the explicit
`Sublinear L` predicate. -/
theorem sublinear_of_isLittleO {L : ℕ → ℕ} {f : ℕ → ℝ}
    (h : f =o[Filter.atTop] (fun m => (L m : ℝ))) : Sublinear L f := by
  intro δ hδ
  have heventually := h.bound hδ
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨M, hM⟩ := heventually
  refine ⟨M, fun m hm => ?_⟩
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (L m : ℝ) from Nat.cast_nonneg _)] using hM m hm

private theorem cast_succ_isBigO_cast_mul (b : ℕ) (hb : 0 < b) :
    (fun m : ℕ => (m : ℝ) + 1) =O[Filter.atTop]
      (fun m : ℕ => ((b * m : ℕ) : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with m hm
  have hnat : m + 1 ≤ 2 * (b * m) := by
    have hb1 : 1 ≤ b := hb
    have hmb : m ≤ b * m := by
      simpa only [one_mul] using Nat.mul_le_mul_right m hb1
    omega
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1),
    abs_of_nonneg (Nat.cast_nonneg (b * m))]
  exact_mod_cast hnat

private theorem log_succ_isLittleO_mul (b : ℕ) (hb : 0 < b) :
    (fun m : ℕ => Real.log ((m : ℝ) + 1)) =o[Filter.atTop]
      (fun m : ℕ => ((b * m : ℕ) : ℝ)) := by
  have harg : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop
  have hlog : (fun m : ℕ => Real.log ((m : ℝ) + 1)) =o[Filter.atTop]
      (fun m : ℕ => (m : ℝ) + 1) := by
    simpa only [Function.comp_apply] using
      Real.isLittleO_log_id_atTop.comp_tendsto harg
  exact hlog.trans_isBigO (cast_succ_isBigO_cast_mul b hb)

/-- The polynomial factors in the type-class estimates on `constituent.tex:397-439`
become an admissible nonnegative logarithmic loss. -/
theorem log_succ_loss (b : ℕ) (hb : 0 < b) (C : ℝ) (hC : 0 ≤ C) :
    Loss (fun m => b * m) (fun _ε m => C * Real.log ((m : ℝ) + 1)) := by
  constructor
  · intro ε m
    exact mul_nonneg hC (Real.log_nonneg (by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith))
  · intro ε hε
    apply sublinear_of_isLittleO
    exact (log_succ_isLittleO_mul b hb).const_mul_left C

/-- The finite weighted entropy-continuity debit used at `constituent.tex:439` still vanishes
with the tolerance. -/
theorem vanishesWithTolerance_const_mul (c : ℝ) (hc : 0 ≤ c)
    {delta : ℚ → ℝ} (hdelta : VanishesWithTolerance delta) :
    VanishesWithTolerance (fun ε => c * delta ε) := by
  constructor
  · intro ε
    exact mul_nonneg hc (hdelta.1 ε)
  · intro ζ hζ
    rcases eq_or_lt_of_le hc with rfl | hcpos
    · exact ⟨1, by norm_num, fun ε hε hε1 => by simpa using hζ.le⟩
    · obtain ⟨ε₀, hε₀, hsmall⟩ := hdelta.2 (ζ / c) (div_pos hζ hcpos)
      refine ⟨ε₀, hε₀, ?_⟩
      intro ε hε hεle
      rw [abs_mul, abs_of_nonneg hc]
      calc
        c * |delta ε| ≤ c * (ζ / c) :=
          mul_le_mul_of_nonneg_left (hsmall ε hε hεle) hc
        _ = ζ := by field_simp [hcpos.ne']

end OmegaBound.ADVXXZGeneral
end
