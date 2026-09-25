import OmegaBound.ADVXXZGeneralCExact42Centre
import OmegaBound.ADVXXZGeneralCExact33Sublinear

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

private theorem gridPool_prob_le_one42 {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) : P.prob i ≤ 1 := by
  rw [← P.sum_prob]
  exact Finset.single_le_sum (fun j _ => P.prob_nonneg j) (Finset.mem_univ i)

private theorem constituentOutBase_le_two42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (t : Fin s) (r : Fin 6)
    (v : ChildShape p t) : d.outBase ⟨t,r,v⟩ ≤ 2 * b * p.baseN t := by
  have hA : (d.A t).prob r ≤ 1 := gridPool_prob_le_one42 (d.A t) r
  have ha : (d.alpha t r).prob v +
      (d.alpha t r).prob (complement p t v) ≤ 2 := by
    linarith [gridPool_prob_le_one42 (d.alpha t r) v,
      gridPool_prob_le_one42 (d.alpha t r) (complement p t v)]
  have hleft : (b : ℚ) * p.baseN t * (d.A t).prob r ≤
      (b : ℚ) * p.baseN t := by
    exact mul_le_of_le_one_right (by positivity) hA
  have hcast : (d.outBase ⟨t,r,v⟩ : ℚ) ≤ (2 * b * p.baseN t : ℕ) := by
    rw [hd.out_eq t r v]
    calc
      (b : ℚ) * p.baseN t * (d.A t).prob r *
          ((d.alpha t r).prob v +
            (d.alpha t r).prob (complement p t v))
          ≤ ((b : ℚ) * p.baseN t) * 2 :=
        mul_le_mul hleft ha
          (add_nonneg ((d.alpha t r).prob_nonneg v)
            ((d.alpha t r).prob_nonneg (complement p t v))) (by positivity)
      _ = (2 * b * p.baseN t : ℕ) := by push_cast; ring
  exact_mod_cast hcast

private theorem constituentOutN_le_two_length42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ)
    (i : Fin (Fintype.card (ConstituentTerm p))) :
    constituentOutN d.toPaper m i ≤ 2 * cLength p b m := by
  let a := constituentIndex (p := p) i
  have hi : Fintype.equivFin (ConstituentTerm p) a = i := by
    simp [a, constituentIndex]
  rw [← hi]
  rcases a with ⟨t,r,v⟩
  rw [constituentOutN_grid_index]
  have hbase : p.baseN t ≤ constituentBaseTotal p := by
    rw [constituentBaseTotal]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (p.baseN j)) (Finset.mem_univ t)
  calc
    d.outBase ⟨t,r,v⟩ * m ≤ (2 * b * p.baseN t) * m :=
      Nat.mul_le_mul_right m (constituentOutBase_le_two42 d hd t r v)
    _ ≤ (2 * b * constituentBaseTotal p) * m := by
      exact Nat.mul_le_mul_right m (Nat.mul_le_mul_left (2*b) hbase)
    _ = 2 * cLength p b m := by simp only [cLength]; ring

private abbrev ConstituentReducedGridCode42 {w s : ℕ}
    (p : ConstituentInput w s) (L : ℕ) :=
  (Fin (Fintype.card (ConstituentTerm p)) ×
    (Side × { σ : Chunk w // σ ≠ default })) → Fin (2*L+1)

private noncomputable def constituentReducedFullGridCode42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (ε : ℚ)
    (h : ConstituentFullGrid27 d m ε) :
    ConstituentReducedGridCode42 p (cLength p b m) := fun a => by
  refine ⟨(h.val.val a.1 a.2.1 a.2.2.val).val, Nat.lt_succ_of_le ?_⟩
  have hv : (h.val.val a.1 a.2.1 a.2.2.val).val ≤
      constituentOutN d.toPaper m a.1 :=
    Nat.lt_succ_iff.mp (h.val.val a.1 a.2.1 a.2.2.val).isLt
  exact hv.trans (constituentOutN_le_two_length42 d hd m a.1)

private theorem constituentReducedFullGridCode_injective42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (ε : ℚ) :
    Function.Injective (constituentReducedFullGridCode42 d hd m ε) := by
  intro ξ η hcode
  apply Subtype.ext
  apply Subtype.ext
  funext i W σ
  apply Fin.ext
  by_cases hσ : σ = default
  · subst σ
    have hsumξ := ξ.val.property.1 i W
    have hsumη := η.val.property.1 i W
    have hother :
        ∑ τ ∈ (Finset.univ : Finset (Chunk w)).erase default,
            (ξ.val.val i W τ).val =
          ∑ τ ∈ (Finset.univ : Finset (Chunk w)).erase default,
            (η.val.val i W τ).val := by
      apply Finset.sum_congr rfl
      intro τ hτ
      have hne : τ ≠ default := (Finset.mem_erase.mp hτ).1
      have hc := congrArg Fin.val (congrFun hcode (i, (W, ⟨τ, hne⟩)))
      change (ξ.val.val i W τ).val = (η.val.val i W τ).val at hc
      exact hc
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ default)] at hsumξ hsumη
    omega
  · have hc := congrArg Fin.val (congrFun hcode (i, (W, ⟨σ, hσ⟩)))
    change (ξ.val.val i W σ).val = (η.val.val i W σ).val at hc
    exact hc

private theorem constituent_full_grid_card_raw42 {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (ε : ℚ) :
    Fintype.card (ConstituentFullGrid27 d m ε) ≤
      (2*cLength p b m+1) ^
        (3 * Fintype.card (ConstituentTerm p) *
          (Fintype.card (Chunk w) - 1)) := by
  calc
    Fintype.card (ConstituentFullGrid27 d m ε) ≤
        Fintype.card (ConstituentReducedGridCode42 p (cLength p b m)) :=
      Fintype.card_le_of_injective _
        (constituentReducedFullGridCode_injective42 d hd m ε)
    _ = (2*cLength p b m+1) ^
        (3 * Fintype.card (ConstituentTerm p) *
          (Fintype.card (Chunk w) - 1)) := by
      simp [ConstituentReducedGridCode42]
      congr 1
      have hside : Fintype.card Side = 3 := by decide +kernel
      rw [hside]
      ring

private theorem constituentTerm_card_pos42 {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) :
    0 < Fintype.card (ConstituentTerm p) := by
  let t : Fin s := ⟨0, p.terms_nonempty⟩
  let r : Fin 6 := 0
  have hchild : Nonempty (ChildShape p t) := by
    by_contra hempty
    letI : IsEmpty (ChildShape p t) := not_nonempty_iff.mp hempty
    have hs := (d.alpha t r).sum_prob
    simp at hs
  exact Fintype.card_pos_iff.mpr ⟨⟨t, r, Classical.choice hchild⟩⟩

set_option maxHeartbeats 1000000 in
-- The dependent finite-code cardinality and eventual exponent absorption need extra elaboration.
/-- The nearby constituent grids form an eventually nonempty polynomial pool. -/
theorem constituent_full_grid_pool28 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) :
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      1 ≤ Fintype.card (ConstituentFullGrid27 d m ε) ∧
        Fintype.card (ConstituentFullGrid27 d m ε) ≤
          (cLength p b m + 1)^ConstituentGridDimension p d := by
  intro ε hε
  let T := Fintype.card (ConstituentTerm p)
  let K := Fintype.card (Chunk w)
  let E := 3*T*(K-1)
  refine ⟨2^E, fun m hm => ?_⟩
  let L := cLength p b m
  have hT : 0 < T := constituentTerm_card_pos42 p d
  have hK : 0 < K := Fintype.card_pos
  have hgap : E + 1 ≤ 3*T*K := by
    have hthreeT : 1 ≤ 3*T := by omega
    have hident : E + 3*T = 3*T*K := by
      calc
        E + 3*T = 3*T*((K-1)+1) := by dsimp only [E]; ring
        _ = 3*T*K := by rw [Nat.sub_add_cancel hK]
    omega
  have hM : 2^E ≤ L + 1 := by
    calc
      2^E ≤ m := hm
      _ ≤ L := le_cLength 1 p d b m hb.1
      _ ≤ L+1 := Nat.le_succ L
  constructor
  · exact Fintype.card_pos_iff.mpr
      ⟨constituentCentreFullGrid42 d hd hb m ε hε.le⟩
  · calc
      Fintype.card (ConstituentFullGrid27 d m ε) ≤
          (2*L+1)^E := by
        simpa only [L, E, T, K] using constituent_full_grid_card_raw42 d hd m ε
      _ ≤ (2*(L+1))^E :=
        Nat.pow_le_pow_left (by omega) E
      _ = 2^E * (L+1)^E := by rw [mul_pow]
      _ ≤ (L+1) * (L+1)^E := Nat.mul_le_mul_right _ hM
      _ = (L+1)^(E+1) := by rw [pow_succ]; ring
      _ ≤ (L+1)^(3*T*K) := Nat.pow_le_pow_right (by omega) hgap
      _ = (cLength p b m + 1)^ConstituentGridDimension p d := by
        simp only [L, T, K, ConstituentGridDimension, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        congr 1
        ac_rfl

end
end OmegaBound.ADVXXZGeneral
end
