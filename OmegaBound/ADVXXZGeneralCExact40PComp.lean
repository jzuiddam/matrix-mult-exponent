import OmegaBound.ADVXXZGeneralCompatibilityQuotientParent25
import OmegaBound.ADVXXZGeneralPProjectionParent25
import OmegaBound.ADVXXZGeneralPQPairWords
import OmegaBound.ADVXXZGeneralCoarseTransportParent25
import OmegaBound.ADVXXZGeneralEntropy
import OmegaBound.ADVXXZGeneralCExact36Defs

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

namespace Parent25

/-- The exact P-projection fibre statement at one empirical-grid scale. -/
def PProjectionBridge40 : Prop :=
  ∀ {w s b m : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
    ∀ ε r W (β : RepresentedLaw p d b ε m r W) (j : AlphaLabel p d b m r),
      Nonempty (PFiber p d b ε m r W β j.val ≃
        ((t : Fin s) → ProjectionFiber (parentCount p d b m r t)
          (fun σ : Chunk (w+w) => grade (leftHalf σ)) (betaCount p d b ε m r W β t)
          (fun i => coordFin (side d r W) (j.val.val ⟨t,i,0⟩).val))) ∧
      ∀ t c, OmegaBound.ADVXXZ.typeCnt
        (fun i => coordFin (side d r W) (j.val.val ⟨t,i,0⟩).val) c =
          projectedCount (fun σ : Chunk (w+w) => grade (leftHalf σ))
            (betaCount p d b ε m r W β t) c

end Parent25

private theorem rat_floor_nat_toNat (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem parent25_betaCount_eq_typeCnt {w s b : ℕ}
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
    exact rat_floor_nat_toNat 0
  · rw [div_mul_cancel₀]
    · exact rat_floor_nat_toNat _
    · exact_mod_cast hn

private theorem parent25_typeCnt_comp_eq_projectedCount
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

private theorem parent25_coordFin_val {w : ℕ} (S : Side) (u : Shape w) :
    (Parent25.coordFin S u).val = coord S u := by
  cases S <;> rfl

/-- Every represented paired law has the projected first-half histogram prescribed by every
exact-alpha target label. -/
theorem parent25_projected_beta_count40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (J : AlphaLabel p d b m r) (t : Fin s) (c : Fin (2*w+1)) :
    OmegaBound.ADVXXZ.typeCnt
        (fun i => Parent25.coordFin (Parent25.side d r W)
          (J.val.val ⟨t,i,0⟩).val) c =
      projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t) c := by
  classical
  rcases parent25_representedLaw_witness p d ε m r W β with ⟨K, a, haContains, haLaw⟩
  let shapeJ : Fin (Parent25.parentCount p d b m r t) → ChildShape p t :=
    fun i => J.val.val ⟨t, i, 0⟩
  let shapeK : Fin (Parent25.parentCount p d b m r t) → ChildShape p t :=
    fun i => K.val.val ⟨t, i, 0⟩
  let coordMap : ChildShape p t → Fin (2*w+1) :=
    fun u => Parent25.coordFin (Parent25.side d r W) u.val
  let pairs : Fin (Parent25.parentCount p d b m r t) → Chunk (w+w) :=
    fun i => Parent25.paired a t i
  have hJ : ∀ u, OmegaBound.ADVXXZ.typeCnt shapeJ u = Parent25.alphaCount p d b m r t u := by
    intro u
    exact parent25_alphaLabel_target_count p d r J t u
  have hK : ∀ u, OmegaBound.ADVXXZ.typeCnt shapeK u = Parent25.alphaCount p d b m r t u := by
    intro u
    exact parent25_alphaLabel_target_count p d r K t u
  have hcoord : (fun i => Parent25.grade (leftHalf (pairs i))) = fun i => coordMap (shapeK i) := by
    funext i
    apply Fin.ext
    dsimp only [pairs, coordMap, shapeK]
    change (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
      (Parent25.coordFin (Parent25.side d r W) (K.val.val ⟨t, i, 0⟩).val).val
    rw [show (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
      chunkLvl (leftHalf (Parent25.paired a t i)) by rfl, parent25_coordFin_val]
    rw [parent25_leftHalf_paired]
    exact haContains ⟨t, i, 0⟩
  have hpairs : ∀ σ, OmegaBound.ADVXXZ.typeCnt pairs σ =
      Parent25.betaCount p d b ε m r W β t σ := by
    intro σ
    exact (parent25_betaCount_eq_typeCnt p d ε m r W β a haLaw t σ).symm
  calc
    OmegaBound.ADVXXZ.typeCnt
        (fun i => Parent25.coordFin (Parent25.side d r W)
          (J.val.val ⟨t,i,0⟩).val) c =
        projectedCount coordMap (Parent25.alphaCount p d b m r t) c :=
      parent25_typeCnt_comp_eq_projectedCount coordMap
        (Parent25.alphaCount p d b m r t) shapeJ hJ c
    _ = OmegaBound.ADVXXZ.typeCnt (fun i => coordMap (shapeK i)) c :=
      (parent25_typeCnt_comp_eq_projectedCount coordMap
        (Parent25.alphaCount p d b m r t) shapeK hK c).symm
    _ = OmegaBound.ADVXXZ.typeCnt
        (fun i => Parent25.grade (leftHalf (pairs i))) c := by rw [hcoord]
    _ = projectedCount (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t) c :=
      parent25_typeCnt_comp_eq_projectedCount
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t) pairs hpairs c

private theorem parent25_coord_complement_eq_of_eq {w s : ℕ}
    {p : ConstituentInput w s} (t : Fin s) (S : Side) (u v : ChildShape p t)
    (h : coord S u.val = coord S v.val) :
    coord S (complement p t u).val = coord S (complement p t v).val := by
  cases S <;> simp only [complement, coord] at h ⊢ <;> omega

private theorem parent25_pfiber_predicate {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (J : AlphaLabel p d b m r)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W)) :
    (Parent25.contains p d b m r W J.val a ∧
        Parent25.empirical p d b m r W a = β.val) ↔
      ∀ t,
        (∀ σ, OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ =
          Parent25.betaCount p d b ε m r W β t σ) ∧
        ∀ i, Parent25.grade (leftHalf (Parent25.paired a t i)) =
          Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val := by
  classical
  constructor
  · rintro ⟨haContains, haLaw⟩ t
    constructor
    · intro σ
      exact (parent25_betaCount_eq_typeCnt p d ε m r W β a haLaw t σ).symm
    · intro i
      apply Fin.ext
      change (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
        (Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val).val
      rw [show (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
        chunkLvl (leftHalf (Parent25.paired a t i)) by rfl, parent25_coordFin_val,
        parent25_leftHalf_paired]
      exact haContains ⟨t, i, 0⟩
  · intro hx
    rcases parent25_representedLaw_witness p d ε m r W β with
      ⟨K, a₀, ha₀Contains, ha₀Law⟩
    constructor
    · rintro ⟨t, i, h⟩
      fin_cases h
      · have hi := congrArg Fin.val ((hx t).2 i)
        change (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
          (Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val).val at hi
        rw [show (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
          chunkLvl (leftHalf (Parent25.paired a t i)) by rfl, parent25_coordFin_val,
          parent25_leftHalf_paired] at hi
        exact hi
      · let σ := Parent25.paired a t i
        have hnewPos : 0 < OmegaBound.ADVXXZ.typeCnt
            (fun k => Parent25.paired a t k) σ := by
          unfold OmegaBound.ADVXXZ.typeCnt
          apply Finset.card_pos.mpr
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        have hwCount := parent25_betaCount_eq_typeCnt p d ε m r W β a₀ ha₀Law t σ
        have h₀Pos : 0 < OmegaBound.ADVXXZ.typeCnt
            (fun k => Parent25.paired a₀ t k) σ := by
          rw [← hwCount, ← (hx t).1 σ]
          exact hnewPos
        unfold OmegaBound.ADVXXZ.typeCnt at h₀Pos
        rcases Finset.card_pos.mp h₀Pos with ⟨k, hk⟩
        have hpair : Parent25.paired a₀ t k = Parent25.paired a t i := by
          exact (Finset.mem_filter.mp hk).2
        have hleftChunks := congrArg leftHalf hpair
        rw [parent25_leftHalf_paired, parent25_leftHalf_paired] at hleftChunks
        have hrightChunks := congrArg rightHalf hpair
        rw [parent25_rightHalf_paired, parent25_rightHalf_paired] at hrightChunks
        have hi := congrArg Fin.val ((hx t).2 i)
        change (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
          (Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val).val at hi
        rw [show (Parent25.grade (leftHalf (Parent25.paired a t i))).val =
          chunkLvl (leftHalf (Parent25.paired a t i)) by rfl, parent25_coordFin_val,
          parent25_leftHalf_paired] at hi
        have hleftCoord :
            coord (Parent25.side d r W) (K.val.val ⟨t,k,0⟩).val =
              coord (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val := by
          calc
            coord (Parent25.side d r W) (K.val.val ⟨t,k,0⟩).val =
                chunkLvl (a₀ ⟨t,k,0⟩) := (ha₀Contains ⟨t,k,0⟩).symm
            _ = chunkLvl (a ⟨t,i,0⟩) := congrArg chunkLvl hleftChunks
            _ = coord (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val := hi
        have hcomp := parent25_coord_complement_eq_of_eq t (Parent25.side d r W)
          (K.val.val ⟨t,k,0⟩) (J.val.val ⟨t,i,0⟩) hleftCoord
        calc
          chunkLvl (a ⟨t,i,1⟩) = chunkLvl (a₀ ⟨t,k,1⟩) :=
            (congrArg chunkLvl hrightChunks).symm
          _ = coord (Parent25.side d r W) (K.val.val ⟨t,k,1⟩).val :=
            ha₀Contains ⟨t,k,1⟩
          _ = coord (Parent25.side d r W)
              (complement p t (K.val.val ⟨t,k,0⟩)).val := by
            rw [parent25_alphaLabel_complementary p d r K t k]
          _ = coord (Parent25.side d r W)
              (complement p t (J.val.val ⟨t,i,0⟩)).val := hcomp
          _ = coord (Parent25.side d r W) (J.val.val ⟨t,i,1⟩).val := by
            rw [parent25_alphaLabel_complementary p d r J t i]
    · funext t σ
      unfold Parent25.empirical
      have hwCount := parent25_betaCount_eq_typeCnt p d ε m r W β a₀ ha₀Law t σ
      have ha₀Point := congrFun (congrFun ha₀Law t) σ
      calc
        (OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a t i) σ : ℚ) /
            Parent25.parentCount p d b m r t =
          (Parent25.betaCount p d b ε m r W β t σ : ℚ) /
            Parent25.parentCount p d b m r t := by rw [(hx t).1 σ]
        _ = (OmegaBound.ADVXXZ.typeCnt (fun i => Parent25.paired a₀ t i) σ : ℚ) /
            Parent25.parentCount p d b m r t := by rw [hwCount]
        _ = β.val t σ := ha₀Point

private def parent25ProjectionFamilyEquiv {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (J : AlphaLabel p d b m r) :
    {x : (t : Fin s) → Fin (Parent25.parentCount p d b m r t) → Chunk (w+w) //
      ∀ t,
        (∀ σ, OmegaBound.ADVXXZ.typeCnt (x t) σ =
          Parent25.betaCount p d b ε m r W β t σ) ∧
        ∀ i, Parent25.grade (leftHalf (x t i)) =
          Parent25.coordFin (Parent25.side d r W) (J.val.val ⟨t,i,0⟩).val} ≃
      ((t : Fin s) → ProjectionFiber (Parent25.parentCount p d b m r t)
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t)
        (fun i => Parent25.coordFin (Parent25.side d r W)
          (J.val.val ⟨t,i,0⟩).val)) where
  toFun x t := ⟨x.val t, x.property t⟩
  invFun x := ⟨fun t => (x t).val, fun t => (x t).property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext t
    apply Subtype.ext
    rfl

private noncomputable def parent25PFiberEquiv {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W)
    (J : AlphaLabel p d b m r) :
    Parent25.PFiber p d b ε m r W β J.val ≃
      ((t : Fin s) → ProjectionFiber (Parent25.parentCount p d b m r t)
        (fun σ : Chunk (w+w) => Parent25.grade (leftHalf σ))
        (Parent25.betaCount p d b ε m r W β t)
        (fun i => Parent25.coordFin (Parent25.side d r W)
          (J.val.val ⟨t,i,0⟩).val)) :=
  ((parent25PairWordsEquiv (p := p) (d := d) (b := b) (m := m) (r := r)).subtypeEquiv
      (fun a => parent25_pfiber_predicate p d ε m r W β J a)).trans
    (parent25ProjectionFamilyEquiv p d ε m r W β J)

/-- The complete paired P-law has the exact parentwise projection fibres. -/
theorem constituent_P_projection_fibres40 : Parent25.PProjectionBridge40 := by
  intro w s b m p d _hd _hb ε r W β J
  constructor
  · exact ⟨parent25PFiberEquiv p d ε m r W β J⟩
  · intro t c
    exact parent25_projected_beta_count40 p d ε m r W β J t c

private def parent25PFiberSigmaEquiv {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    {z : AlphaLabel p d b m r ×
        (Parent25.Pop p d b m r).Part (Parent25.side d r W) //
      Parent25.contains p d b m r W z.1.val z.2 ∧
        Parent25.empirical p d b m r W z.2 = β.val} ≃
      ((J : AlphaLabel p d b m r) ×
        Parent25.PFiber p d b ε m r W β J.val) where
  toFun z := ⟨z.val.1, ⟨z.val.2, z.property⟩⟩
  invFun z := ⟨(z.1, z.2.val), z.2.property⟩
  left_inv z := by rfl
  right_inv z := by rfl

private def parent25QFiberSigmaEquiv {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    {z : AlphaLabel p d b m r ×
        (Parent25.Pop p d b m r).Part (Parent25.side d r W) //
      Parent25.contains p d b m r W z.1.val z.2 ∧
        Parent25.empirical p d b m r W z.2 = β.val ∧
        Parent25.compatible p d b m r W z.1.val z.2} ≃
      ((J : AlphaLabel p d b m r) ×
        {a : Parent25.PFiber p d b ε m r W β J.val //
          Parent25.compatible p d b m r W J.val a.val}) where
  toFun z := ⟨z.val.1, ⟨⟨z.val.2, z.property.1, z.property.2.1⟩, z.property.2.2⟩⟩
  invFun z := ⟨(z.1, z.2.val.val), z.2.val.property.1,
    z.2.val.property.2, z.2.property⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- The corrected raw P and Q probabilities retain their common ambient denominator and split
exactly into parent-label fibres. -/
theorem parent25_joint_cardinality_identities40 {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (β : RepresentedLaw p d b ε m r W) :
    let ambient := (Nat.card (AlphaLabel p d b m r ×
      (Parent25.Pop p d b m r).Part (Parent25.side d r W)) : ℝ)
    ambient * Parent25.jointP p d b ε m r W β =
        ∑ J : AlphaLabel p d b m r,
          (Nat.card (Parent25.PFiber p d b ε m r W β J.val) : ℝ) ∧
      ambient * Parent25.jointQ p d b ε m r W β =
        ∑ J : AlphaLabel p d b m r,
          (Nat.card {a : Parent25.PFiber p d b ε m r W β J.val //
    Parent25.compatible p d b m r W J.val a.val} : ℝ) := by
  classical
  letI : Fintype ((Parent25.Pop p d b m r).Part (Parent25.side d r W)) :=
    (Parent25.Pop p d b m r).partFinite (Parent25.side d r W)
  rcases parent25_representedLaw_witness p d ε m r W β with
    ⟨J₀, a₀, _ha₀Contains, _ha₀Law⟩
  let Ambient := AlphaLabel p d b m r ×
    (Parent25.Pop p d b m r).Part (Parent25.side d r W)
  haveI : Nonempty Ambient := ⟨(J₀, a₀)⟩
  have hAmbientNat : Nat.card Ambient ≠ 0 := Nat.card_pos.ne'
  have hAmbient : (Nat.card Ambient : ℝ) ≠ 0 := by exact_mod_cast hAmbientNat
  letI : ∀ J : AlphaLabel p d b m r,
      Finite (Parent25.PFiber p d b ε m r W β J.val) := fun _ =>
    Finite.of_injective (fun a => a.val) Subtype.val_injective
  letI : ∀ J : AlphaLabel p d b m r,
      Finite {a : Parent25.PFiber p d b ε m r W β J.val //
        Parent25.compatible p d b m r W J.val a.val} := fun _ =>
    Finite.of_injective (fun a => a.val) Subtype.val_injective
  have hP : Nat.card
      {z : AlphaLabel p d b m r ×
          (Parent25.Pop p d b m r).Part (Parent25.side d r W) //
        Parent25.contains p d b m r W z.1.val z.2 ∧
          Parent25.empirical p d b m r W z.2 = β.val} =
      ∑ J : AlphaLabel p d b m r,
        Nat.card (Parent25.PFiber p d b ε m r W β J.val) := by
    rw [Nat.card_congr (parent25PFiberSigmaEquiv p d ε m r W β), Nat.card_sigma]
  have hQ : Nat.card
      {z : AlphaLabel p d b m r ×
          (Parent25.Pop p d b m r).Part (Parent25.side d r W) //
        Parent25.contains p d b m r W z.1.val z.2 ∧
          Parent25.empirical p d b m r W z.2 = β.val ∧
          Parent25.compatible p d b m r W z.1.val z.2} =
      ∑ J : AlphaLabel p d b m r,
        Nat.card {a : Parent25.PFiber p d b ε m r W β J.val //
          Parent25.compatible p d b m r W J.val a.val} := by
    rw [Nat.card_congr (parent25QFiberSigmaEquiv p d ε m r W β), Nat.card_sigma]
  dsimp only
  constructor
  · unfold Parent25.jointP
    change (Nat.card Ambient : ℝ) * (_ / (Nat.card Ambient : ℝ)) = _
    rw [mul_div_cancel₀ _ hAmbient]
    exact_mod_cast hP
  · unfold Parent25.jointQ
    change (Nat.card Ambient : ℝ) * (_ / (Nat.card Ambient : ℝ)) = _
    rw [mul_div_cancel₀ _ hAmbient]
    exact_mod_cast hQ

end OmegaBound.ADVXXZGeneral
end
