import OmegaBound.ADVXXZGeneralAmend31BoundaryDimensionPos
import OmegaBound.Rank

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

private def boundaryFactor31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ) (W : Side) : ℕ :=
  if boundaryActive31 a W then
    (boundaryWords31 q a n (boundaryReadingSide31 W)).card else 1

private def boundaryWordAt31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ) (W : Side)
    (i : Fin (boundaryWords31 q a n W).card) :
    Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q :=
  ((boundaryWords31 q a n W).equivFin.symm i).1

private theorem boundaryWordAt31_mem (q : ℕ) (a : ℚ × AtomKey) (n : ℕ) (W : Side)
    (i : Fin (boundaryWords31 q a n W).card) :
    boundaryWordAt31 q a n W i ∈ boundaryWords31 q a n W :=
  ((boundaryWords31 q a n W).equivFin.symm i).2

private theorem boundaryWordAt31_injective (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (W : Side) : Function.Injective (boundaryWordAt31 q a n W) := by
  intro i j hij
  apply (boundaryWords31 q a n W).equivFin.symm.injective
  apply Subtype.ext
  exact hij

private theorem boundaryWordAt31_level (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (W : Side) (i : Fin (boundaryWords31 q a n W).card) (t : Fin (a.1 * (n : ℚ)).floor.toNat) :
    levOf (boundaryWordAt31 q a n W i t) = coord W a.2.2.1 := by
  have h := boundaryWordAt31_mem q a n W i
  rw [boundaryWords31, Finset.mem_filter] at h
  exact h.2.1 t

private theorem boundaryWordAt31_emp (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (W : Side) (i : Fin (boundaryWords31 q a n W).card)
    (hk : (a.1 * (n : ℚ)).floor.toNat ≠ 0) (σ : Chunk a.2.1) :
    emp (chunkSeq (boundaryWordAt31 q a n W i)) σ = a.2.2.2 W σ := by
  have h := boundaryWordAt31_mem q a n W i
  rw [boundaryWords31, Finset.mem_filter] at h
  exact h.2.2.resolve_left hk σ

private theorem boundary_reflect_reflect31 {w : ℕ} (σ : Chunk w) :
    reflect (reflect σ) = σ := by
  funext j
  apply Fin.ext
  simp [reflect]
  have hj := (σ j).isLt
  omega

private theorem boundary_chunkLvl_reflect_add31 {w : ℕ} (σ : Chunk w) :
    chunkLvl (reflect σ) + chunkLvl σ = 2 * w := by
  have hpoint (x : Fin w) : (reflect σ x).val + (σ x).val = 2 := by
    simp only [reflect]
    have hx := (σ x).isLt
    omega
  calc
    chunkLvl (reflect σ) + chunkLvl σ =
        ∑ x : Fin w, ((reflect σ x).val + (σ x).val) := by
          simp only [chunkLvl, Finset.sum_add_distrib]
    _ =
        ∑ _x : Fin w, 2 := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact hpoint x
    _ = 2 * w := by simp [Nat.mul_comm]

private theorem boundary_emp_partner31 {q w k : ℕ}
    (x : Fin k → Fin w → CW90.Idx7 q) (σ : Chunk w) :
    emp (chunkSeq (boundaryWordPartner31 x)) σ = emp (chunkSeq x) (reflect σ) := by
  unfold emp typeCnt
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [boundary_partner_chunks31]
  constructor
  · intro h
    have := congrArg reflect h
    simpa only [boundary_reflect_reflect31] using this
  · intro h
    rw [h, boundary_reflect_reflect31]

private theorem boundary_rat_floor_toNat_nat31 (r : ℕ) : ((r : ℚ).floor).toNat = r := by
  change ((((r : ℤ) : ℚ).floor).toNat) = r
  rw [Rat.floor_intCast]
  simp

private theorem boundary_count_cast_restrict31 (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) (σ : Chunk a.2.1) :
    (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
  have ha := hI a (by simp)
  rcases ha with ⟨_hma, _hbeta_nonneg, _hsum, _hsupport, _hzero, _hreflect,
    ⟨K, hK⟩, hbeta⟩
  rcases hbeta W σ with ⟨C, hC⟩
  have hkmul : a.1 * (((b*m : ℕ) : ℚ)) = ((K*m : ℕ) : ℚ) := by
    calc
      a.1 * (((b*m : ℕ) : ℚ)) = ((b : ℚ) * a.1) * (m : ℚ) := by
        push_cast
        ring
      _ = (K : ℚ) * (m : ℚ) := by rw [hK]
      _ = ((K*m : ℕ) : ℚ) := by push_cast; rfl
  have hk : (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = K*m := by
    rw [hkmul]
    exact boundary_rat_floor_toNat_nat31 _
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
  rw [hk, hcmul, boundary_rat_floor_toNat_nat31]

private theorem boundary_type_counts_sum_restrict31 (b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hI : BoundaryInventoryAdmissible [a] b) :
    ∑ σ, boundaryTypeCounts31 a (b*m) W σ =
      (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat := by
  have ha := hI a (by simp)
  rcases ha with ⟨_hma, _hbeta_nonneg, hsum, _hsupport, _hzero, _hreflect,
    _hmass, _hbeta_integral⟩
  have hq : ((∑ σ, boundaryTypeCounts31 a (b*m) W σ : ℕ) : ℚ) =
      ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by
    rw [Nat.cast_sum]
    calc
      ∑ σ : Chunk a.2.1, (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
          ∑ σ : Chunk a.2.1,
            ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) * a.2.2.2 W σ := by
        apply Finset.sum_congr rfl
        intro σ _hσ
        exact boundary_count_cast_restrict31 b m a W hI σ
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) *
          ∑ σ : Chunk a.2.1, a.2.2.2 W σ := by rw [Finset.mul_sum]
      _ = ((a.1 * (((b*m : ℕ) : ℚ))).floor.toNat : ℚ) := by rw [hsum, mul_one]
  exact_mod_cast hq

private theorem boundary_words_pos_restrict31 (q b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b) :
    0 < (boundaryWords31 q a (b*m) W).card := by
  have hsum := boundary_type_counts_sum_restrict31 b m a W hI
  obtain ⟨s, hs⟩ := ADVXXZEps.exists_typeCnt_eq
    (boundaryTypeCounts31 a (b*m) W) hsum
  have hclass : 0 < Fintype.card
      {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
        ∀ σ, typeCnt x σ = boundaryTypeCounts31 a (b*m) W σ} :=
    Fintype.card_pos_iff.mpr ⟨⟨s, hs⟩⟩
  rw [boundary_words_card31 q b m a W hI]
  exact Nat.mul_pos hclass (Nat.pow_pos hq)

private def boundaryFirstWord31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ) (W : Side)
    (h : 0 < (boundaryWords31 q a n W).card) :
    Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q :=
  boundaryWordAt31 q a n W ⟨0, h⟩

private def boundaryLowWord31 {q w k : ℕ} : Fin k → Fin w → CW90.Idx7 q :=
  fun _ _ => .inl none

private def boundaryHighWord31 {q w k : ℕ} : Fin k → Fin w → CW90.Idx7 q :=
  fun _ _ => .inr ()

private theorem boundary_word_eq_low31 {q w : ℕ} (x : Fin w → CW90.Idx7 q)
    (h : levOf x = 0) : x = fun _ => .inl none := by
  funext j
  have hle : (lvl7 (x j)).val ≤ levOf x := by
    unfold levOf chunkLvl chunkOf
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (lvl7 (x i)).val)
      (Finset.mem_univ j)
  rw [h] at hle
  generalize x j = v at hle ⊢
  rcases v with (_ | i) | z
  · rfl
  · simp [CW90.lvl7] at hle
  · cases z
    simp [CW90.lvl7] at hle

private theorem boundary_word_eq_high31 {q w : ℕ} (x : Fin w → CW90.Idx7 q)
    (h : levOf x = 2 * w) : x = fun _ => .inr () := by
  funext j
  have hadd := boundary_chunkLvl_reflect_add31 (chunkOf x)
  have hrefzero : chunkLvl (reflect (chunkOf x)) = 0 := by
    change chunkLvl (reflect (chunkOf x)) + levOf x = 2 * w at hadd
    omega
  have hle : (reflect (chunkOf x) j).val ≤ chunkLvl (reflect (chunkOf x)) := by
    unfold chunkLvl
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (reflect (chunkOf x) i).val)
      (Finset.mem_univ j)
  rw [hrefzero] at hle
  have hj : (lvl7 (x j)).val = 2 := by
    simp only [reflect, chunkOf] at hle
    have hv := (lvl7 (x j)).isLt
    omega
  generalize x j = v at hj ⊢
  rcases v with (_ | i) | z
  · simp [CW90.lvl7] at hj
  · simp [CW90.lvl7] at hj
  · cases z
    rfl

private theorem boundary_cw_power_unit31 {q w k : ℕ}
    (x y z : Fin k → Fin w → CW90.Idx7 q) (i j l : ℕ)
    (hx : ∀ t, levOf (x t) = i) (hy : ∀ t, levOf (y t) = j)
    (hz : ∀ t, levOf (z t) = l) (hsum : i + j + l = 2 * w)
    (hzero : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ l = 0) ∨ (j = 0 ∧ l = 0)) :
    tensorPower (tensorPower (cwZ q) w) k x y z = 1 := by
  rcases hzero with hxy | hxz | hyz
  · have hl : l = 2 * w := by omega
    have ex : x = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (x t) (by rw [hx t, hxy.1])
    have ey : y = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (y t) (by rw [hy t, hxy.2])
    have ez : z = boundaryHighWord31 := by
      funext t
      exact boundary_word_eq_high31 (z t) (by rw [hz t, hl])
    subst x; subst y; subst z
    simp [tensorPower, boundaryLowWord31, boundaryHighWord31, cwZ]
  · have hj : j = 2 * w := by omega
    have ex : x = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (x t) (by rw [hx t, hxz.1])
    have ey : y = boundaryHighWord31 := by
      funext t
      exact boundary_word_eq_high31 (y t) (by rw [hy t, hj])
    have ez : z = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (z t) (by rw [hz t, hxz.2])
    subst x; subst y; subst z
    simp [tensorPower, boundaryLowWord31, boundaryHighWord31, cwZ]
  · have hi : i = 2 * w := by omega
    have ex : x = boundaryHighWord31 := by
      funext t
      exact boundary_word_eq_high31 (x t) (by rw [hx t, hi])
    have ey : y = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (y t) (by rw [hy t, hyz.1])
    have ez : z = boundaryLowWord31 := by
      funext t
      exact boundary_word_eq_low31 (z t) (by rw [hz t, hyz.2])
    subst x; subst y; subst z
    simp [tensorPower, boundaryLowWord31, boundaryHighWord31, cwZ]

private theorem boundary_partner_symbol_injective31 {q : ℕ} :
    Function.Injective (@boundarySymbol31 q) := by
  intro x y h
  have := congrArg boundarySymbol31 h
  simpa only [boundary_symbol_involutive31] using this

private theorem boundary_cw_power_zeroY31 {q w k : ℕ}
    (x y : Fin k → Fin w → CW90.Idx7 q) :
    tensorPower (tensorPower (cwZ q) w) k x boundaryLowWord31
      (boundaryWordPartner31 y) = if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_one
    intro t _ht
    apply Finset.prod_eq_one
    intro j _hj
    exact (boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (x t j))).2.1.trans
      (if_pos rfl)
  · rw [if_neg hxy]
    have hpoint : ∃ t, x t ≠ y t := by
      by_contra h
      apply hxy
      funext t
      exact not_ne_iff.mp (not_exists.mp h t)
    rcases hpoint with ⟨t, ht⟩
    have hcoord : ∃ j, x t j ≠ y t j := by
      by_contra h
      apply ht
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    rcases hcoord with ⟨j, hj⟩
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [(boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (y t j))).2.1]
    rw [if_neg]
    intro h
    exact hj (boundary_partner_symbol_injective31 h.symm)

private theorem boundary_cw_power_zeroZ31 {q w k : ℕ}
    (x y : Fin k → Fin w → CW90.Idx7 q) :
    tensorPower (tensorPower (cwZ q) w) k x (boundaryWordPartner31 y)
      boundaryLowWord31 = if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_one
    intro t _ht
    apply Finset.prod_eq_one
    intro j _hj
    exact (boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (x t j))).1.trans
      (if_pos rfl)
  · rw [if_neg hxy]
    have hpoint : ∃ t, x t ≠ y t := by
      by_contra h
      apply hxy
      funext t
      exact not_ne_iff.mp (not_exists.mp h t)
    rcases hpoint with ⟨t, ht⟩
    have hcoord : ∃ j, x t j ≠ y t j := by
      by_contra h
      apply ht
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    rcases hcoord with ⟨j, hj⟩
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [(boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (y t j))).1]
    rw [if_neg]
    intro h
    exact hj (boundary_partner_symbol_injective31 h.symm)

private theorem boundary_cw_power_zeroX31 {q w k : ℕ}
    (x y : Fin k → Fin w → CW90.Idx7 q) :
    tensorPower (tensorPower (cwZ q) w) k boundaryLowWord31 x
      (boundaryWordPartner31 y) = if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_one
    intro t _ht
    apply Finset.prod_eq_one
    intro j _hj
    exact (boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (x t j))).2.2.trans
      (if_pos rfl)
  · rw [if_neg hxy]
    have hpoint : ∃ t, x t ≠ y t := by
      by_contra h
      apply hxy
      funext t
      exact not_ne_iff.mp (not_exists.mp h t)
    rcases hpoint with ⟨t, ht⟩
    have hcoord : ∃ j, x t j ≠ y t j := by
      by_contra h
      apply ht
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    rcases hcoord with ⟨j, hj⟩
    unfold tensorPower boundaryLowWord31 boundaryWordPartner31
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [(boundary_symbol_coefficient31 (x t j) (boundarySymbol31 (y t j))).2.2]
    rw [if_neg]
    intro h
    exact hj (boundary_partner_symbol_injective31 h.symm)

private def boundaryOccurrenceX31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (hX : 0 < (boundaryWords31 q a n .X).card)
    (iA : Fin (boundaryFactor31 q a n .X))
    (iB : Fin (boundaryFactor31 q a n .Y)) :
    Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q :=
  if hA : boundaryActive31 a .X then
    boundaryWordAt31 q a n .X
      (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hA]) iA)
  else if hB : boundaryActive31 a .Y then
    boundaryWordAt31 q a n .X
      (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hB]) iB)
  else boundaryFirstWord31 q a n .X hX

private def boundaryOccurrenceY31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (hY : 0 < (boundaryWords31 q a n .Y).card)
    (iB : Fin (boundaryFactor31 q a n .Y))
    (iC : Fin (boundaryFactor31 q a n .Z)) :
    Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q :=
  if hB : boundaryActive31 a .Y then
    boundaryWordPartner31
      (boundaryWordAt31 q a n .X
        (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hB]) iB))
  else if hC : boundaryActive31 a .Z then
    boundaryWordAt31 q a n .Y
      (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hC]) iC)
  else boundaryFirstWord31 q a n .Y hY

private def boundaryOccurrenceZ31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (hZ : 0 < (boundaryWords31 q a n .Z).card)
    (iC : Fin (boundaryFactor31 q a n .Z))
    (iA : Fin (boundaryFactor31 q a n .X)) :
    Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q :=
  if hA : boundaryActive31 a .X then
    boundaryWordPartner31
      (boundaryWordAt31 q a n .X
        (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hA]) iA))
  else if hC : boundaryActive31 a .Z then
    boundaryWordPartner31
      (boundaryWordAt31 q a n .Y
        (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hC]) iC))
  else boundaryFirstWord31 q a n .Z hZ

private theorem boundaryPartnerWord_level31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (Z U V : Side) (hUV : U ≠ V) (hUZ : U ≠ Z) (hVZ : V ≠ Z)
    (hz : coord Z a.2.2.1 = 0) (i : Fin (boundaryWords31 q a n U).card)
    (t : Fin (a.1 * (n : ℚ)).floor.toNat) :
    levOf (boundaryWordPartner31 (boundaryWordAt31 q a n U i) t) =
      coord V a.2.2.1 := by
  have hbase := boundaryWordAt31_level q a n U i t
  have href := boundary_partner_chunks31 (boundaryWordAt31 q a n U i) t
  have hadd := boundary_chunkLvl_reflect_add31 (chunkSeq (boundaryWordAt31 q a n U i) t)
  have hshape := a.2.2.1.property
  change chunkLvl (chunkSeq (boundaryWordPartner31 (boundaryWordAt31 q a n U i)) t) = _
  rw [href]
  change chunkLvl (chunkSeq (boundaryWordAt31 q a n U i) t) = _ at hbase
  fin_cases Z <;> fin_cases U <;> fin_cases V <;>
    simp only [coord] at hz hbase hshape ⊢ <;> simp_all
  all_goals omega

private theorem boundaryPartnerWord_emp31 (q b m : ℕ) (a : ℚ × AtomKey)
    (Z U V : Side) (hUV : U ≠ V) (hUZ : U ≠ Z) (hVZ : V ≠ Z)
    (hz : coord Z a.2.2.1 = 0) (hI : BoundaryInventoryAdmissible [a] b)
    (i : Fin (boundaryWords31 q a (b*m) U).card)
    (hk : (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat ≠ 0) (σ : Chunk a.2.1) :
    emp (chunkSeq (boundaryWordPartner31 (boundaryWordAt31 q a (b*m) U i))) σ =
      a.2.2.2 V σ := by
  have ha := hI a (by simp)
  have hreflect := ha.2.2.2.2.2.1 Z U V hUV hUZ hVZ hz (reflect σ)
  calc
    emp (chunkSeq (boundaryWordPartner31 (boundaryWordAt31 q a (b*m) U i))) σ =
        emp (chunkSeq (boundaryWordAt31 q a (b*m) U i)) (reflect σ) :=
      boundary_emp_partner31 _ _
    _ = a.2.2.2 U (reflect σ) := boundaryWordAt31_emp q a (b*m) U i hk _
    _ = a.2.2.2 V σ := by rw [hreflect, boundary_reflect_reflect31]

private theorem boundaryOccurrenceX31_level (q b m : ℕ) (a : ℚ × AtomKey)
    (hX : 0 < (boundaryWords31 q a (b*m) .X).card)
    (iA : Fin (boundaryFactor31 q a (b*m) .X))
    (iB : Fin (boundaryFactor31 q a (b*m) .Y))
    (t : Fin (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat) :
    levOf (boundaryOccurrenceX31 q a (b*m) hX iA iB t) = coord .X a.2.2.1 := by
  unfold boundaryOccurrenceX31 boundaryFirstWord31
  split_ifs with hA hB
  all_goals apply boundaryWordAt31_level

private theorem boundaryOccurrenceX31_emp (q b m : ℕ) (a : ℚ × AtomKey)
    (hX : 0 < (boundaryWords31 q a (b*m) .X).card)
    (iA : Fin (boundaryFactor31 q a (b*m) .X))
    (iB : Fin (boundaryFactor31 q a (b*m) .Y))
    (hk : (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat ≠ 0) (σ : Chunk a.2.1) :
    emp (chunkSeq (boundaryOccurrenceX31 q a (b*m) hX iA iB)) σ = a.2.2.2 .X σ := by
  unfold boundaryOccurrenceX31 boundaryFirstWord31
  split_ifs with hA hB
  all_goals apply boundaryWordAt31_emp <;> assumption

private theorem boundaryOccurrenceY31_level (q b m : ℕ) (a : ℚ × AtomKey)
    (hY : 0 < (boundaryWords31 q a (b*m) .Y).card)
    (iB : Fin (boundaryFactor31 q a (b*m) .Y))
    (iC : Fin (boundaryFactor31 q a (b*m) .Z))
    (t : Fin (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat) :
    levOf (boundaryOccurrenceY31 q a (b*m) hY iB iC t) = coord .Y a.2.2.1 := by
  unfold boundaryOccurrenceY31 boundaryFirstWord31
  split_ifs with hB hC
  · exact boundaryPartnerWord_level31 q a (b*m) .Z .X .Y (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hB.1 _ t
  · exact boundaryWordAt31_level _ _ _ _ _ _
  · exact boundaryWordAt31_level _ _ _ _ _ _

private theorem boundaryOccurrenceY31_emp (q b m : ℕ) (a : ℚ × AtomKey)
    (hY : 0 < (boundaryWords31 q a (b*m) .Y).card)
    (hI : BoundaryInventoryAdmissible [a] b)
    (iB : Fin (boundaryFactor31 q a (b*m) .Y))
    (iC : Fin (boundaryFactor31 q a (b*m) .Z))
    (hk : (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat ≠ 0) (σ : Chunk a.2.1) :
    emp (chunkSeq (boundaryOccurrenceY31 q a (b*m) hY iB iC)) σ = a.2.2.2 .Y σ := by
  unfold boundaryOccurrenceY31 boundaryFirstWord31
  split_ifs with hB hC
  · exact boundaryPartnerWord_emp31 q b m a .Z .X .Y (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hB.1 hI _ hk σ
  · exact boundaryWordAt31_emp _ _ _ _ _ hk σ
  · exact boundaryWordAt31_emp _ _ _ _ _ hk σ

private theorem boundaryOccurrenceZ31_level (q b m : ℕ) (a : ℚ × AtomKey)
    (hZ : 0 < (boundaryWords31 q a (b*m) .Z).card)
    (iC : Fin (boundaryFactor31 q a (b*m) .Z))
    (iA : Fin (boundaryFactor31 q a (b*m) .X))
    (t : Fin (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat) :
    levOf (boundaryOccurrenceZ31 q a (b*m) hZ iC iA t) = coord .Z a.2.2.1 := by
  unfold boundaryOccurrenceZ31 boundaryFirstWord31
  split_ifs with hA hC
  · exact boundaryPartnerWord_level31 q a (b*m) .Y .X .Z (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hA.1 _ t
  · exact boundaryPartnerWord_level31 q a (b*m) .X .Y .Z (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hC.1 _ t
  · exact boundaryWordAt31_level _ _ _ _ _ _

private theorem boundaryOccurrenceZ31_emp (q b m : ℕ) (a : ℚ × AtomKey)
    (hZ : 0 < (boundaryWords31 q a (b*m) .Z).card)
    (hI : BoundaryInventoryAdmissible [a] b)
    (iC : Fin (boundaryFactor31 q a (b*m) .Z))
    (iA : Fin (boundaryFactor31 q a (b*m) .X))
    (hk : (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat ≠ 0) (σ : Chunk a.2.1) :
    emp (chunkSeq (boundaryOccurrenceZ31 q a (b*m) hZ iC iA)) σ = a.2.2.2 .Z σ := by
  unfold boundaryOccurrenceZ31 boundaryFirstWord31
  split_ifs with hA hC
  · exact boundaryPartnerWord_emp31 q b m a .Y .X .Z (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hA.1 hI _ hk σ
  · exact boundaryPartnerWord_emp31 q b m a .X .Y .Z (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hC.1 hI _ hk σ
  · exact boundaryWordAt31_emp _ _ _ _ _ hk σ

private theorem boundaryWords_card_kzero31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (W : Side) (hk : (a.1 * (n : ℚ)).floor.toNat = 0) :
    (boundaryWords31 q a n W).card = 1 := by
  have hw : boundaryWords31 q a n W = Finset.univ := by
    ext x
    rw [boundaryWords31, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, iff_true]
    exact ⟨fun t => (Fin.cast hk t).elim0, Or.inl hk⟩
  rw [hw]
  rw [Finset.card_univ, Fintype.card_fun]
  simp [hk]

private theorem boundary_fin_eq_of_card_one31 {n : ℕ} (hn : n = 1) (i j : Fin n) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

private theorem boundaryOccurrenceTensor31 (q b m : ℕ) (a : ℚ × AtomKey)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b) (ε : ℚ) (hε : 0 ≤ ε)
    (iA₁ iA₂ : Fin (boundaryFactor31 q a (b*m) .X))
    (iB₁ iB₂ : Fin (boundaryFactor31 q a (b*m) .Y))
    (iC₁ iC₂ : Fin (boundaryFactor31 q a (b*m) .Z)) :
    let hX := boundary_words_pos_restrict31 q b m a .X hq hI
    let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
    let hZ := boundary_words_pos_restrict31 q b m a .Z hq hI
    let x := boundaryOccurrenceX31 q a (b*m) hX iA₁ iB₁
    let y := boundaryOccurrenceY31 q a (b*m) hY iB₂ iC₁
    let z := boundaryOccurrenceZ31 q a (b*m) hZ iC₂ iA₂
    (if (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat = 0 then 1 else
      if (∀ σ, |emp (chunkSeq x) σ - a.2.2.2 .X σ| ≤ ε) ∧
         (∀ σ, |emp (chunkSeq y) σ - a.2.2.2 .Y σ| ≤ ε) ∧
         (∀ σ, |emp (chunkSeq z) σ - a.2.2.2 .Z σ| ≤ ε)
      then tensorPower
        (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
          (coord .Z a.2.2.1))
        (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat x y z
      else 0) = if iB₁ = iB₂ ∧ iC₁ = iC₂ ∧ iA₁ = iA₂ then 1 else 0 := by
  dsimp only
  let hX := boundary_words_pos_restrict31 q b m a .X hq hI
  let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
  let hZ := boundary_words_pos_restrict31 q b m a .Z hq hI
  let x := boundaryOccurrenceX31 q a (b*m) hX iA₁ iB₁
  let y := boundaryOccurrenceY31 q a (b*m) hY iB₂ iC₁
  let z := boundaryOccurrenceZ31 q a (b*m) hZ iC₂ iA₂
  let k := (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat
  by_cases hk : k = 0
  · have hcard (W : Side) : (boundaryWords31 q a (b*m) W).card = 1 :=
      boundaryWords_card_kzero31 q a (b*m) W hk
    have hfac (W : Side) : boundaryFactor31 q a (b*m) W = 1 := by
      simp [boundaryFactor31, hcard]
    have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31 (hfac .X) _ _
    have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31 (hfac .Y) _ _
    have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31 (hfac .Z) _ _
    simp only [k] at hk
    rw [if_pos hk, if_pos ⟨hiB, hiC, hiA⟩]
  · have hxemp : ∀ σ, |emp (chunkSeq x) σ - a.2.2.2 .X σ| ≤ ε := by
      intro σ
      rw [boundaryOccurrenceX31_emp q b m a hX iA₁ iB₁ hk σ, sub_self, abs_zero]
      exact hε
    have hyemp : ∀ σ, |emp (chunkSeq y) σ - a.2.2.2 .Y σ| ≤ ε := by
      intro σ
      rw [boundaryOccurrenceY31_emp q b m a hY hI iB₂ iC₁ hk σ, sub_self, abs_zero]
      exact hε
    have hzemp : ∀ σ, |emp (chunkSeq z) σ - a.2.2.2 .Z σ| ≤ ε := by
      intro σ
      rw [boundaryOccurrenceZ31_emp q b m a hZ hI iC₂ iA₂ hk σ, sub_self, abs_zero]
      exact hε
    rw [if_neg hk, if_pos ⟨hxemp, hyemp, hzemp⟩]
    have hxlev : ∀ t, levOf (x t) = coord .X a.2.2.1 :=
      boundaryOccurrenceX31_level q b m a hX iA₁ iB₁
    have hylev : ∀ t, levOf (y t) = coord .Y a.2.2.1 := by
      exact boundaryOccurrenceY31_level q b m a hY iB₂ iC₁
    have hzlev : ∀ t, levOf (z t) = coord .Z a.2.2.1 :=
      boundaryOccurrenceZ31_level q b m a hZ iC₂ iA₂
    have hcon : tensorPower
        (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
          (coord .Z a.2.2.1)) k x y z =
        tensorPower (tensorPower (cwZ q) a.2.1) k x y z := by
      unfold tensorPower
      apply Finset.prod_congr rfl
      intro t _ht
      unfold conZ zoP
      rw [if_pos ⟨hxlev t, hylev t, hzlev t⟩]
      rfl
    rw [hcon]
    have ha := hI a (by simp)
    rcases ha with ⟨_hmass, _hnonneg, _hsum, _hsupport, hzero, _hreflect,
      _hint, _hbetaInt⟩
    by_cases hA : boundaryActive31 a .X
    · have hnB : ¬ boundaryActive31 a .Y := by
        intro hB
        exact (Nat.ne_of_gt hA.2.2) hB.1
      have hnC : ¬ boundaryActive31 a .Z := by
        intro hC
        exact (Nat.ne_of_gt hA.2.1) hC.1
      have hyLow : y = boundaryLowWord31 := by
        funext t
        apply boundary_word_eq_low31
        rw [hylev t, hA.1]
      rw [hyLow]
      simp only [x, y, z, boundaryOccurrenceX31, boundaryOccurrenceY31,
        boundaryOccurrenceZ31, dif_pos hA, dif_neg hnB, dif_neg hnC]
      rw [boundary_cw_power_zeroY31]
      have hwiff :
          boundaryWordAt31 q a (b*m) .X
              (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hA]) iA₁) =
            boundaryWordAt31 q a (b*m) .X
              (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hA]) iA₂) ↔
          iA₁ = iA₂ := by
        constructor
        · intro h
          exact Fin.cast_injective _ (boundaryWordAt31_injective q a (b*m) .X h)
        · rintro rfl
          rfl
      simp only [hwiff]
      have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryFactor31, hnB]) _ _
      have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryFactor31, hnC]) _ _
      simp [hiB, hiC]
    · by_cases hB : boundaryActive31 a .Y
      · have hnC : ¬ boundaryActive31 a .Z := by
          intro hC
          exact (Nat.ne_of_gt hB.2.1) hC.1
        have hzLow : z = boundaryLowWord31 := by
          funext t
          apply boundary_word_eq_low31
          rw [hzlev t, hB.1]
        rw [hzLow]
        simp only [x, y, z, boundaryOccurrenceX31, boundaryOccurrenceY31,
          boundaryOccurrenceZ31, dif_neg hA, dif_pos hB, dif_neg hnC]
        rw [boundary_cw_power_zeroZ31]
        have hwiff :
            boundaryWordAt31 q a (b*m) .X
                (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hB]) iB₁) =
              boundaryWordAt31 q a (b*m) .X
                (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hB]) iB₂) ↔
            iB₁ = iB₂ := by
          constructor
          · intro h
            exact Fin.cast_injective _ (boundaryWordAt31_injective q a (b*m) .X h)
          · rintro rfl
            rfl
        simp only [hwiff]
        have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31
          (by simp [boundaryFactor31, hA]) _ _
        have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31
          (by simp [boundaryFactor31, hnC]) _ _
        simp [hiA, hiC]
      · by_cases hC : boundaryActive31 a .Z
        · have hxLow : x = boundaryLowWord31 := by
            funext t
            apply boundary_word_eq_low31
            rw [hxlev t, hC.1]
          rw [hxLow]
          simp only [x, y, z, boundaryOccurrenceX31, boundaryOccurrenceY31,
            boundaryOccurrenceZ31, dif_neg hA, dif_neg hB, dif_pos hC]
          rw [boundary_cw_power_zeroX31]
          have hwiff :
              boundaryWordAt31 q a (b*m) .Y
                  (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hC]) iC₁) =
                boundaryWordAt31 q a (b*m) .Y
                  (Fin.cast (by simp [boundaryFactor31, boundaryReadingSide31, hC]) iC₂) ↔
              iC₁ = iC₂ := by
            constructor
            · intro h
              exact Fin.cast_injective _ (boundaryWordAt31_injective q a (b*m) .Y h)
            · rintro rfl
              rfl
          simp only [hwiff]
          have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hA]) _ _
          have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hB]) _ _
          simp [hiA, hiB]
        · have hpair :
              (coord .X a.2.2.1 = 0 ∧ coord .Y a.2.2.1 = 0) ∨
              (coord .X a.2.2.1 = 0 ∧ coord .Z a.2.2.1 = 0) ∨
              (coord .Y a.2.2.1 = 0 ∧ coord .Z a.2.2.1 = 0) := by
            have hz : coord .X a.2.2.1 = 0 ∨ coord .Y a.2.2.1 = 0 ∨
                coord .Z a.2.2.1 = 0 := by
              rcases hzero with ⟨W, hW⟩
              fin_cases W
              · exact Or.inl hW
              · exact Or.inr (Or.inl hW)
              · exact Or.inr (Or.inr hW)
            rcases hz with hx | hy | hz
            · by_cases hy0 : coord .Y a.2.2.1 = 0
              · exact Or.inl ⟨hx, hy0⟩
              · by_cases hz0 : coord .Z a.2.2.1 = 0
                · exact Or.inr (Or.inl ⟨hx, hz0⟩)
                · exfalso
                  exact hC ⟨hx, Nat.pos_of_ne_zero hy0, Nat.pos_of_ne_zero hz0⟩
            · by_cases hx0 : coord .X a.2.2.1 = 0
              · exact Or.inl ⟨hx0, hy⟩
              · by_cases hz0 : coord .Z a.2.2.1 = 0
                · exact Or.inr (Or.inr ⟨hy, hz0⟩)
                · exfalso
                  exact hA ⟨hy, Nat.pos_of_ne_zero hx0, Nat.pos_of_ne_zero hz0⟩
            · by_cases hx0 : coord .X a.2.2.1 = 0
              · exact Or.inr (Or.inl ⟨hx0, hz⟩)
              · by_cases hy0 : coord .Y a.2.2.1 = 0
                · exact Or.inr (Or.inr ⟨hy0, hz⟩)
                · exfalso
                  exact hB ⟨hz, Nat.pos_of_ne_zero hx0, Nat.pos_of_ne_zero hy0⟩
          rw [boundary_cw_power_unit31 x y z _ _ _ hxlev hylev hzlev
            a.2.2.1.property hpair]
          have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hA]) _ _
          have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hB]) _ _
          have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hC]) _ _
          rw [if_pos ⟨hiB, hiC, hiA⟩]

private noncomputable def boundaryInventoryX31 (q b m : ℕ) (I : Inventory) (ε : ℚ)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .X) → Fin (boundaryDimension31 q I (b*m) .Y) →
      (inventoryTensorZ q I (b*m) ε).X := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hX := boundary_words_pos_restrict31 q b m a .X hq ha
      intro iA iB
      let sA : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iA)
      let sB : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iB)
      exact (boundaryOccurrenceX31 q a (b*m) hX sA.1 sB.1, ih ht sA.2 sB.2)

private noncomputable def boundaryInventoryY31 (q b m : ℕ) (I : Inventory) (ε : ℚ)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .Y) → Fin (boundaryDimension31 q I (b*m) .Z) →
      (inventoryTensorZ q I (b*m) ε).Y := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hY := boundary_words_pos_restrict31 q b m a .Y hq ha
      intro iB iC
      let sB : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iB)
      let sC : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iC)
      exact (boundaryOccurrenceY31 q a (b*m) hY sB.1 sC.1, ih ht sB.2 sC.2)

private noncomputable def boundaryInventoryZ31 (q b m : ℕ) (I : Inventory) (ε : ℚ)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .Z) → Fin (boundaryDimension31 q I (b*m) .X) →
      (inventoryTensorZ q I (b*m) ε).Z := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hZ := boundary_words_pos_restrict31 q b m a .Z hq ha
      intro iC iA
      let sC : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iC)
      let sA : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast (by simp [boundaryDimension31, boundaryFactor31]) iA)
      exact (boundaryOccurrenceZ31 q a (b*m) hZ sC.1 sA.1, ih ht sC.2 sA.2)

private theorem boundaryInventory_apply31 (q b m : ℕ) (I : Inventory) (ε : ℚ)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) (hε : 0 ≤ ε) :
    ∀ (iA₁ iA₂ : Fin (boundaryDimension31 q I (b*m) .X))
      (iB₁ iB₂ : Fin (boundaryDimension31 q I (b*m) .Y))
      (iC₁ iC₂ : Fin (boundaryDimension31 q I (b*m) .Z)),
      (inventoryTensorZ q I (b*m) ε).tensor
          (boundaryInventoryX31 q b m I ε hq hI iA₁ iB₁)
          (boundaryInventoryY31 q b m I ε hq hI iB₂ iC₁)
          (boundaryInventoryZ31 q b m I ε hq hI iC₂ iA₂) =
        (matMulZ (boundaryDimension31 q I (b*m) .X)
          (boundaryDimension31 q I (b*m) .Y)
          (boundaryDimension31 q I (b*m) .Z)).tensor
            (iA₁, iB₁) (iB₂, iC₁) (iC₂, iA₂) := by
  induction I with
  | nil =>
      intro iA₁ iA₂ iB₁ iB₂ iC₁ iC₂
      have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      simp [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ,
        boundaryInventoryX31, boundaryInventoryY31, boundaryInventoryZ31,
        boundaryDimension31, matMulZ, hiA, hiB, hiC]
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hX := boundary_words_pos_restrict31 q b m a .X hq ha
      have hY := boundary_words_pos_restrict31 q b m a .Y hq ha
      have hZ := boundary_words_pos_restrict31 q b m a .Z hq ha
      intro iA₁ iA₂ iB₁ iB₂ iC₁ iC₂
      have hdimX : boundaryDimension31 q (a :: I) (b*m) .X =
          boundaryFactor31 q a (b*m) .X * boundaryDimension31 q I (b*m) .X := by
        simp [boundaryDimension31, boundaryFactor31]
      have hdimY : boundaryDimension31 q (a :: I) (b*m) .Y =
          boundaryFactor31 q a (b*m) .Y * boundaryDimension31 q I (b*m) .Y := by
        simp [boundaryDimension31, boundaryFactor31]
      have hdimZ : boundaryDimension31 q (a :: I) (b*m) .Z =
          boundaryFactor31 q a (b*m) .Z * boundaryDimension31 q I (b*m) .Z := by
        simp [boundaryDimension31, boundaryFactor31]
      let sA₁ : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast hdimX iA₁)
      let sA₂ : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast hdimX iA₂)
      let sB₁ : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast hdimY iB₁)
      let sB₂ : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast hdimY iB₂)
      let sC₁ : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast hdimZ iC₁)
      let sC₂ : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast hdimZ iC₂)
      have hhead := boundaryOccurrenceTensor31 q b m a hq ha ε hε
        sA₁.1 sA₂.1 sB₁.1 sB₂.1 sC₁.1 sC₂.1
      have htail := ih ht sA₁.2 sA₂.2 sB₁.2 sB₂.2 sC₁.2 sC₂.2
      have hxdef :
          boundaryInventoryX31 q b m (a :: I) ε hq hI iA₁ iB₁ =
            (boundaryOccurrenceX31 q a (b*m) hX sA₁.1 sB₁.1,
              boundaryInventoryX31 q b m I ε hq ht sA₁.2 sB₁.2) := by
        rfl
      have hydef :
          boundaryInventoryY31 q b m (a :: I) ε hq hI iB₂ iC₁ =
            (boundaryOccurrenceY31 q a (b*m) hY sB₂.1 sC₁.1,
              boundaryInventoryY31 q b m I ε hq ht sB₂.2 sC₁.2) := by
        rfl
      have hzdef :
          boundaryInventoryZ31 q b m (a :: I) ε hq hI iC₂ iA₂ =
            (boundaryOccurrenceZ31 q a (b*m) hZ sC₂.1 sA₂.1,
              boundaryInventoryZ31 q b m I ε hq ht sC₂.2 sA₂.2) := by
        rfl
      have hAi : iA₁ = iA₂ ↔ sA₁.1 = sA₂.1 ∧ sA₁.2 = sA₂.2 := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨h₁, h₂⟩
          have hs : sA₁ = sA₂ := Prod.ext h₁ h₂
          apply Fin.cast_injective hdimX
          calc
            Fin.cast hdimX iA₁ = finProdFinEquiv sA₁ := by
              dsimp only [sA₁]
              exact (finProdFinEquiv.apply_symm_apply _).symm
            _ = finProdFinEquiv sA₂ := congrArg (fun p => finProdFinEquiv p) hs
            _ = Fin.cast hdimX iA₂ := by
              dsimp only [sA₂]
              exact finProdFinEquiv.apply_symm_apply _
      have hBi : iB₁ = iB₂ ↔ sB₁.1 = sB₂.1 ∧ sB₁.2 = sB₂.2 := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨h₁, h₂⟩
          have hs : sB₁ = sB₂ := Prod.ext h₁ h₂
          apply Fin.cast_injective hdimY
          calc
            Fin.cast hdimY iB₁ = finProdFinEquiv sB₁ := by
              dsimp only [sB₁]
              exact (finProdFinEquiv.apply_symm_apply _).symm
            _ = finProdFinEquiv sB₂ := congrArg (fun p => finProdFinEquiv p) hs
            _ = Fin.cast hdimY iB₂ := by
              dsimp only [sB₂]
              exact finProdFinEquiv.apply_symm_apply _
      have hCi : iC₁ = iC₂ ↔ sC₁.1 = sC₂.1 ∧ sC₁.2 = sC₂.2 := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨h₁, h₂⟩
          have hs : sC₁ = sC₂ := Prod.ext h₁ h₂
          apply Fin.cast_injective hdimZ
          calc
            Fin.cast hdimZ iC₁ = finProdFinEquiv sC₁ := by
              dsimp only [sC₁]
              exact (finProdFinEquiv.apply_symm_apply _).symm
            _ = finProdFinEquiv sC₂ := congrArg (fun p => finProdFinEquiv p) hs
            _ = Fin.cast hdimZ iC₂ := by
              dsimp only [sC₂]
              exact finProdFinEquiv.apply_symm_apply _
      simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ]
      rw [hxdef, hydef, hzdef]
      simp only [Prod.fst, Prod.snd]
      change _ * _ = _
      rw [hhead]
      change _ * (inventoryTensorZ q I (b*m) ε).tensor
          (boundaryInventoryX31 q b m I ε hq ht sA₁.2 sB₁.2)
          (boundaryInventoryY31 q b m I ε hq ht sB₂.2 sC₁.2)
          (boundaryInventoryZ31 q b m I ε hq ht sC₂.2 sA₂.2) = _
      rw [htail]
      simp only [matMulZ, hAi, hBi, hCi]
      split_ifs <;> simp_all

/-- Paper clauses:
`P/prelim.tex:181–200,267–278` and `P/constituent.tex:17–21,28–39`. -/
theorem boundary_matrix_restrict31 (q b m : ℕ) (I : Inventory) (ε : ℚ)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) (hε : 0 ≤ ε) :
  Restricts (boundaryMatrixZ q I (b*m)).tensor
    (inventoryTensorZ q I (b*m) ε).tensor := by
  let fX := fun x : (boundaryMatrixZ q I (b*m)).X =>
    boundaryInventoryX31 q b m I ε hq hI x.1 x.2
  let fY := fun y : (boundaryMatrixZ q I (b*m)).Y =>
    boundaryInventoryY31 q b m I ε hq hI y.1 y.2
  let fZ := fun z : (boundaryMatrixZ q I (b*m)).Z =>
    boundaryInventoryZ31 q b m I ε hq hI z.1 z.2
  have hpre :
      (fun x y z => (inventoryTensorZ q I (b*m) ε).tensor (fX x) (fY y) (fZ z)) ≤ₜ
        (inventoryTensorZ q I (b*m) ε).tensor :=
    precomp_restricts fX fY fZ (inventoryTensorZ q I (b*m) ε).tensor
  refine Restricts.of_eq hpre ?_
  funext x y z
  rcases x with ⟨iA₁, iB₁⟩
  rcases y with ⟨iB₂, iC₁⟩
  rcases z with ⟨iC₂, iA₂⟩
  exact (boundaryInventory_apply31 q b m I ε hq hI hε
    iA₁ iA₂ iB₁ iB₂ iC₁ iC₂).symm

private theorem boundary_emp_support31 {q w k : ℕ}
    (x : Fin k → Fin w → CW90.Idx7 q) (beta : Chunk w → ℚ)
    (hk : 0 < k) (hemp : ∀ σ, emp (chunkSeq x) σ = beta σ) (t : Fin k) :
    beta (chunkOf (x t)) ≠ 0 := by
  change beta (chunkSeq x t) ≠ 0
  intro hzero
  have he := hemp (chunkSeq x t)
  change (typeCnt (chunkSeq x) (chunkSeq x t) : ℚ) / (k : ℚ) =
    beta (chunkSeq x t) at he
  rw [hzero] at he
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  rw [div_eq_iff hkq] at he
  have hc0 : typeCnt (chunkSeq x) (chunkSeq x t) = 0 := by
    exact_mod_cast (by simpa using he)
  have hpos : 0 < typeCnt (chunkSeq x) (chunkSeq x t) := by
    rw [typeCnt, Finset.card_pos]
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  omega

private theorem boundaryOccurrenceSupportedTensor31 (q b m : ℕ)
    (a : ℚ × AtomKey) (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b)
    (ε : ℚ) (hε : 0 ≤ ε)
    (iA₁ iA₂ : Fin (boundaryFactor31 q a (b*m) .X))
    (iB₁ iB₂ : Fin (boundaryFactor31 q a (b*m) .Y))
    (iC₁ iC₂ : Fin (boundaryFactor31 q a (b*m) .Z)) :
    let hX := boundary_words_pos_restrict31 q b m a .X hq hI
    let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
    let hZ := boundary_words_pos_restrict31 q b m a .Z hq hI
    let x := boundaryOccurrenceX31 q a (b*m) hX iA₁ iB₁
    let y := boundaryOccurrenceY31 q a (b*m) hY iB₂ iC₁
    let z := boundaryOccurrenceZ31 q a (b*m) hZ iC₂ iA₂
    (if (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat = 0 then 1 else
      if ( (∀ σ, |emp (chunkSeq x) σ - a.2.2.2 .X σ| ≤ ε) ∧
           (∀ σ, |emp (chunkSeq y) σ - a.2.2.2 .Y σ| ≤ ε) ∧
           (∀ σ, |emp (chunkSeq z) σ - a.2.2.2 .Z σ| ≤ ε) ∧
           (∀ t, a.2.2.2 .X (chunkOf (x t)) ≠ 0) ∧
           (∀ t, a.2.2.2 .Y (chunkOf (y t)) ≠ 0) ∧
           (∀ t, a.2.2.2 .Z (chunkOf (z t)) ≠ 0) )
      then tensorPower
        (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
          (coord .Z a.2.2.1))
        (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat x y z
      else 0) = if iB₁ = iB₂ ∧ iC₁ = iC₂ ∧ iA₁ = iA₂ then 1 else 0 := by
  dsimp only
  let hX := boundary_words_pos_restrict31 q b m a .X hq hI
  let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
  let hZ := boundary_words_pos_restrict31 q b m a .Z hq hI
  let x := boundaryOccurrenceX31 q a (b*m) hX iA₁ iB₁
  let y := boundaryOccurrenceY31 q a (b*m) hY iB₂ iC₁
  let z := boundaryOccurrenceZ31 q a (b*m) hZ iC₂ iA₂
  let k := (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat
  by_cases hk : k = 0
  · have hcard (W : Side) : (boundaryWords31 q a (b*m) W).card = 1 :=
      boundaryWords_card_kzero31 q a (b*m) W hk
    have hfac (W : Side) : boundaryFactor31 q a (b*m) W = 1 := by
      simp [boundaryFactor31, hcard]
    have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31 (hfac .X) _ _
    have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31 (hfac .Y) _ _
    have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31 (hfac .Z) _ _
    simp only [k] at hk
    rw [if_pos hk, if_pos ⟨hiB, hiC, hiA⟩]
  · simp only [k] at hk
    have hxemp : ∀ σ, emp (chunkSeq x) σ = a.2.2.2 .X σ :=
      fun σ => boundaryOccurrenceX31_emp q b m a hX iA₁ iB₁ hk σ
    have hyemp : ∀ σ, emp (chunkSeq y) σ = a.2.2.2 .Y σ :=
      fun σ => boundaryOccurrenceY31_emp q b m a hY hI iB₂ iC₁ hk σ
    have hzemp : ∀ σ, emp (chunkSeq z) σ = a.2.2.2 .Z σ :=
      fun σ => boundaryOccurrenceZ31_emp q b m a hZ hI iC₂ iA₂ hk σ
    have hxapprox : ∀ σ, |emp (chunkSeq x) σ - a.2.2.2 .X σ| ≤ ε := by
      intro σ
      rw [hxemp σ, sub_self, abs_zero]
      exact hε
    have hyapprox : ∀ σ, |emp (chunkSeq y) σ - a.2.2.2 .Y σ| ≤ ε := by
      intro σ
      rw [hyemp σ, sub_self, abs_zero]
      exact hε
    have hzapprox : ∀ σ, |emp (chunkSeq z) σ - a.2.2.2 .Z σ| ≤ ε := by
      intro σ
      rw [hzemp σ, sub_self, abs_zero]
      exact hε
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hxsupport : ∀ t, a.2.2.2 .X (chunkOf (x t)) ≠ 0 :=
      boundary_emp_support31 x (a.2.2.2 .X) hkpos hxemp
    have hysupport : ∀ t, a.2.2.2 .Y (chunkOf (y t)) ≠ 0 :=
      boundary_emp_support31 y (a.2.2.2 .Y) hkpos hyemp
    have hzsupport : ∀ t, a.2.2.2 .Z (chunkOf (z t)) ≠ 0 :=
      boundary_emp_support31 z (a.2.2.2 .Z) hkpos hzemp
    rw [if_neg hk, if_pos ⟨hxapprox, hyapprox, hzapprox, hxsupport, hysupport,
      hzsupport⟩]
    have hp := boundaryOccurrenceTensor31 q b m a hq hI ε hε
      iA₁ iA₂ iB₁ iB₂ iC₁ iC₂
    dsimp only at hp
    rw [if_neg hk, if_pos ⟨hxapprox, hyapprox, hzapprox⟩] at hp
    exact hp

private noncomputable def boundarySupportedInventoryX31 (q b m : ℕ)
    (I : Inventory) (ε : ℚ) (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .X) → Fin (boundaryDimension31 q I (b*m) .Y) →
      (supportedInventoryTensorZ q I (b*m) ε).X := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hX := boundary_words_pos_restrict31 q b m a .X hq ha
      intro iA iB
      let sA : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iA)
      let sB : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iB)
      exact (boundaryOccurrenceX31 q a (b*m) hX sA.1 sB.1, ih ht sA.2 sB.2)

private noncomputable def boundarySupportedInventoryY31 (q b m : ℕ)
    (I : Inventory) (ε : ℚ) (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .Y) → Fin (boundaryDimension31 q I (b*m) .Z) →
      (supportedInventoryTensorZ q I (b*m) ε).Y := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hY := boundary_words_pos_restrict31 q b m a .Y hq ha
      intro iB iC
      let sB : Fin (boundaryFactor31 q a (b*m) .Y) ×
          Fin (boundaryDimension31 q I (b*m) .Y) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iB)
      let sC : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iC)
      exact (boundaryOccurrenceY31 q a (b*m) hY sB.1 sC.1, ih ht sB.2 sC.2)

private noncomputable def boundarySupportedInventoryZ31 (q b m : ℕ)
    (I : Inventory) (ε : ℚ) (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Fin (boundaryDimension31 q I (b*m) .Z) → Fin (boundaryDimension31 q I (b*m) .X) →
      (supportedInventoryTensorZ q I (b*m) ε).Z := by
  induction I with
  | nil => exact fun _ _ => PUnit.unit
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hZ := boundary_words_pos_restrict31 q b m a .Z hq ha
      intro iC iA
      let sC : Fin (boundaryFactor31 q a (b*m) .Z) ×
          Fin (boundaryDimension31 q I (b*m) .Z) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iC)
      let sA : Fin (boundaryFactor31 q a (b*m) .X) ×
          Fin (boundaryDimension31 q I (b*m) .X) :=
        finProdFinEquiv.symm (Fin.cast (by
          simp [boundaryDimension31, boundaryFactor31]) iA)
      exact (boundaryOccurrenceZ31 q a (b*m) hZ sC.1 sA.1, ih ht sC.2 sA.2)

private theorem fin_eq_iff_boundarySplit31 {n r s : ℕ} (h : n = r*s)
    (i j : Fin n) :
    i = j ↔
      (finProdFinEquiv.symm (Fin.cast h i)).1 =
          (finProdFinEquiv.symm (Fin.cast h j)).1 ∧
        (finProdFinEquiv.symm (Fin.cast h i)).2 =
          (finProdFinEquiv.symm (Fin.cast h j)).2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    have hs : finProdFinEquiv.symm (Fin.cast h i) =
        finProdFinEquiv.symm (Fin.cast h j) := Prod.ext h₁ h₂
    apply Fin.cast_injective h
    calc
      Fin.cast h i = finProdFinEquiv (finProdFinEquiv.symm (Fin.cast h i)) :=
        (finProdFinEquiv.apply_symm_apply _).symm
      _ = finProdFinEquiv (finProdFinEquiv.symm (Fin.cast h j)) :=
        congrArg (fun p => finProdFinEquiv p) hs
      _ = Fin.cast h j := finProdFinEquiv.apply_symm_apply _

private theorem boundary_indicator_product31 (A B C D E F : Prop)
    [Decidable A] [Decidable B] [Decidable C] [Decidable D] [Decidable E]
    [Decidable F] :
    (if A ∧ C ∧ E then (1 : ℤ) else 0) *
        (if B ∧ D ∧ F then 1 else 0) =
      if (A ∧ B) ∧ (C ∧ D) ∧ (E ∧ F) then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    by_cases hD : D <;> by_cases hE : E <;> by_cases hF : F <;> simp [*]

private theorem boundarySupportedInventory_apply31 (q b m : ℕ) (I : Inventory)
    (ε : ℚ) (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) (hε : 0 ≤ ε) :
    ∀ (iA₁ iA₂ : Fin (boundaryDimension31 q I (b*m) .X))
      (iB₁ iB₂ : Fin (boundaryDimension31 q I (b*m) .Y))
      (iC₁ iC₂ : Fin (boundaryDimension31 q I (b*m) .Z)),
      (supportedInventoryTensorZ q I (b*m) ε).tensor
          (boundarySupportedInventoryX31 q b m I ε hq hI iA₁ iB₁)
          (boundarySupportedInventoryY31 q b m I ε hq hI iB₂ iC₁)
          (boundarySupportedInventoryZ31 q b m I ε hq hI iC₂ iA₂) =
        (matMulZ (boundaryDimension31 q I (b*m) .X)
          (boundaryDimension31 q I (b*m) .Y)
          (boundaryDimension31 q I (b*m) .Z)).tensor
            (iA₁, iB₁) (iB₂, iC₁) (iC₂, iA₂) := by
  induction I with
  | nil =>
      intro iA₁ iA₂ iB₁ iB₂ iC₁ iC₂
      have hiA : iA₁ = iA₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      have hiB : iB₁ = iB₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      have hiC : iC₁ = iC₂ := boundary_fin_eq_of_card_one31
        (by simp [boundaryDimension31]) _ _
      simp [supportedInventoryTensorZ, boundarySupportedInventoryX31,
        boundarySupportedInventoryY31, boundarySupportedInventoryZ31,
        boundaryDimension31, matMulZ, hiA, hiB, hiC]
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hX := boundary_words_pos_restrict31 q b m a .X hq ha
      have hY := boundary_words_pos_restrict31 q b m a .Y hq ha
      have hZ := boundary_words_pos_restrict31 q b m a .Z hq ha
      intro iA₁ iA₂ iB₁ iB₂ iC₁ iC₂
      have hdimX : boundaryDimension31 q (a :: I) (b*m) .X =
          boundaryFactor31 q a (b*m) .X * boundaryDimension31 q I (b*m) .X := by
        simp [boundaryDimension31, boundaryFactor31]
      have hdimY : boundaryDimension31 q (a :: I) (b*m) .Y =
          boundaryFactor31 q a (b*m) .Y * boundaryDimension31 q I (b*m) .Y := by
        simp [boundaryDimension31, boundaryFactor31]
      have hdimZ : boundaryDimension31 q (a :: I) (b*m) .Z =
          boundaryFactor31 q a (b*m) .Z * boundaryDimension31 q I (b*m) .Z := by
        simp [boundaryDimension31, boundaryFactor31]
      let sA₁ := finProdFinEquiv.symm (Fin.cast hdimX iA₁)
      let sA₂ := finProdFinEquiv.symm (Fin.cast hdimX iA₂)
      let sB₁ := finProdFinEquiv.symm (Fin.cast hdimY iB₁)
      let sB₂ := finProdFinEquiv.symm (Fin.cast hdimY iB₂)
      let sC₁ := finProdFinEquiv.symm (Fin.cast hdimZ iC₁)
      let sC₂ := finProdFinEquiv.symm (Fin.cast hdimZ iC₂)
      have hhead := boundaryOccurrenceSupportedTensor31 q b m a hq ha ε hε
        sA₁.1 sA₂.1 sB₁.1 sB₂.1 sC₁.1 sC₂.1
      have htail := ih ht sA₁.2 sA₂.2 sB₁.2 sB₂.2 sC₁.2 sC₂.2
      have hxdef :
          boundarySupportedInventoryX31 q b m (a :: I) ε hq hI iA₁ iB₁ =
            (boundaryOccurrenceX31 q a (b*m) hX sA₁.1 sB₁.1,
              boundarySupportedInventoryX31 q b m I ε hq ht sA₁.2 sB₁.2) := by
        rfl
      have hydef :
          boundarySupportedInventoryY31 q b m (a :: I) ε hq hI iB₂ iC₁ =
            (boundaryOccurrenceY31 q a (b*m) hY sB₂.1 sC₁.1,
              boundarySupportedInventoryY31 q b m I ε hq ht sB₂.2 sC₁.2) := by
        rfl
      have hzdef :
          boundarySupportedInventoryZ31 q b m (a :: I) ε hq hI iC₂ iA₂ =
            (boundaryOccurrenceZ31 q a (b*m) hZ sC₂.1 sA₂.1,
              boundarySupportedInventoryZ31 q b m I ε hq ht sC₂.2 sA₂.2) := by
        rfl
      have hAi := fin_eq_iff_boundarySplit31 hdimX iA₁ iA₂
      have hBi := fin_eq_iff_boundarySplit31 hdimY iB₁ iB₂
      have hCi := fin_eq_iff_boundarySplit31 hdimZ iC₁ iC₂
      simp only [supportedInventoryTensorZ]
      rw [hxdef, hydef, hzdef]
      simp only [Prod.fst, Prod.snd]
      change _ * _ = _
      rw [hhead, htail]
      simp only [matMulZ, hAi, hBi, hCi]
      exact boundary_indicator_product31
        (sB₁.1 = sB₂.1) (sB₁.2 = sB₂.2)
        (sC₁.1 = sC₂.1) (sC₁.2 = sC₂.2)
        (sA₁.1 = sA₂.1) (sA₁.2 = sA₂.2)

/-- Transparent (`def`) form of this restriction. -/
noncomputable def boundaryMatrixSupportedRestriction31 (q b m : ℕ)
    (I : Inventory) (ε : ℚ) (hq : 0 < q)
    (hI : BoundaryInventoryAdmissible I b) (hε : 0 ≤ ε) :
    Restricts (boundaryMatrixZ q I (b*m)).tensor
      (supportedInventoryTensorZ q I (b*m) ε).tensor := by
  let fX := fun x : (boundaryMatrixZ q I (b*m)).X =>
    boundarySupportedInventoryX31 q b m I ε hq hI x.1 x.2
  let fY := fun y : (boundaryMatrixZ q I (b*m)).Y =>
    boundarySupportedInventoryY31 q b m I ε hq hI y.1 y.2
  let fZ := fun z : (boundaryMatrixZ q I (b*m)).Z =>
    boundarySupportedInventoryZ31 q b m I ε hq hI z.1 z.2
  have hpre :
      (fun x y z => (supportedInventoryTensorZ q I (b*m) ε).tensor
        (fX x) (fY y) (fZ z)) ≤ₜ
        (supportedInventoryTensorZ q I (b*m) ε).tensor :=
    precomp_restricts fX fY fZ (supportedInventoryTensorZ q I (b*m) ε).tensor
  refine Restricts.of_eq hpre ?_
  funext x y z
  rcases x with ⟨iA₁, iB₁⟩
  rcases y with ⟨iB₂, iC₁⟩
  rcases z with ⟨iC₂, iA₂⟩
  exact (boundarySupportedInventory_apply31 q b m I ε hq hI hε
    iA₁ iA₂ iB₁ iB₂ iC₁ iC₂).symm

private noncomputable def boundaryWordIndexOrZero31 (q : ℕ) (a : ℚ × AtomKey)
    (n : ℕ) (W : Side) (hpos : 0 < (boundaryWords31 q a n W).card)
    (x : Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q) :
    Fin (boundaryWords31 q a n W).card :=
  if hx : x ∈ boundaryWords31 q a n W then
    (boundaryWords31 q a n W).equivFin ⟨x, hx⟩
  else ⟨0, hpos⟩

private theorem boundaryWordIndexOrZero_eq_iff31 (q : ℕ) (a : ℚ × AtomKey)
    (n : ℕ) (W : Side) (hpos : 0 < (boundaryWords31 q a n W).card)
    (x y : Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q)
    (hx : x ∈ boundaryWords31 q a n W) (hy : y ∈ boundaryWords31 q a n W) :
    boundaryWordIndexOrZero31 q a n W hpos x =
        boundaryWordIndexOrZero31 q a n W hpos y ↔ x = y := by
  unfold boundaryWordIndexOrZero31
  simp only [dif_pos hx, dif_pos hy]
  constructor
  · intro h
    exact congrArg Subtype.val ((boundaryWords31 q a n W).equivFin.injective h)
  · rintro rfl
    rfl

private theorem boundary_mem_iff_emp31 (q b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hI : BoundaryInventoryAdmissible [a] b)
    (x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
      Fin a.2.1 → CW90.Idx7 q) :
    x ∈ boundaryWords31 q a (b*m) W ↔
      (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = 0 ∨
        ∀ σ, emp (chunkSeq x) σ = a.2.2.2 W σ := by
  have ha := hI a (by simp)
  rw [boundaryWords31, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    by_cases hk : (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = 0
    · constructor
      · intro t
        exact (Fin.cast hk t).elim0
      · exact Or.inl hk
    · have hemp : ∀ σ, emp (chunkSeq x) σ = a.2.2.2 W σ :=
        h.resolve_left hk
      constructor
      · intro t
        have hne := boundary_emp_support31 x (a.2.2.2 W)
          (Nat.pos_of_ne_zero hk) hemp t
        change chunkLvl (chunkSeq x t) = coord W a.2.2.1
        exact ha.2.2.2.1 W (chunkSeq x t) hne
      · exact Or.inr hemp

private theorem boundary_mem_iff_approx_zero31 (q b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hI : BoundaryInventoryAdmissible [a] b)
    (hk : (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat ≠ 0)
    (x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
      Fin a.2.1 → CW90.Idx7 q) :
    x ∈ boundaryWords31 q a (b*m) W ↔
      ∀ σ, |emp (chunkSeq x) σ - a.2.2.2 W σ| ≤ 0 := by
  rw [boundary_mem_iff_emp31 q b m a W hI x]
  simp only [hk, false_or, abs_nonpos_iff, sub_eq_zero]

private theorem boundary_partner_mem31 (q b m : ℕ) (a : ℚ × AtomKey)
    (Z U V : Side) (hUV : U ≠ V) (hUZ : U ≠ Z) (hVZ : V ≠ Z)
    (hz : coord Z a.2.2.1 = 0) (hI : BoundaryInventoryAdmissible [a] b)
    (x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
      Fin a.2.1 → CW90.Idx7 q)
    (hx : x ∈ boundaryWords31 q a (b*m) U) :
    boundaryWordPartner31 x ∈ boundaryWords31 q a (b*m) V := by
  rw [boundary_mem_iff_emp31 q b m a U hI x] at hx
  rw [boundary_mem_iff_emp31 q b m a V hI (boundaryWordPartner31 x)]
  rcases hx with hk | hemp
  · exact Or.inl hk
  · exact Or.inr fun σ => by
      have ha := hI a (by simp)
      have hreflect := ha.2.2.2.2.2.1 Z U V hUV hUZ hVZ hz (reflect σ)
      calc
        emp (chunkSeq (boundaryWordPartner31 x)) σ =
            emp (chunkSeq x) (reflect σ) := boundary_emp_partner31 x σ
        _ = a.2.2.2 U (reflect σ) := hemp _
        _ = a.2.2.2 V σ := by rw [hreflect, boundary_reflect_reflect31]

private noncomputable def boundaryActiveIndex31 (q : ℕ) (a : ℚ × AtomKey)
    (n : ℕ) (W : Side)
    (hpos : 0 < (boundaryWords31 q a n (boundaryReadingSide31 W)).card)
    (x : Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q) :
    Fin (boundaryFactor31 q a n W) :=
  if hW : boundaryActive31 a W then
    Fin.cast (by simp [boundaryFactor31, hW])
      (boundaryWordIndexOrZero31 q a n (boundaryReadingSide31 W) hpos x)
  else ⟨0, by simp [boundaryFactor31, hW]⟩

private theorem boundaryActiveIndex_eq_iff31 (q : ℕ) (a : ℚ × AtomKey)
    (n : ℕ) (W : Side) (hW : boundaryActive31 a W)
    (hpos : 0 < (boundaryWords31 q a n (boundaryReadingSide31 W)).card)
    (x y : Fin (a.1 * (n : ℚ)).floor.toNat → Fin a.2.1 → CW90.Idx7 q)
    (hx : x ∈ boundaryWords31 q a n (boundaryReadingSide31 W))
    (hy : y ∈ boundaryWords31 q a n (boundaryReadingSide31 W)) :
    boundaryActiveIndex31 q a n W hpos x =
        boundaryActiveIndex31 q a n W hpos y ↔ x = y := by
  unfold boundaryActiveIndex31
  simp only [dif_pos hW, Fin.cast_inj]
  exact boundaryWordIndexOrZero_eq_iff31 q a n (boundaryReadingSide31 W) hpos x y hx hy

private theorem boundary_matMulZ_apply31 (a b c : ℕ)
    (i i' : Fin a) (j j' : Fin b) (k k' : Fin c) :
    (matMulZ a b c).tensor (i, j) (j', k) (k', i') =
      if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := rfl

private theorem boundaryOccurrenceExactReverse31 (q b m : ℕ) (a : ℚ × AtomKey)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b)
    (x y z : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
      Fin a.2.1 → CW90.Idx7 q) :
    let hX := boundary_words_pos_restrict31 q b m a .X hq hI
    let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
    let AX := boundaryActiveIndex31 q a (b*m) .X hX x
    let AZ := boundaryActiveIndex31 q a (b*m) .X hX (boundaryWordPartner31 z)
    let BX := boundaryActiveIndex31 q a (b*m) .Y hX x
    let BY := boundaryActiveIndex31 q a (b*m) .Y hX (boundaryWordPartner31 y)
    let CY := boundaryActiveIndex31 q a (b*m) .Z hY y
    let CZ := boundaryActiveIndex31 q a (b*m) .Z hY (boundaryWordPartner31 z)
    (if (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = 0 then 1 else
      if (∀ σ, |emp (chunkSeq x) σ - a.2.2.2 .X σ| ≤ 0) ∧
         (∀ σ, |emp (chunkSeq y) σ - a.2.2.2 .Y σ| ≤ 0) ∧
         (∀ σ, |emp (chunkSeq z) σ - a.2.2.2 .Z σ| ≤ 0)
      then tensorPower
        (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
          (coord .Z a.2.2.1))
        (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat x y z
      else 0) =
      if x ∈ boundaryWords31 q a (b*m) .X ∧
          y ∈ boundaryWords31 q a (b*m) .Y ∧
          z ∈ boundaryWords31 q a (b*m) .Z
      then (matMulZ (boundaryFactor31 q a (b*m) .X)
        (boundaryFactor31 q a (b*m) .Y)
        (boundaryFactor31 q a (b*m) .Z)).tensor
          (AX, BX) (BY, CY) (CZ, AZ)
      else 0 := by
  dsimp only
  let hX := boundary_words_pos_restrict31 q b m a .X hq hI
  let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
  let AX := boundaryActiveIndex31 q a (b*m) .X hX x
  let AZ := boundaryActiveIndex31 q a (b*m) .X hX (boundaryWordPartner31 z)
  let BX := boundaryActiveIndex31 q a (b*m) .Y hX x
  let BY := boundaryActiveIndex31 q a (b*m) .Y hX (boundaryWordPartner31 y)
  let CY := boundaryActiveIndex31 q a (b*m) .Z hY y
  let CZ := boundaryActiveIndex31 q a (b*m) .Z hY (boundaryWordPartner31 z)
  let k := (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat
  by_cases hk : k = 0
  · have hmem (W : Side) (v : Fin k → Fin a.2.1 → CW90.Idx7 q) :
        v ∈ boundaryWords31 q a (b*m) W := by
      apply (boundary_mem_iff_emp31 q b m a W hI v).2
      exact Or.inl hk
    have hcard (W : Side) : (boundaryWords31 q a (b*m) W).card = 1 :=
      boundaryWords_card_kzero31 q a (b*m) W hk
    have hfactor (W : Side) : boundaryFactor31 q a (b*m) W = 1 := by
      simp [boundaryFactor31, hcard]
    have hA : AX = AZ := boundary_fin_eq_of_card_one31 (hfactor .X) _ _
    have hB : BX = BY := boundary_fin_eq_of_card_one31 (hfactor .Y) _ _
    have hC : CY = CZ := boundary_fin_eq_of_card_one31 (hfactor .Z) _ _
    simp only [k] at hk
    rw [if_pos hk, if_pos ⟨hmem .X x, hmem .Y y, hmem .Z z⟩]
    change 1 = if BX = BY ∧ CY = CZ ∧ AX = AZ then 1 else 0
    rw [if_pos ⟨hB, hC, hA⟩]
  · simp only [k] at hk
    have hxiff := boundary_mem_iff_approx_zero31 q b m a .X hI hk x
    have hyiff := boundary_mem_iff_approx_zero31 q b m a .Y hI hk y
    have hziff := boundary_mem_iff_approx_zero31 q b m a .Z hI hk z
    rw [if_neg hk]
    by_cases hall : x ∈ boundaryWords31 q a (b*m) .X ∧
        y ∈ boundaryWords31 q a (b*m) .Y ∧
        z ∈ boundaryWords31 q a (b*m) .Z
    · rw [if_pos hall, if_pos ⟨hxiff.1 hall.1, hyiff.1 hall.2.1, hziff.1 hall.2.2⟩]
      have hxlev : ∀ t, levOf (x t) = coord .X a.2.2.1 := by
        have hx := hall.1
        rw [boundaryWords31, Finset.mem_filter] at hx
        exact hx.2.1
      have hylev : ∀ t, levOf (y t) = coord .Y a.2.2.1 := by
        have hy := hall.2.1
        rw [boundaryWords31, Finset.mem_filter] at hy
        exact hy.2.1
      have hzlev : ∀ t, levOf (z t) = coord .Z a.2.2.1 := by
        have hz := hall.2.2
        rw [boundaryWords31, Finset.mem_filter] at hz
        exact hz.2.1
      have hcon : tensorPower
          (conZ q a.2.1 (coord .X a.2.2.1) (coord .Y a.2.2.1)
            (coord .Z a.2.2.1)) k x y z =
          tensorPower (tensorPower (cwZ q) a.2.1) k x y z := by
        unfold tensorPower
        apply Finset.prod_congr rfl
        intro t _ht
        unfold conZ zoP
        rw [if_pos ⟨hxlev t, hylev t, hzlev t⟩]
        rfl
      rw [hcon]
      have ha := hI a (by simp)
      rcases ha with ⟨_h_mass, _hnonneg, _hsum, _hsupport, hzero, _hreflect,
        _hint, _hbetaInt⟩
      by_cases hA : boundaryActive31 a .X
      · have hnB : ¬ boundaryActive31 a .Y := by
          intro hB
          exact (Nat.ne_of_gt hA.2.2) hB.1
        have hnC : ¬ boundaryActive31 a .Z := by
          intro hC
          exact (Nat.ne_of_gt hA.2.1) hC.1
        have hyLow : y = boundaryLowWord31 := by
          funext t
          apply boundary_word_eq_low31
          rw [hylev t, hA.1]
        have hzpp : boundaryWordPartner31 (boundaryWordPartner31 z) = z := by
          funext t j
          exact boundary_symbol_involutive31 (z t j)
        have hcw : tensorPower (tensorPower (cwZ q) a.2.1) k x y z =
            if x = boundaryWordPartner31 z then 1 else 0 := by
          rw [hyLow]
          calc
            _ = tensorPower (tensorPower (cwZ q) a.2.1) k x boundaryLowWord31
                (boundaryWordPartner31 (boundaryWordPartner31 z)) := by rw [hzpp]
            _ = _ := boundary_cw_power_zeroY31 x (boundaryWordPartner31 z)
        rw [hcw]
        have hpz := boundary_partner_mem31 q b m a .Y .Z .X (by decide +kernel)
          (by decide +kernel) (by decide +kernel) hA.1 hI z hall.2.2
        have hAiff : AX = AZ ↔ x = boundaryWordPartner31 z := by
          exact boundaryActiveIndex_eq_iff31 q a (b*m) .X hA hX x
            (boundaryWordPartner31 z) hall.1 hpz
        have hiB : BX = BY := boundary_fin_eq_of_card_one31
          (by simp [boundaryFactor31, hnB]) _ _
        have hiC : CY = CZ := boundary_fin_eq_of_card_one31
          (by simp [boundaryFactor31, hnC]) _ _
        rw [boundary_matMulZ_apply31]
        change (if x = boundaryWordPartner31 z then 1 else 0) =
          if BX = BY ∧ CY = CZ ∧ AX = AZ then 1 else 0
        simp only [hiB, hiC, true_and, hAiff]
      · by_cases hB : boundaryActive31 a .Y
        · have hnC : ¬ boundaryActive31 a .Z := by
            intro hC
            exact (Nat.ne_of_gt hB.2.1) hC.1
          have hzLow : z = boundaryLowWord31 := by
            funext t
            apply boundary_word_eq_low31
            rw [hzlev t, hB.1]
          have hypp : boundaryWordPartner31 (boundaryWordPartner31 y) = y := by
            funext t j
            exact boundary_symbol_involutive31 (y t j)
          have hcw : tensorPower (tensorPower (cwZ q) a.2.1) k x y z =
              if x = boundaryWordPartner31 y then 1 else 0 := by
            rw [hzLow]
            calc
              _ = tensorPower (tensorPower (cwZ q) a.2.1) k x
                  (boundaryWordPartner31 (boundaryWordPartner31 y))
                  boundaryLowWord31 := by rw [hypp]
              _ = _ := boundary_cw_power_zeroZ31 x (boundaryWordPartner31 y)
          rw [hcw]
          have hpy := boundary_partner_mem31 q b m a .Z .Y .X (by decide +kernel)
            (by decide +kernel) (by decide +kernel) hB.1 hI y hall.2.1
          have hBiff : BX = BY ↔ x = boundaryWordPartner31 y := by
            exact boundaryActiveIndex_eq_iff31 q a (b*m) .Y hB hX x
              (boundaryWordPartner31 y) hall.1 hpy
          have hiA : AX = AZ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hA]) _ _
          have hiC : CY = CZ := boundary_fin_eq_of_card_one31
            (by simp [boundaryFactor31, hnC]) _ _
          rw [boundary_matMulZ_apply31]
          change (if x = boundaryWordPartner31 y then 1 else 0) =
            if BX = BY ∧ CY = CZ ∧ AX = AZ then 1 else 0
          simp only [hBiff, hiC, hiA, and_self, and_true]
        · by_cases hC : boundaryActive31 a .Z
          · have hxLow : x = boundaryLowWord31 := by
              funext t
              apply boundary_word_eq_low31
              rw [hxlev t, hC.1]
            have hzpp : boundaryWordPartner31 (boundaryWordPartner31 z) = z := by
              funext t j
              exact boundary_symbol_involutive31 (z t j)
            have hcw : tensorPower (tensorPower (cwZ q) a.2.1) k x y z =
                if y = boundaryWordPartner31 z then 1 else 0 := by
              rw [hxLow]
              calc
                _ = tensorPower (tensorPower (cwZ q) a.2.1) k boundaryLowWord31 y
                    (boundaryWordPartner31 (boundaryWordPartner31 z)) := by rw [hzpp]
                _ = _ := boundary_cw_power_zeroX31 y (boundaryWordPartner31 z)
            rw [hcw]
            have hpz := boundary_partner_mem31 q b m a .X .Z .Y (by decide +kernel)
              (by decide +kernel) (by decide +kernel) hC.1 hI z hall.2.2
            have hCiff : CY = CZ ↔ y = boundaryWordPartner31 z := by
              exact boundaryActiveIndex_eq_iff31 q a (b*m) .Z hC hY y
                (boundaryWordPartner31 z) hall.2.1 hpz
            have hiA : AX = AZ := boundary_fin_eq_of_card_one31
              (by simp [boundaryFactor31, hA]) _ _
            have hiB : BX = BY := boundary_fin_eq_of_card_one31
              (by simp [boundaryFactor31, hB]) _ _
            rw [boundary_matMulZ_apply31]
            change (if y = boundaryWordPartner31 z then 1 else 0) =
              if BX = BY ∧ CY = CZ ∧ AX = AZ then 1 else 0
            simp only [hiA, hiB, true_and, hCiff, and_true]
          · have hpair :
                (coord .X a.2.2.1 = 0 ∧ coord .Y a.2.2.1 = 0) ∨
                (coord .X a.2.2.1 = 0 ∧ coord .Z a.2.2.1 = 0) ∨
                (coord .Y a.2.2.1 = 0 ∧ coord .Z a.2.2.1 = 0) := by
              have hz0 : coord .X a.2.2.1 = 0 ∨ coord .Y a.2.2.1 = 0 ∨
                  coord .Z a.2.2.1 = 0 := by
                rcases hzero with ⟨W, hW⟩
                fin_cases W
                · exact Or.inl hW
                · exact Or.inr (Or.inl hW)
                · exact Or.inr (Or.inr hW)
              rcases hz0 with hx0 | hy0 | hz0
              · by_cases hy : coord .Y a.2.2.1 = 0
                · exact Or.inl ⟨hx0, hy⟩
                · by_cases hz : coord .Z a.2.2.1 = 0
                  · exact Or.inr (Or.inl ⟨hx0, hz⟩)
                  · exact False.elim (hC ⟨hx0, Nat.pos_of_ne_zero hy,
                      Nat.pos_of_ne_zero hz⟩)
              · by_cases hx : coord .X a.2.2.1 = 0
                · exact Or.inl ⟨hx, hy0⟩
                · by_cases hz : coord .Z a.2.2.1 = 0
                  · exact Or.inr (Or.inr ⟨hy0, hz⟩)
                  · exact False.elim (hA ⟨hy0, Nat.pos_of_ne_zero hx,
                      Nat.pos_of_ne_zero hz⟩)
              · by_cases hx : coord .X a.2.2.1 = 0
                · exact Or.inr (Or.inl ⟨hx, hz0⟩)
                · by_cases hy : coord .Y a.2.2.1 = 0
                  · exact Or.inr (Or.inr ⟨hy, hz0⟩)
                  · exact False.elim (hB ⟨hz0, Nat.pos_of_ne_zero hx,
                      Nat.pos_of_ne_zero hy⟩)
            rw [boundary_cw_power_unit31 x y z _ _ _ hxlev hylev hzlev
              a.2.2.1.property hpair]
            have hiA : AX = AZ := boundary_fin_eq_of_card_one31
              (by simp [boundaryFactor31, hA]) _ _
            have hiB : BX = BY := boundary_fin_eq_of_card_one31
              (by simp [boundaryFactor31, hB]) _ _
            have hiC : CY = CZ := boundary_fin_eq_of_card_one31
              (by simp [boundaryFactor31, hC]) _ _
            change 1 = if BX = BY ∧ CY = CZ ∧ AX = AZ then 1 else 0
            rw [if_pos ⟨hiB, hiC, hiA⟩]
    · rw [if_neg hall]
      rw [if_neg]
      intro happ
      exact hall ⟨hxiff.2 happ.1, hyiff.2 happ.2.1, hziff.2 happ.2.2⟩

private theorem boundarySingletonExactReverse31 (q b m : ℕ) (a : ℚ × AtomKey)
    (hq : 0 < q) (hI : BoundaryInventoryAdmissible [a] b) :
    Restricts (inventoryTensorZ q [a] (b*m) 0).tensor
      (matMulZ (boundaryFactor31 q a (b*m) .X)
        (boundaryFactor31 q a (b*m) .Y)
        (boundaryFactor31 q a (b*m) .Z)).tensor := by
  let hX := boundary_words_pos_restrict31 q b m a .X hq hI
  let hY := boundary_words_pos_restrict31 q b m a .Y hq hI
  let fX := fun u : (inventoryTensorZ q [a] (b*m) 0).X =>
    (boundaryActiveIndex31 q a (b*m) .X hX u.1,
      boundaryActiveIndex31 q a (b*m) .Y hX u.1)
  let fY := fun u : (inventoryTensorZ q [a] (b*m) 0).Y =>
    (boundaryActiveIndex31 q a (b*m) .Y hX (boundaryWordPartner31 u.1),
      boundaryActiveIndex31 q a (b*m) .Z hY u.1)
  let fZ := fun u : (inventoryTensorZ q [a] (b*m) 0).Z =>
    (boundaryActiveIndex31 q a (b*m) .Z hY (boundaryWordPartner31 u.1),
      boundaryActiveIndex31 q a (b*m) .X hX (boundaryWordPartner31 u.1))
  let pX := fun u : (inventoryTensorZ q [a] (b*m) 0).X =>
    u.1 ∈ boundaryWords31 q a (b*m) .X
  let pY := fun u : (inventoryTensorZ q [a] (b*m) 0).Y =>
    u.1 ∈ boundaryWords31 q a (b*m) .Y
  let pZ := fun u : (inventoryTensorZ q [a] (b*m) 0).Z =>
    u.1 ∈ boundaryWords31 q a (b*m) .Z
  let M := (matMulZ (boundaryFactor31 q a (b*m) .X)
    (boundaryFactor31 q a (b*m) .Y) (boundaryFactor31 q a (b*m) .Z)).tensor
  let S := fun x y z => M (fX x) (fY y) (fZ z)
  have hpre : S ≤ₜ M := precomp_restricts fX fY fZ M
  have hzero : zoP pX pY pZ S ≤ₜ S := zoP_restricts pX pY pZ S
  refine Restricts.of_eq (Restricts.trans hzero hpre) ?_
  funext ux uy uz
  rcases ux with ⟨x, ux⟩
  rcases uy with ⟨y, uy⟩
  rcases uz with ⟨z, uz⟩
  rcases ux with ⟨⟩
  rcases uy with ⟨⟩
  rcases uz with ⟨⟩
  rw [zoP_apply]
  simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ, mul_one]
  exact boundaryOccurrenceExactReverse31 q b m a hq hI x y z

private theorem inventoryConsExactRestrictsTensorProd31 (q n : ℕ)
    (a : ℚ × AtomKey) (I : Inventory) :
    Restricts (inventoryTensorZ q (a :: I) n 0).tensor
      (tensorProd (inventoryTensorZ q [a] n 0).tensor
        (inventoryTensorZ q I n 0).tensor) := by
  let fX := fun x : (inventoryTensorZ q (a :: I) n 0).X => ((x.1, PUnit.unit), x.2)
  let fY := fun y : (inventoryTensorZ q (a :: I) n 0).Y => ((y.1, PUnit.unit), y.2)
  let fZ := fun z : (inventoryTensorZ q (a :: I) n 0).Z => ((z.1, PUnit.unit), z.2)
  refine Restricts.of_eq (precomp_restricts fX fY fZ
    (tensorProd (inventoryTensorZ q [a] n 0).tensor
      (inventoryTensorZ q I n 0).tensor)) ?_
  funext x y z
  dsimp only [fX, fY, fZ]
  simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ, tensorProd, mul_one]

private theorem matMulTensorProdRestrictsMatMul31 (a b c a' b' c' : ℕ) :
    Restricts (tensorProd (matMulZ a b c).tensor (matMulZ a' b' c').tensor)
      (matMulZ (a*a') (b*b') (c*c')).tensor := by
  let fX := mmIdx a b a' b'
  let fY := mmIdx b c b' c'
  let fZ := mmIdx c a c' a'
  refine Restricts.of_eq (precomp_restricts fX fY fZ
    (matMulZ (a*a') (b*b') (c*c')).tensor) ?_
  funext x y z
  exact matMul_tensorProd_apply a b c a' b' c' x y z

/-- Transparent (`def`) form of this restriction. -/
noncomputable def boundaryMatrixExactReverseRestriction31 (q b m : ℕ)
    (I : Inventory) (hq : 0 < q) (hI : BoundaryInventoryAdmissible I b) :
    Restricts (inventoryTensorZ q I (b*m) 0).tensor
      (boundaryMatrixZ q I (b*m)).tensor := by
  induction I with
  | nil =>
      let fX := fun _ : (inventoryTensorZ q [] (b*m) 0).X =>
        ((0 : Fin 1), (0 : Fin 1))
      let fY := fun _ : (inventoryTensorZ q [] (b*m) 0).Y =>
        ((0 : Fin 1), (0 : Fin 1))
      let fZ := fun _ : (inventoryTensorZ q [] (b*m) 0).Z =>
        ((0 : Fin 1), (0 : Fin 1))
      refine Restricts.of_eq (precomp_restricts fX fY fZ
        (boundaryMatrixZ q [] (b*m)).tensor) ?_
      funext x y z
      dsimp only [fX, fY, fZ]
      simp [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ,
        boundaryMatrixZ, boundaryDimension31, matMulZ]
  | cons a I ih =>
      have ha : BoundaryInventoryAdmissible [a] b := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hI a (by simp)
      have ht : BoundaryInventoryAdmissible I b := by
        intro x hx
        exact hI x (by simp [hx])
      have hsplit := inventoryConsExactRestrictsTensorProd31 q (b*m) a I
      have hhead := boundarySingletonExactReverse31 q b m a hq ha
      have htail := ih ht
      have hprod₁ := Restricts.tensorProd_right hhead (inventoryTensorZ q I (b*m) 0).tensor
      have hprod₂ := Restricts.tensorProd_left htail
        (matMulZ (boundaryFactor31 q a (b*m) .X)
          (boundaryFactor31 q a (b*m) .Y)
          (boundaryFactor31 q a (b*m) .Z)).tensor
      have hmatrix := matMulTensorProdRestrictsMatMul31
        (boundaryFactor31 q a (b*m) .X)
        (boundaryFactor31 q a (b*m) .Y)
        (boundaryFactor31 q a (b*m) .Z)
        (boundaryDimension31 q I (b*m) .X)
        (boundaryDimension31 q I (b*m) .Y)
        (boundaryDimension31 q I (b*m) .Z)
      have h := Restricts.trans hsplit
        (Restricts.trans hprod₁ (Restricts.trans hprod₂ hmatrix))
      simpa [boundaryMatrixZ, boundaryDimension31, boundaryFactor31] using h

end
end OmegaBound.ADVXXZGeneral
end
