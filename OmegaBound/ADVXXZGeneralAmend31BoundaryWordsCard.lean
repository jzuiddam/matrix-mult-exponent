import OmegaBound.ADVXXZGeneralAmend31NIterate

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

private theorem card_idx7_level_fibre31 (q : ℕ) (v : Fin 3) :
    Fintype.card {a : CW90.Idx7 q // lvl7 a = v} = if v = 1 then q else 1 := by
  fin_cases v
  · letI : Unique {a : CW90.Idx7 q // lvl7 a = 0} :=
      { default := ⟨.inl none, rfl⟩
        uniq := by
          rintro ⟨a, h⟩
          apply Subtype.ext
          rcases a with (_ | i) | z
          · rfl
          · change (1 : Fin 3) = 0 at h
            have hv := congrArg Fin.val h
            omega
          · change (2 : Fin 3) = 0 at h
            have hv := congrArg Fin.val h
            omega }
    simp
  · have hb : Function.Bijective
        (fun i : Fin q => (⟨Sum.inl (some i), rfl⟩ :
          {a : CW90.Idx7 q // lvl7 a = 1})) := by
      constructor
      · intro i j h
        simpa using h
      · rintro ⟨(_ | i) | ⟨⟩, h⟩
        · simp [CW90.lvl7] at h
        · exact ⟨i, rfl⟩
        · simp [CW90.lvl7] at h
    exact (Fintype.card_of_bijective hb).symm.trans (Fintype.card_fin q)
  · letI : Unique {a : CW90.Idx7 q // lvl7 a = 2} :=
      { default := ⟨.inr (), rfl⟩
        uniq := by
          rintro ⟨a, h⟩
          apply Subtype.ext
          rcases a with (_ | i) | z
          · change (0 : Fin 3) = 2 at h
            have hv := congrArg Fin.val h
            omega
          · change (1 : Fin 3) = 2 at h
            have hv := congrArg Fin.val h
            omega
          · cases z
            rfl }
    simp

private def boundaryLevelMapFibreEquiv31 {σ : Type*} [Fintype σ]
    (q : ℕ) (v : σ → Fin 3) :
    {a : σ → CW90.Idx7 q // (fun z => lvl7 (a z)) = v} ≃
      ∀ z : σ, {a : CW90.Idx7 q // lvl7 a = v z} where
  toFun a z := ⟨a.1 z, congrFun a.2 z⟩
  invFun a := ⟨fun z => (a z).1, funext fun z => (a z).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_levelMap_fibre31 {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (v : σ → Fin 3) :
    Fintype.card {a : σ → CW90.Idx7 q // (fun z => lvl7 (a z)) = v} =
      q ^ ((Finset.univ.filter fun z => v z = 1).card) := by
  classical
  rw [Fintype.card_congr (boundaryLevelMapFibreEquiv31 q v), Fintype.card_pi]
  simp_rw [card_idx7_level_fibre31]
  simp [Finset.prod_ite]

private theorem rat_floor_toNat_nat31 (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem boundary_count_cast31 (b m : ℕ) (a : ℚ × AtomKey) (W : Side)
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
    exact rat_floor_toNat_nat31 _
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
  rw [hk, hcmul]
  rw [rat_floor_toNat_nat31]

private theorem mem_boundaryWords_iff_counts31 (q b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hI : BoundaryInventoryAdmissible [a] b)
    (x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
      Fin a.2.1 → CW90.Idx7 q) :
    x ∈ boundaryWords31 q a (b*m) W ↔
      ∀ σ, typeCnt (chunkSeq x) σ = boundaryTypeCounts31 a (b*m) W σ := by
  let k := (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat
  have ha := hI a (by simp)
  rcases ha with ⟨_hma, _hbeta_nonneg, _hsum, hsupport, _hzero, _hreflect,
    _hmass, _hbeta_integral⟩
  unfold boundaryWords31
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change
    ((∀ t, levOf (x t) = coord W a.2.2.1) ∧
      (k = 0 ∨ ∀ σ, emp (chunkSeq x) σ = a.2.2.2 W σ)) ↔
    ∀ σ, typeCnt (chunkSeq x) σ = boundaryTypeCounts31 a (b*m) W σ
  by_cases hk : k = 0
  · have hc0 : ∀ σ, boundaryTypeCounts31 a (b*m) W σ = 0 := by
      intro σ
      have hc := boundary_count_cast31 b m a W hI σ
      change ((boundaryTypeCounts31 a (b*m) W σ : ℕ) : ℚ) =
        (k : ℚ) * a.2.2.2 W σ at hc
      rw [hk, Nat.cast_zero, zero_mul] at hc
      exact_mod_cast hc
    have hk' : (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat = 0 := hk
    letI : IsEmpty (Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat) :=
      ⟨fun t => (Fin.cast hk' t).elim0⟩
    constructor
    · intro _hword σ
      rw [hc0]
      unfold typeCnt
      simp
    · intro _hcounts
      constructor
      · intro t
        exact (Fin.cast hk' t).elim0
      · exact Or.inl hk
  · have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    simp only [hk, false_or]
    constructor
    · rintro ⟨_hlevel, hemp⟩ σ
      have htcast : (typeCnt (chunkSeq x) σ : ℚ) =
          (k : ℚ) * a.2.2.2 W σ := by
        have he := hemp σ
        change (typeCnt (chunkSeq x) σ : ℚ) / (k : ℚ) = a.2.2.2 W σ at he
        rw [div_eq_iff hkq] at he
        simpa [mul_comm] using he
      have hccast := boundary_count_cast31 b m a W hI σ
      change (boundaryTypeCounts31 a (b*m) W σ : ℚ) =
        (k : ℚ) * a.2.2.2 W σ at hccast
      exact_mod_cast htcast.trans hccast.symm
    · intro hcounts
      constructor
      · intro t
        have hpos : 0 < typeCnt (chunkSeq x) (chunkSeq x t) := by
          rw [typeCnt, Finset.card_pos]
          exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        have hbetane : a.2.2.2 W (chunkSeq x t) ≠ 0 := by
          intro hbeta0
          have hccast := boundary_count_cast31 b m a W hI (chunkSeq x t)
          change (boundaryTypeCounts31 a (b*m) W (chunkSeq x t) : ℚ) =
            (k : ℚ) * a.2.2.2 W (chunkSeq x t) at hccast
          rw [hbeta0, mul_zero] at hccast
          have hc0 : boundaryTypeCounts31 a (b*m) W (chunkSeq x t) = 0 := by
            exact_mod_cast hccast
          rw [hcounts, hc0] at hpos
          omega
        change chunkLvl (chunkSeq x t) = coord W a.2.2.1
        exact hsupport W (chunkSeq x t) hbetane
      · intro σ
        change (typeCnt (chunkSeq x) σ : ℚ) / (k : ℚ) = a.2.2.2 W σ
        rw [div_eq_iff hkq]
        have htcast : (typeCnt (chunkSeq x) σ : ℚ) =
            (boundaryTypeCounts31 a (b*m) W σ : ℚ) := by
          exact_mod_cast hcounts σ
        rw [htcast, boundary_count_cast31 b m a W hI σ]
        exact mul_comm _ _

private def boundaryWordsSigmaEquiv31 (q b m : ℕ) (a : ℚ × AtomKey)
    (W : Side) (hI : BoundaryInventoryAdmissible [a] b) :
    {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
        Fin a.2.1 → CW90.Idx7 q // x ∈ boundaryWords31 q a (b*m) W} ≃
      Σ s : {s : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
          ∀ σ, typeCnt s σ = boundaryTypeCounts31 a (b*m) W σ},
        {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
            Fin a.2.1 → CW90.Idx7 q // chunkSeq x = s.1} where
  toFun x := ⟨⟨chunkSeq x.1, (mem_boundaryWords_iff_counts31 q b m a W hI x.1).mp x.2⟩,
    ⟨x.1, rfl⟩⟩
  invFun z := ⟨z.2.1, (mem_boundaryWords_iff_counts31 q b m a W hI z.2.1).mpr (by
    simpa only [z.2.2] using z.1.2)⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨s, hs⟩, ⟨x, hx⟩⟩
    cases hx
    rfl

private def boundaryChunkSeqFibreEquiv31 {q w k : ℕ} (s : Fin k → Chunk w) :
    {x : Fin k → Fin w → CW90.Idx7 q // chunkSeq x = s} ≃
      {x : (Fin k × Fin w) → CW90.Idx7 q //
        (fun z => lvl7 (x z)) = fun z => s z.1 z.2} where
  toFun x := ⟨fun z : Fin k × Fin w => x.1 z.1 z.2, by
    change (fun z : Fin k × Fin w => lvl7 (x.1 z.1 z.2)) = fun z => s z.1 z.2
    funext z
    have hx := congrFun (congrFun x.2 z.1) z.2
    exact hx⟩
  invFun x := ⟨fun t j => x.1 (t,j), by
    change (fun t j => lvl7 (x.1 (t,j))) = s
    funext t j
    exact congrFun x.2 (t,j)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_comp_typeCnt31 {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (s : Fin n → α) (f : α → ℕ) :
    ∑ t, f (s t) = ∑ a, typeCnt s a * f a := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := s) (t := (Finset.univ : Finset α))
    (fun t _ => Finset.mem_univ (s t)) (fun t => f (s t))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hconst : ∀ t ∈ (Finset.univ : Finset (Fin n)).filter (fun t => s t = a),
      f (s t) = f a := fun t ht => by rw [(Finset.mem_filter.mp ht).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, typeCnt]

private theorem card_chunkSeq_fibre31 {q w k : ℕ} (s : Fin k → Chunk w) :
    Fintype.card {x : Fin k → Fin w → CW90.Idx7 q // chunkSeq x = s} =
      q ^ (∑ σ : Chunk w, typeCnt s σ *
        (Finset.univ.filter (fun j : Fin w => (σ j).val = 1)).card) := by
  classical
  rw [Fintype.card_congr (boundaryChunkSeqFibreEquiv31 s),
    card_levelMap_fibre31]
  congr 1
  calc
    (Finset.univ.filter (fun z : Fin k × Fin w => s z.1 z.2 = 1)).card =
        ∑ z : Fin k × Fin w, if s z.1 z.2 = 1 then 1 else 0 := by
          rw [Finset.card_filter]
    _ = ∑ t : Fin k, ∑ j : Fin w, if s t j = 1 then 1 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ t : Fin k,
        (Finset.univ.filter (fun j : Fin w => (s t j).val = 1)).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _hj
      change (if s t j = 1 then 1 else 0) = (if (s t j).val = 1 then 1 else 0)
      by_cases h : s t j = 1
      · simp [h]
      · have hv : (s t j).val ≠ 1 := by
          intro hv
          apply h
          exact Fin.ext hv
        simp [h, hv]
    _ = ∑ σ : Chunk w, typeCnt s σ *
        (Finset.univ.filter (fun j : Fin w => (σ j).val = 1)).card := by
      exact sum_comp_typeCnt31 s (fun σ : Chunk w =>
        (Finset.univ.filter (fun j : Fin w => (σ j).val = 1)).card)

/-- Paper clauses:
`P/prelim.tex:181–200,267–278` and `P/constituent.tex:35–39`. -/
theorem boundary_words_card31 (q b m : ℕ) (a : ℚ × AtomKey) (W : Side)
    (hI : BoundaryInventoryAdmissible [a] b) :
  let k := (a.1 * ((b*m : ℕ) : ℚ)).floor.toNat
  let c := boundaryTypeCounts31 a (b*m) W
  (boundaryWords31 q a (b*m) W).card =
    Fintype.card {x : Fin k → Chunk a.2.1 // ∀ σ, typeCnt x σ = c σ} *
      q ^ (∑ σ : Chunk a.2.1, c σ *
        (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card) := by
  dsimp only
  let e := boundaryWordsSigmaEquiv31 q b m a W hI
  calc
    (boundaryWords31 q a (b*m) W).card =
        Fintype.card {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
          Fin a.2.1 → CW90.Idx7 q // x ∈ boundaryWords31 q a (b*m) W} := by
            simp
    _ = Fintype.card
        (Σ s : {s : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
            ∀ σ, typeCnt s σ = boundaryTypeCounts31 a (b*m) W σ},
          {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
              Fin a.2.1 → CW90.Idx7 q // chunkSeq x = s.1}) :=
        Fintype.card_congr e
    _ = ∑ s : {s : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
            ∀ σ, typeCnt s σ = boundaryTypeCounts31 a (b*m) W σ},
          Fintype.card {x : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat →
            Fin a.2.1 → CW90.Idx7 q // chunkSeq x = s.1} := by
        rw [Fintype.card_sigma]
    _ = ∑ _s : {s : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
            ∀ σ, typeCnt s σ = boundaryTypeCounts31 a (b*m) W σ},
          q ^ (∑ σ : Chunk a.2.1, boundaryTypeCounts31 a (b*m) W σ *
            (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card) := by
        apply Finset.sum_congr rfl
        intro s _hs
        rw [card_chunkSeq_fibre31]
        congr 1
        apply Finset.sum_congr rfl
        intro σ _hσ
        rw [s.2 σ]
    _ = Fintype.card
          {s : Fin (a.1 * (((b*m : ℕ) : ℚ))).floor.toNat → Chunk a.2.1 //
            ∀ σ, typeCnt s σ = boundaryTypeCounts31 a (b*m) W σ} *
          q ^ (∑ σ : Chunk a.2.1, boundaryTypeCounts31 a (b*m) W σ *
            (Finset.univ.filter (fun j : Fin a.2.1 => (σ j).val = 1)).card) := by
        simp

end
end OmegaBound.ADVXXZGeneral
end
