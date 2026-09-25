import OmegaBound.ADVXXZGeneralGridFinite
import OmegaBound.ADVXXZGeneralGrid
import OmegaBound.ADVXXZGeneralAmend25Rates

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

-- Finite witnesses remain outputs of the producer.
/-- Paper clause: `H/analysis_global.tex:77–100; P/global.tex:115`. -/
def fullGridPool27 {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ε : ℚ) : ℕ :=
  Fintype.card (FullGrid g n ε)

/-- Paper clause: `H/analysis_global.tex:77–100; P/global.tex:115`. -/
def gridMinimum27 {ι : Type} [Fintype ι] (v : ι → ℕ) : ℕ :=
  if h : (Finset.univ : Finset ι).Nonempty then
    ((Finset.univ : Finset ι).image v).min' (h.image v) else 0

/-- Paper clause: `H/analysis_global.tex:77–100; P/global.tex:115`. -/
def gridTruncation27 {ι : Type} [Fintype ι] (v : ι → ℕ) (i : ι) :
    Fin (gridMinimum27 v) ↪ Fin (v i) where
  toFun k := ⟨k.val, lt_of_lt_of_le k.isLt (by
    have h : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
    simp only [gridMinimum27, dif_pos h]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩
  inj' := by intro a b h; exact Fin.ext (congrArg (fun x : Fin (v i) => x.val) h)

-- The same physical output index as used by `constituentOutputZ`.
/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def ConstituentExactGrid27 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) :=
  {h : (t : Fin (Fintype.card (ConstituentTerm p))) → Side → Chunk w →
      Fin (constituentOutN d.toPaper m t + 1) //
    (∀ t W, (∑ σ, (h t W σ).val) = constituentOutN d.toPaper m t) ∧
      ∀ t W σ, (h t W σ).val ≠ 0 →
        chunkLvl σ = coord W (constituentIndex (p := p) t).2.2.1}

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def ConstituentFullGrid27 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (ε : ℚ) :=
  {h : ConstituentExactGrid27 d m // ∀ t W,
    0 < constituentOutN d.toPaper m t → ∀ σ,
      |((h.val t W σ).val : ℚ) / constituentOutN d.toPaper m t -
        (constituentOutBeta d.toPaper W t).prob σ| ≤ ε}

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def constituentGridTensorZ27 (q : ℕ) {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m) : ITensor :=
  let L := (t : Fin (Fintype.card (ConstituentTerm p))) →
    Fin (constituentOutN d.toPaper m t) → Fin w → CW90.Idx7 q
  let keep := fun W (x : L) => ∀ t σ, typeCnt (chunkSeq (x t)) σ = (h.val t W σ).val
  { X := L, Y := L, Z := L
    tensor := zoP (keep .X) (keep .Y) (keep .Z) (fun x y z => ∏ t,
      tensorPower (conZ q w (constituentOutI (p := p) t) (constituentOutJ (p := p) t)
        (constituentOutK (p := p) t)) (constituentOutN d.toPaper m t) (x t) (y t) (z t)) }
end
end OmegaBound.ADVXXZGeneral
end

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def mixtureDist27 {A B : Type} [Fintype A] [Fintype B]
    (weights : RatDist A) (P : A → RatDist B) : RatDist B where
  num x := ∑ a, weights.num a * (P a).num x * ∏ a' ∈ Finset.univ.erase a, (P a').den
  den := weights.den * ∏ a, (P a).den
  den_pos := Nat.mul_pos weights.den_pos (Finset.prod_pos fun a _ => (P a).den_pos)
  sum_num := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, RatDist.sum_num]
    have h : ∀ a, (P a).den * ∏ a' ∈ Finset.univ.erase a, (P a').den = ∏ a', (P a').den :=
      fun a => Finset.mul_prod_erase Finset.univ (fun a => (P a).den) (Finset.mem_univ a)
    simp_rw [mul_assoc, h]
    rw [← Finset.sum_mul, weights.sum_num]

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def joinChunk27 {w : ℕ} (x y : Chunk w) : Chunk (w+w) :=
  fun i => if hi : i.val < w then x ⟨i.val,hi⟩ else y ⟨i.val-w,by omega⟩

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def productSplit27 {w : ℕ} (x y : SplitDist w) : SplitDist (w+w) :=
  RatDist.map (fun a => joinChunk27 a.1 a.2)
    (RatDist.pairWith x (fun _ => y) y.den (fun _ => rfl))

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def constituentGridBeta27 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin s) (r : Fin 6) (u : ChildShape p t) : SplitDist w :=
  let i := Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩
  if hn : 0 < constituentOutN d.toPaper m i then
    { num := fun σ => (h.val i W σ).val
      den := constituentOutN d.toPaper m i
      den_pos := hn
      sum_num := h.property.1 i W }
  else d.betaChild W t r u

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def constituentGridRegionBeta27 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin s) (r : Fin 6) : SplitDist (w+w) :=
  mixtureDist27 (d.alpha t r) fun u =>
    productSplit27 (constituentGridBeta27 d m h W t r u)
      (constituentGridBeta27 d m h W t r (complement p t u))


/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
theorem mixture_supported27 {A : Type} [Fintype A] {w : ℕ}
    (weights : RatDist A) (P : A → SplitDist w) (k : ℕ)
    (h : ∀ a, Supported (P a) k) : Supported (mixtureDist27 weights P) k := by
  intro σ hσ
  by_contra hk
  apply hσ
  change (∑ a, weights.num a * (P a).num σ * ∏ a' ∈ Finset.univ.erase a, (P a').den) = 0
  apply Finset.sum_eq_zero
  intro a _
  have ha : (P a).num σ = 0 := by
    by_contra ha; exact hk (h a σ ha)
  simp only [ha, mul_zero, zero_mul]

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
theorem product_supported27 {w : ℕ} (x y : SplitDist w) (i j : ℕ)
    (hx : Supported x i) (hy : Supported y j) : Supported (productSplit27 x y) (i+j) := by
  intro σ hσ
  by_contra hk
  apply hσ
  change (∑ a ∈ Finset.univ.filter (fun a : Chunk w × Chunk w => joinChunk27 a.1 a.2 = σ),
    x.num a.1 * y.num a.2) = 0
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hx0 : x.num a.1 = 0
  · simp only [hx0, zero_mul]
  by_cases hy0 : y.num a.2 = 0
  · simp only [hy0, mul_zero]
  exfalso
  apply hk
  have hjoin := (Finset.mem_filter.mp ha).2
  rw [← hjoin]
  have hh : chunkLvl (joinChunk27 a.1 a.2) = chunkLvl a.1 + chunkLvl a.2 := by
    simpa [joinChunk27, chunkLvl, Fin.sum_univ_add] using
      (OmegaBound.ADVXXZ.chunkLvl_eq_add (joinChunk27 a.1 a.2))
  exact hh.trans (congrArg₂ (· + ·) (hx _ hx0) (hy _ hy0))

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
theorem constituentGridBeta_supported27 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (h : ConstituentExactGrid27 d m) (W : Side) (t : Fin s)
    (r : Fin 6) (u : ChildShape p t) :
    Supported (constituentGridBeta27 d m h W t r u) (coord W u.val) := by
  unfold constituentGridBeta27
  dsimp only
  split_ifs with hn
  · intro σ hσ
    have hg := h.property.2 (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) W σ hσ
    have hi : constituentIndex (p := p) (Fintype.equivFin (ConstituentTerm p) ⟨t,r,u⟩) =
        ⟨t,r,u⟩ := (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply _
    rw [hi] at hg
    exact hg
  · exact hd.child_support W t r u

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
theorem constituentGridRegion_supported27 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (h : ConstituentExactGrid27 d m) (W : Side) (t : Fin s) (r : Fin 6) :
    Supported (constituentGridRegionBeta27 d m h W t r)
      (match W with | .X => p.i t | .Y => p.j t | .Z => p.k t) := by
  apply mixture_supported27
  intro u
  have hs := product_supported27 _ _ _ _ (constituentGridBeta_supported27 d hd m h W t r u)
    (constituentGridBeta_supported27 d hd m h W t r (complement p t u))
  cases W with
  | X =>
    convert hs using 1
    exact (Nat.add_sub_of_le u.property.1).symm
  | Y =>
    convert hs using 1
    exact (Nat.add_sub_of_le u.property.2.1).symm
  | Z =>
    convert hs using 1
    exact (Nat.add_sub_of_le u.property.2.2).symm

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def constituentGridParent27 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (h : ConstituentExactGrid27 d m) : ConstituentInput w s :=
  { p with
    beta := fun W t => mixtureDist27 (d.A t) (constituentGridRegionBeta27 d m h W t)
    beta_supported := by
      intro W t σ hσ
      have hs := mixture_supported27 (d.A t) (constituentGridRegionBeta27 d m h W t) _
        (fun r => constituentGridRegion_supported27 d hd m h W t r)
      apply hs σ
      intro hz
      apply hσ
      change ((_ : ℕ) : ℝ) / ((_ : ℕ) : ℝ) = 0
      rw [hz, Nat.cast_zero, zero_div] }

/-- Paper clause: `H/analysis_constituent.tex:117–125; P/constituent.tex:149`. -/
def constituentGridSpec27 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (m : ℕ) (h : ConstituentExactGrid27 d m) :
    ConstituentSpec (constituentGridParent27 d hd m h) where
  A := d.A
  alpha := d.alpha
  betaRegion := constituentGridRegionBeta27 d m h
  betaChild := fun W t r u => constituentGridBeta27 (p := p) d m h W t r u
  perm := d.perm
  outBase := d.outBase
end
end OmegaBound.ADVXXZGeneral
end
