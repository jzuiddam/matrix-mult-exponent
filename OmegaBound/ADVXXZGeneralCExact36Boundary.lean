import OmegaBound.ADVXXZGeneralCExact36Bridges

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-! Local implementations of the two boundary laws for exact constituent grids,
`constituent_grid_boundary_or_zero28` and `constituent_grid_admissible28`. -/

def constituentChildCount28 {w s : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {m : ℕ} (h : ConstituentExactGrid27 d m)
    (W : Side) (t : Fin s) (r : Fin 6) (v : ChildShape p t) (σ : Chunk w) : ℕ :=
  (h.val (Fintype.equivFin (ConstituentTerm p) ⟨t,r,v⟩) W σ).val

def ConstituentGridBoundary28 {w s : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {m : ℕ} (h : ConstituentExactGrid27 d m) : Prop :=
  ∀ t r v (Z X Y : Side), X ≠ Y → X ≠ Z → Y ≠ Z → coord Z v.1 = 0 →
    ∀ σ, constituentChildCount28 h X t r v σ =
      constituentChildCount28 h Y t r v (reflect σ)

private def constituentExactSideWord {A : Type} (x y z : A) : Side → A
  | .X => x
  | .Y => y
  | .Z => z

private theorem constituentExactSideWord_apply {A : Type} {B : A → Type}
    (x y z : (a : A) → B a) (W : Side) (a : A) :
    constituentExactSideWord x y z W a =
      constituentExactSideWord (x a) (y a) (z a) W := by
  cases W <;> rfl

private theorem constituentExact_lvl7_eq_zero {q w : ℕ}
    (a : Fin w → CW90.Idx7 q) (h : chunkLvl (chunkOf a) = 0) (c : Fin w) :
    (CW90.lvl7 (a c)).val = 0 := by
  have hle : (chunkOf a c).val ≤ chunkLvl (chunkOf a) := by
    unfold chunkLvl
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun p => (chunkOf a p).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simpa only [chunkOf] using (show (chunkOf a c).val = 0 by omega)

private theorem constituentExact_cwZ_ne_permutations {q : ℕ}
    (x y z : CW90.Idx7 q) (h : cwZ q x y z ≠ 0) :
    cwZ q y x z ≠ 0 ∧ cwZ q x z y ≠ 0 ∧ cwZ q y z x ≠ 0 ∧
      cwZ q z x y ≠ 0 ∧ cwZ q z y x ≠ 0 := by
  rcases x with (_ | x0) | x0 <;>
    rcases y with (_ | y0) | y0 <;>
      rcases z with (_ | z0) | z0 <;> simp_all [cwZ]

set_option maxHeartbeats 1000000 in
private theorem constituentExact_chunk_reflect_last {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf z) = 0) :
    chunkOf y = reflect (chunkOf x) := by
  funext c
  apply Fin.ext
  have hz := constituentExact_lvl7_eq_zero z hzero c
  have hc := hcw c
  rcases hx : x c with (_ | x0) | x0 <;>
    rcases hy : y c with (_ | y0) | y0 <;>
      rcases hz' : z c with (_ | z0) | z0 <;>
        simp_all [cwZ, chunkOf, reflect, CW90.lvl7]

private theorem constituentExact_chunk_reflect {q w : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (A B C : Side)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcw : ∀ c, cwZ q (x c) (y c) (z c) ≠ 0)
    (hzero : chunkLvl (chunkOf (constituentExactSideWord x y z C)) = 0) :
    chunkOf (constituentExactSideWord x y z B) =
      reflect (chunkOf (constituentExactSideWord x y z A)) := by
  cases A <;> cases B <;> cases C <;> simp_all [constituentExactSideWord]
  · exact constituentExact_chunk_reflect_last x y z hcw hzero
  · exact constituentExact_chunk_reflect_last x z y
      (fun c => (constituentExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.1) hzero
  · exact constituentExact_chunk_reflect_last y x z
      (fun c => (constituentExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).1) hzero
  · exact constituentExact_chunk_reflect_last y z x
      (fun c => (constituentExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.1) hzero
  · exact constituentExact_chunk_reflect_last z x y
      (fun c => (constituentExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.1) hzero
  · exact constituentExact_chunk_reflect_last z y x
      (fun c => (constituentExact_cwZ_ne_permutations (x c) (y c) (z c) (hcw c)).2.2.2.2) hzero

private theorem constituentExact_reflect_reflect {w : ℕ} (σ : Chunk w) :
    reflect (reflect σ) = σ := by
  funext c
  apply Fin.ext
  simp only [reflect]
  have hc := (σ c).isLt
  omega

private theorem constituentExact_conZ_ne_data {q w i j k : ℕ}
    (x y z : Fin w → CW90.Idx7 q) (h : conZ q w i j k x y z ≠ 0) :
    levOf x = i ∧ levOf y = j ∧ levOf z = k ∧
      ∀ c, cwZ q (x c) (y c) (z c) ≠ 0 := by
  unfold conZ zoP at h
  split at h
  · rename_i hlevels
    refine ⟨hlevels.1, hlevels.2.1, hlevels.2.2, ?_⟩
    intro c hc
    apply h
    unfold tensorPower
    exact Finset.prod_eq_zero (Finset.mem_univ c) hc
  · simp at h

theorem constituentGridBoundary_of_coeff_ne_zero36 {q w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (m : ℕ)
    (h : ConstituentExactGrid27 d m)
    (x : (constituentGridTensorZ27 q d m h).X)
    (y : (constituentGridTensorZ27 q d m h).Y)
    (z : (constituentGridTensorZ27 q d m h).Z)
    (hcoeff : (constituentGridTensorZ27 q d m h).tensor x y z ≠ 0) :
    ConstituentGridBoundary28 h := by
  classical
  let k := constituentOutN d.toPaper m
  let L := (a : Fin (Fintype.card (ConstituentTerm p))) →
    Fin (k a) → Fin w → CW90.Idx7 q
  let keep := fun (W : Side) (v : L) => ∀ a σ,
    ADVXXZ.typeCnt (chunkSeq (v a)) σ = (h.val a W σ).val
  let core := fun a : Fin (Fintype.card (ConstituentTerm p)) =>
    tensorPower (conZ q w (constituentOutI (p := p) a)
      (constituentOutJ (p := p) a) (constituentOutK (p := p) a))
      (k a) (x a) (y a) (z a)
  change (if keep .X x ∧ keep .Y y ∧ keep .Z z then ∏ a, core a else 0) ≠ 0 at hcoeff
  have hall : keep .X x ∧ keep .Y y ∧ keep .Z z := by
    by_contra hnot
    rw [if_neg hnot] at hcoeff
    exact hcoeff rfl
  have hprod : ∏ a, core a ≠ 0 := by
    rw [if_pos hall] at hcoeff
    exact hcoeff
  have hkeep (W : Side) : keep W (constituentExactSideWord x y z W) := by
    cases W with
    | X => simpa only [constituentExactSideWord] using hall.1
    | Y => simpa only [constituentExactSideWord] using hall.2.1
    | Z => simpa only [constituentExactSideWord] using hall.2.2
  intro t r v S0 S1 S2 h12 h10 h20 hzero σ
  let a := Fintype.equivFin (ConstituentTerm p) ⟨t, r, v⟩
  have ha : constituentIndex (p := p) a = ⟨t, r, v⟩ := by
    simpa only [a, constituentIndex] using
      (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply ⟨t, r, v⟩
  have hcore : core a ≠ 0 := by
    intro hz
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ a) hz)
  have hcon (i : Fin (k a)) :
      conZ q w (constituentOutI (p := p) a) (constituentOutJ (p := p) a)
        (constituentOutK (p := p) a) (x a i) (y a i) (z a i) ≠ 0 := by
    intro hi
    apply hcore
    unfold core tensorPower
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hdata (i : Fin (k a)) :=
    constituentExact_conZ_ne_data (x a i) (y a i) (z a i) (hcon i)
  have hlevel (i : Fin (k a)) :
      chunkLvl (chunkOf (constituentExactSideWord (x a i) (y a i) (z a i) S0)) =
        coord S0 v.1 := by
    cases S0 with
    | X =>
      change levOf (x a i) = coord .X v.1
      have hx := (hdata i).1
      unfold constituentOutI at hx
      rw [ha] at hx
      exact hx
    | Y =>
      change levOf (y a i) = coord .Y v.1
      have hy := (hdata i).2.1
      unfold constituentOutJ at hy
      rw [ha] at hy
      exact hy
    | Z =>
      change levOf (z a i) = coord .Z v.1
      have hz := (hdata i).2.2.1
      unfold constituentOutK at hz
      rw [ha] at hz
      exact hz
  have hreflect (i : Fin (k a)) :
      chunkOf (constituentExactSideWord (x a i) (y a i) (z a i) S2) =
        reflect (chunkOf (constituentExactSideWord (x a i) (y a i) (z a i) S1)) := by
    apply constituentExact_chunk_reflect (x a i) (y a i) (z a i) S1 S2 S0
      h12 h10 h20
    · exact (hdata i).2.2.2
    · rw [hlevel i, hzero]
  have hreflect' (i : Fin (k a)) :
      chunkOf (constituentExactSideWord x y z S2 a i) =
        reflect (chunkOf (constituentExactSideWord x y z S1 a i)) := by
    cases S1 <;> cases S2 <;> simpa only [constituentExactSideWord] using hreflect i
  have hcount :
      ADVXXZ.typeCnt (chunkSeq (constituentExactSideWord x y z S1 a)) σ =
        ADVXXZ.typeCnt (chunkSeq (constituentExactSideWord x y z S2 a)) (reflect σ) := by
    unfold ADVXXZ.typeCnt
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, chunkSeq,
      constituentExactSideWord_apply]
    rw [hreflect' i]
    constructor
    · intro hi
      rw [hi]
    · intro hi
      have hr := congrArg reflect hi
      simpa only [constituentExact_reflect_reflect] using hr
  calc
    constituentChildCount28 h S1 t r v σ =
        ADVXXZ.typeCnt (chunkSeq (constituentExactSideWord x y z S1 a)) σ := by
      exact (hkeep S1 a σ).symm
    _ = ADVXXZ.typeCnt (chunkSeq (constituentExactSideWord x y z S2 a)) (reflect σ) := hcount
    _ = constituentChildCount28 h S2 t r v (reflect σ) := hkeep S2 a (reflect σ)

theorem constituent_grid_boundary_or_zero28 {w s : ℕ} {p : ConstituentInput w s}
    (q : ℕ) (d : ConstituentSpec p) (m : ℕ) (h : ConstituentExactGrid27 d m) :
    ConstituentGridBoundary28 h ∨ (constituentGridTensorZ27 q d m h).tensor = 0 := by
  by_cases hb : ConstituentGridBoundary28 h
  · exact Or.inl hb
  · right
    funext x y z
    apply Classical.byContradiction
    intro hc
    exact hb (constituentGridBoundary_of_coeff_ne_zero36 d m h x y z hc)

theorem constituent_grid_admissible28 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b m : ℕ) (hd : ConstituentAdmissibleAt d b)
    (h : ConstituentExactGrid27 d m) (hboundary : ConstituentGridBoundary28 h) :
    ConstituentAdmissibleAt (constituentGridSpec27 d hd m h) b := by
  classical
  refine
    { roles := hd.roles
      mixture := ?_
      pair_mixture := constituentGridSpec27_pair_mixture d m h
      regional_support := constituentGridRegion_supported27 d hd m h
      child_support := constituentGridBeta_supported27 d hd m h
      child_boundary := ?_
      out_eq := hd.out_eq }
  · intro W t σ
    change (mixtureDist27 (d.A t) (constituentGridRegionBeta27 d m h W t)).prob σ =
      ∑ r, (d.A t).prob r * (constituentGridRegionBeta27 d m h W t r).prob σ
    exact mixtureDist27_prob (d.A t) (constituentGridRegionBeta27 d m h W t) σ
  · intro t r u Z X Y hXY hXZ hYZ hzero σ
    change (constituentGridBeta27 d m h X t r u).prob σ =
      (constituentGridBeta27 d m h Y t r u).prob (reflect σ)
    let a := Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩
    by_cases hn : 0 < constituentOutN d.toPaper m a
    · rw [constituentGridBeta27_prob_pos d m h X t r u σ hn,
        constituentGridBeta27_prob_pos d m h Y t r u (reflect σ) hn]
      have hc := hboundary t r u Z X Y hXY hXZ hYZ hzero σ
      exact congrArg (fun n : ℕ =>
        (n : ℚ) / (constituentOutN d.toPaper m a : ℚ)) hc
    · unfold constituentGridBeta27
      dsimp only
      rw [dif_neg hn, dif_neg hn]
      exact hd.child_boundary t r u Z X Y hXY hXZ hYZ hzero σ

#print axioms constituent_grid_boundary_or_zero28
#print axioms constituent_grid_admissible28

end OmegaBound.ADVXXZGeneral
