import OmegaBound.ADVXXZGeneralGlobalExactGateAssembly

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The exact integral tensor attached to one target label of a global region. -/
def globalExactITensor27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label) : ITensor :=
  { X := GlobalExactLeg27 q g n xi r j .X
    Y := GlobalExactLeg27 q g n xi r j .Y
    Z := GlobalExactLeg27 q g n xi r j .Z
    tensor := globalExactTensorZ27 q g n xi r j }

private theorem scaledGlobalCount_eqGR27 (b m k : ℕ) (a : ℚ)
    (hk : (b : ℚ) * a = (k : ℚ)) :
    (((b*m : ℕ) : ℚ) * a).floor.toNat = k*m := by
  have hq : (((b*m : ℕ) : ℚ) * a) = ((k*m : ℕ) : ℚ) := by
    push_cast
    rw [← hk]
    ring
  rw [hq]
  have hf : (((k*m : ℕ) : ℚ).floor) = (k*m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (k*m) 1
  rw [hf]
  have hz : (k : ℤ) * (m : ℤ) = ((k*m : ℕ) : ℤ) := by norm_num
  rw [hz, Int.toNat_natCast]

/-- The six exact global populations partition the supplied lattice length. -/
theorem globalPopulation_sum27 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b*m)) (hb : GlobalIntegral g b) :
    ∑ r : Fin 6, (globalPopulation g (b*m) xi r).n = b*m := by
  classical
  let k : Fin 6 → Shape w → ℕ := fun r u =>
    Classical.choose ((hb.2 r).2 u).1
  have hk : ∀ r u, (b : ℚ) * g.joint.prob (r, u) = (k r u : ℚ) :=
    fun r u => Classical.choose_spec ((hb.2 r).2 u).1
  have hcount : ∀ r u,
      (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = k r u * m :=
    fun r u => scaledGlobalCount_eqGR27 b m (k r u) (g.joint.prob (r, u)) (hk r u)
  have hksum : ∑ r : Fin 6, ∑ u : Shape w, k r u = b := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    calc
      ∑ r : Fin 6, ∑ u : Shape w, (k r u : ℚ) =
          ∑ r : Fin 6, ∑ u : Shape w, (b : ℚ) * g.joint.prob (r, u) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro u _hu
        exact (hk r u).symm
      _ = (b : ℚ) * ∑ ru : Fin 6 × Shape w, g.joint.prob ru := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum]
      _ = (b : ℚ) := by rw [g.joint.sum_prob, mul_one]
  change ∑ r : Fin 6, ∑ u : Shape w,
      (((b*m : ℕ) : ℚ) * g.joint.prob (r, u)).floor.toNat = b*m
  simp_rw [hcount]
  simp_rw [← Finset.sum_mul]
  rw [hksum]

/-- One region contains no more positions than the complete global lattice. -/
theorem globalPopulation_n_le27 {w b m : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g (b*m)) (hb : GlobalIntegral g b) (r : Fin 6) :
    (globalPopulation g (b*m) xi r).n ≤ b*m := by
  calc
    (globalPopulation g (b*m) xi r).n ≤
        ∑ s : Fin 6, (globalPopulation g (b*m) xi s).n :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Fin 6 => (globalPopulation g (b*m) xi s).n)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    _ = b*m := globalPopulation_sum27 g xi hb

private theorem repairCapacity_of_paperBound27 (P L holes parts : ℕ)
    (hPL : P ≤ L) (hL : 0 < L)
    (hholes : (holes : ℝ) ≤ (1 / (8 * L) : ℝ) * parts) :
    4 * (2 * P) * holes ≤ parts := by
  have hdenNat : 0 < 8 * L := Nat.mul_pos (by norm_num) hL
  have hden : 0 < ((8 * L : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have hscaledReal : (((8 * L : ℕ) : ℝ) * holes) ≤ parts := by
    calc
      (((8 * L : ℕ) : ℝ) * holes) ≤
          ((8 * L : ℕ) : ℝ) * ((1 / (8 * L) : ℝ) * parts) :=
        mul_le_mul_of_nonneg_left hholes hden.le
      _ = parts := by
        push_cast
        field_simp
  have hscaledNat : 8 * L * holes ≤ parts := by exact_mod_cast hscaledReal
  calc
    4 * (2 * P) * holes = 8 * P * holes := by ring
    _ ≤ 8 * L * holes := Nat.mul_le_mul_right holes (Nat.mul_le_mul_left 8 hPL)
    _ ≤ parts := hscaledNat

/-- The paper's `1/(8N)` hole threshold supplies the literal hole-repair capacity. -/
theorem globalPaperHole_capacity27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hw : 0 < w) (hb : GlobalIntegral g b)
    (m : ℕ) (hm : 0 < m) (xi : ExactGrid g (b*m)) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b*m) xi r) M)
    (j : GlobalTargetLabel27 g xi r)
    (hgood : ∀ W, ((globalExactHoles27 g xi r B omega j W).card : ℝ) ≤
      (1 / (8 * (w * (b*m) : ℕ)) : ℝ) *
        Fintype.card (GlobalExactPart27 g (b*m) xi r j.val W))
    (W : Side) :
    4 * (2 * (globalPopulation g (b*m) xi r).n) *
        (globalExactHoles27 g xi r B omega j W).card ≤
      Fintype.card (GlobalExactPart27 g (b*m) xi r j.val W) := by
  apply repairCapacity_of_paperBound27
    (globalPopulation g (b*m) xi r).n (w * (b*m))
    (globalExactHoles27 g xi r B omega j W).card
    (Fintype.card (GlobalExactPart27 g (b*m) xi r j.val W))
  · exact (globalPopulation_n_le27 g xi hb r).trans
      (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (b*m) (Nat.succ_le_iff.mpr hw))
  · exact Nat.mul_pos hw (Nat.mul_pos hb.1 hm)
  · exact hgood W

private def transportedGlobalHoles27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side) :
    Finset (GlobalExactPart27 g n xi r j W) :=
  (globalExactHoles27 g xi r B omega ⟨k, hk⟩ W).map
    (globalLabelExactPartEquiv27 q g xi r j k hj hk W).symm.toEmbedding

private theorem transportedGlobalHoles_card27 {w n M : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side) :
    (transportedGlobalHoles27 q g xi r B omega j k hj hk W).card =
      (globalExactHoles27 g xi r B omega ⟨k, hk⟩ W).card := by
  rw [transportedGlobalHoles27, Finset.card_map]

private theorem mem_transportedGlobalHoles27 {w n M : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side)
    (a : GlobalExactPart27 g n xi r j W) :
    a ∈ transportedGlobalHoles27 q g xi r B omega j k hj hk W ↔
      globalLabelExactPartEquiv27 q g xi r j k hj hk W a ∈
        globalExactHoles27 g xi r B omega ⟨k, hk⟩ W := by
  simp [transportedGlobalHoles27]

private theorem boxZO_restricts_subtypeGR27
    {R X Y Z PX PY PZ : Type*} [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
    (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ)
    (A : Finset PX) (C : Finset PY) (E : Finset PZ) (T : Tensor3 R X Y Z) :
    Restricts (boxZO pX pY pZ A C E T)
      (fun x : {x // pX x ∈ A} => fun y : {y // pY y ∈ C} =>
        fun z : {z // pZ z ∈ E} => T x.val y.val z.val) := by
  classical
  refine ⟨(fun x x' => if x'.val = x then 1 else 0),
    (fun y y' => if y'.val = y then 1 else 0),
    (fun z z' => if z'.val = z then 1 else 0), ?_⟩
  funext x y z
  simp only [Tensor3.act]
  by_cases hx : pX x ∈ A
  · rw [Finset.sum_eq_single ⟨x, hx⟩]
    · by_cases hy : pY y ∈ C
      · rw [Finset.sum_eq_single ⟨y, hy⟩]
        · by_cases hz : pZ z ∈ E
          · rw [Finset.sum_eq_single ⟨z, hz⟩]
            · simp [boxZO, hx, hy, hz]
            · intro z' _ hz'
              have hne : z'.val ≠ z := fun h => hz' (Subtype.ext h)
              simp [hne]
            · intro h
              exact (h (Finset.mem_univ (⟨z, hz⟩ : {z // pZ z ∈ E}))).elim
          · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hz]]
            symm
            apply Finset.sum_eq_zero
            intro z' _
            have hne : z'.val ≠ z := fun h => hz (h ▸ z'.property)
            simp [hne]
        · intro y' _ hy'
          rw [Finset.sum_eq_zero]
          intro z' _
          have hne : y'.val ≠ y := fun h => hy' (Subtype.ext h)
          simp [hne]
        · intro h
          exact (h (Finset.mem_univ (⟨y, hy⟩ : {y // pY y ∈ C}))).elim
      · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hy]]
        symm
        apply Finset.sum_eq_zero
        intro y' _
        apply Finset.sum_eq_zero
        intro z' _
        have hne : y'.val ≠ y := fun h => hy (h ▸ y'.property)
        simp [hne]
    · intro x' _ hx'
      rw [Finset.sum_eq_zero]
      intro y' _
      rw [Finset.sum_eq_zero]
      intro z' _
      have hne : x'.val ≠ x := fun h => hx' (Subtype.ext h)
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ (⟨x, hx⟩ : {x // pX x ∈ A}))).elim
  · rw [show boxZO pX pY pZ A C E T x y z = 0 by simp [boxZO, hx]]
    symm
    apply Finset.sum_eq_zero
    intro x' _
    apply Finset.sum_eq_zero
    intro y' _
    apply Finset.sum_eq_zero
    intro z' _
    have hne : x'.val ≠ x := fun h => hx (h ▸ x'.property)
    simp [hne]

private abbrev GlobalBrokenLegGR27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (k : (globalPopulation g n xi r).Label) (W : Side) :=
  {x : GlobalPhysicalWord q g n xi r //
    (globalPopulation g n xi r).incidence W k (globalPhysicalPart q g n xi r W x) ∧
      globalPartKeep g n xi r M B omega .zUseful W
        (globalPhysicalPart q g n xi r W x)}

private def globalBrokenLegEquivGR27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (k : (globalPopulation g n xi r).Label) (W : Side) :
    GlobalBrokenLegGR27 q g xi r B omega k W ≃
      (globalBrokenCopyZ q g n xi r M B omega k).leg W := by
  cases W <;> exact Equiv.refl _

private def globalBoxToBrokenLegGR27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) (W : Side) :
    {x : GlobalExactLeg27 q g n xi r j W //
      globalExactPart27 q g n xi r j W x ∈
        (transportedGlobalHoles27 q g xi r B omega j k hj hk W)ᶜ} →
      (globalBrokenCopyZ q g n xi r M B omega k).leg W := by
  intro x
  let y := globalLabelExactLegEquiv27 q g xi r j k hj hk W x.val
  have hnotRef : globalExactPart27 q g n xi r j W x.val ∉
      transportedGlobalHoles27 q g xi r B omega j k hj hk W := by
    simpa using x.property
  have hkeep : globalPartKeep g n xi r M B omega .zUseful W
      (globalPhysicalPart q g n xi r W y.val) := by
    by_contra hnot
    apply hnotRef
    apply (mem_transportedGlobalHoles27 q g xi r B omega j k hj hk W
      (globalExactPart27 q g n xi r j W x.val)).2
    rw [globalLabelExactPart_comm27 q g xi r j k hj hk W x.val]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
  have hinc : (globalPopulation g n xi r).incidence W k
      (globalPhysicalPart q g n xi r W y.val) := y.property
  exact globalBrokenLegEquivGR27 q g xi r B omega k W ⟨y.val, hinc, hkeep⟩

set_option maxHeartbeats 1000000 in
-- The transported exact-part subtypes require extra elaboration time.
/-- A common-label exact box is a restriction of the corresponding physical broken copy. -/
theorem globalCommonBox_restricts_broken27 {w n M : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (j k : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    (hk : k ∈ (globalPopulation g n xi r).target) :
    Restricts
      (boxZO (globalExactPart27 q g n xi r j .X)
        (globalExactPart27 q g n xi r j .Y)
        (globalExactPart27 q g n xi r j .Z)
        (transportedGlobalHoles27 q g xi r B omega j k hj hk .X)ᶜ
        (transportedGlobalHoles27 q g xi r B omega j k hj hk .Y)ᶜ
        (transportedGlobalHoles27 q g xi r B omega j k hj hk .Z)ᶜ
        (globalExactTensorZ27 q g n xi r j))
      (globalBrokenCopyZ q g n xi r M B omega k).tensor := by
  let HX := transportedGlobalHoles27 q g xi r B omega j k hj hk .X
  let HY := transportedGlobalHoles27 q g xi r B omega j k hj hk .Y
  let HZ := transportedGlobalHoles27 q g xi r B omega j k hj hk .Z
  have hbox := boxZO_restricts_subtypeGR27
    (globalExactPart27 q g n xi r j .X)
    (globalExactPart27 q g n xi r j .Y)
    (globalExactPart27 q g n xi r j .Z) HXᶜ HYᶜ HZᶜ
    (globalExactTensorZ27 q g n xi r j)
  refine Tensor3.Restricts.trans hbox (ADVXXZ.restricts_of_sub
    (globalBoxToBrokenLegGR27 q g xi r B omega j k hj hk .X)
    (globalBoxToBrokenLegGR27 q g xi r B omega j k hj hk .Y)
    (globalBoxToBrokenLegGR27 q g xi r B omega j k hj hk .Z) ?_)
  intro x y z
  simpa only [globalBrokenCopyZ, globalBoxToBrokenLegGR27,
    globalBrokenLegEquivGR27, ITensor.leg] using
      (globalLabelExactTensor_equiv27 q g xi r j k hj hk x.val y.val z.val).symm

set_option maxHeartbeats 1000000 in
-- Dependent sigma-leg sums require normalization after all index equalities are split.
private theorem famDS_restricts_dependentSumGR27
    {X' Y' Z' iota : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype iota] [DecidableEq iota]
    (Bf : iota → Tensor3 ℤ X' Y' Z') (T : iota → ITensor)
    (h : ∀ i, Restricts (Bf i) (T i).tensor) :
    Restricts (famDS (Finset.univ : Finset iota) Bf) (dependentSumZ T).tensor := by
  classical
  choose A1 A2 A3 hA using h
  refine ⟨fun p q => if hq : q.1 = p.1 then A1 p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A2 p.1 p.2 (hq ▸ q.2) else 0,
    fun p q => if hq : q.1 = p.1 then A3 p.1 p.2 (hq ▸ q.2) else 0, ?_⟩
  funext p q s
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  obtain ⟨k, z⟩ := s
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik
      have hv := congrFun (congrFun (congrFun (hA i) x) y) z
      simp only [famDS, Finset.mem_univ, and_self, if_true]
      rw [hv]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      simp
    · simp only [famDS, true_and, Finset.mem_univ, and_true, hik, if_false]
      simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      have hki : k ≠ i := Ne.symm hik
      simp [hik, hki]
  · simp only [famDS, hij, false_and, if_false]
    simp only [Tensor3.act, dependentSumZ, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]
    intro hkj hki
    exact (hij (hki.symm.trans hkj)).elim

private theorem sum_side_threeGR27 (f : Side → ℕ) :
    ∑ W, f W = f .X + f .Y + f .Z := by
  rw [show (Finset.univ : Finset Side) = {.X, .Y, .Z} by decide +kernel]
  simp [Nat.add_assoc]

set_option maxHeartbeats 1000000 in
-- The global exact-part families require the larger elaboration allowance.
/-- One full reserve-sized group of good global labels repairs to a reference exact tensor. -/
theorem globalRepairExactGroup27 {w n M : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j : GlobalTargetLabel27 g xi r)
    (hn : (globalPopulation g n xi r).n ≠ 0)
    (K : Fin (repairReserve (2 * (globalPopulation g n xi r).n)
      (fun W => Fintype.card (GlobalExactPart27 g n xi r j.val W))) →
        GlobalTargetLabel27 g xi r)
    (hKcapacity : ∀ i W,
      4 * (2 * (globalPopulation g n xi r).n) *
          (globalExactHoles27 g xi r B omega (K i) W).card ≤
        Fintype.card (GlobalExactPart27 g n xi r (K i).val W)) :
    Restricts (globalExactTensorZ27 q g n xi r j.val)
      (dependentSumZ fun i =>
        globalBrokenCopyZ q g n xi r M B omega (K i).val).tensor := by
  classical
  let P := globalPopulation g n xi r
  let reserve := repairReserve (2 * P.n)
    (fun W => Fintype.card (GlobalExactPart27 g n xi r j.val W))
  let holes := fun i W => transportedGlobalHoles27 q g xi r B omega
    j.val (K i).val j.property (K i).property W
  have hcap (i : Fin reserve) (W : Side) :
      4 * (2 * P.n) * (holes i W).card ≤
        Fintype.card (GlobalExactPart27 g n xi r j.val W) := by
    change 4 * (2 * P.n) *
        (transportedGlobalHoles27 q g xi r B omega
          j.val (K i).val j.property (K i).property W).card ≤ _
    rw [transportedGlobalHoles_card27]
    calc
      4 * (2 * P.n) * (globalExactHoles27 g xi r B omega (K i) W).card ≤
          Fintype.card (GlobalExactPart27 g n xi r (K i).val W) := hKcapacity i W
      _ = Fintype.card (GlobalExactPart27 g n xi r j.val W) :=
        Fintype.card_congr (globalLabelExactPartEquiv27 q g xi r
          (K i).val j.val (K i).property j.property W)
  have hreserve :
      4 ^ (Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .X)) +
        Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .Y)) +
        Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .Z)) + 1) ≤
        Fintype.card (Fin reserve) := by
    simp only [Fintype.card_fin]
    rw [show reserve = 4 ^
        (Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .X)) +
         Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .Y)) +
         Nat.log (2 * P.n) (Fintype.card (GlobalExactPart27 g n xi r j.val .Z)) + 1) by
      simp only [reserve, repairReserve, sum_side_threeGR27]]
  have hPpos : 0 < P.n := by
    exact Nat.pos_of_ne_zero (by simpa only [P] using hn)
  have hD : 2 ≤ 2 * P.n := by omega
  have hfix := global_exact_repair_application q g xi r j.val j.property
    (2 * P.n) hD holes (fun i W => hcap i W)
    (Finset.univ : Finset (Fin reserve)) hreserve
  refine Tensor3.Restricts.trans hfix
    (famDS_restricts_dependentSumGR27
      (fun i => boxZO (globalExactPart27 q g n xi r j.val .X)
        (globalExactPart27 q g n xi r j.val .Y)
        (globalExactPart27 q g n xi r j.val .Z)
        (holes i .X)ᶜ (holes i .Y)ᶜ (holes i .Z)ᶜ
        (globalExactTensorZ27 q g n xi r j.val))
      (fun i => globalBrokenCopyZ q g n xi r M B omega (K i).val) ?_)
  intro i
  exact globalCommonBox_restricts_broken27 q g xi r B omega
    j.val (K i).val j.property (K i).property

/-- The numeric position of a member of a complete global repair group. -/
def globalRepairGroupIndex27 (good copies reserve : ℕ)
    (hprefix : copies * reserve ≤ good) : Fin copies × Fin reserve → Fin good :=
  fun gi => Fin.castLE hprefix (finProdFinEquiv gi)

/-- The first complete repair groups in a finite family of global labels. -/
def globalRepairGroupLabel27 {L : Type*} [Fintype L] [DecidableEq L]
    (J : Finset L) (copies reserve : ℕ) (hprefix : copies * reserve ≤ J.card) :
    Fin copies × Fin reserve → {j // j ∈ J} := fun gi =>
  let e : Fin J.card ≃ {j // j ∈ J} :=
    (finCongr (Fintype.card_coe J).symm).trans (Fintype.equivFin {j // j ∈ J}).symm
  e (globalRepairGroupIndex27 J.card copies reserve hprefix gi)

theorem globalRepairGroupLabel27_injective {L : Type*} [Fintype L] [DecidableEq L]
    (J : Finset L) (copies reserve : ℕ) (hprefix : copies * reserve ≤ J.card) :
    Function.Injective (globalRepairGroupLabel27 J copies reserve hprefix) := by
  intro a b hab
  apply finProdFinEquiv.injective
  apply Fin.castLE_injective hprefix
  exact ((finCongr (Fintype.card_coe J).symm).trans
    (Fintype.equivFin {j // j ∈ J}).symm).injective hab

private theorem nestedDependentSumZ_restrictsGR27
    {kappa iota L : Type} [Fintype kappa] [DecidableEq kappa]
    [Fintype iota] [DecidableEq iota] [Fintype L] [DecidableEq L]
    (U : L → ITensor) (e : kappa × iota → L) (he : Function.Injective e) :
    Restricts
      (dependentSumZ fun k => dependentSumZ fun i => U (e (k, i))).tensor
      (dependentSumZ U).tensor := by
  classical
  refine ADVXXZ.restricts_of_sub
    (fun x => ⟨e (x.1, x.2.1), x.2.2⟩)
    (fun y => ⟨e (y.1, y.2.1), y.2.2⟩)
    (fun z => ⟨e (z.1, z.2.1), z.2.2⟩) ?_
  rintro ⟨a, i, x⟩ ⟨b, j, y⟩ ⟨c, k, z⟩
  simp only [dependentSumZ]
  by_cases hab : (a, i) = (b, j)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    by_cases hac : (a, i) = (c, k)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
      simp
    · have heac : e (a, i) ≠ e (c, k) := fun h => hac (he h)
      by_cases hac0 : a = c
      · subst hac0
        have hik : i ≠ k := fun h => hac (congrArg (fun t => (a, t)) h)
        simp [hik, heac]
      · simp [hac0, heac]
  · have heab : e (a, i) ≠ e (b, j) := fun h => hab (he h)
    by_cases hab0 : a = b
    · subst hab0
      have hij : i ≠ j := fun h => hab (congrArg (fun t => (a, t)) h)
      simp [hij, heab]
    · simp [hab0, heab]

set_option maxHeartbeats 1000000 in
-- The quotient repeats the dependent global family in the full prefix and remainder.
/-- Complete repair groups in one region produce the quotient number of exact copies. -/
theorem globalRepairRegionalQuotient27 {w n M : ℕ} (q : ℕ)
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (globalPopulation g n xi r) M)
    (J : Finset (GlobalTargetLabel27 g xi r))
    (j0 : GlobalTargetLabel27 g xi r)
    (hJcapacity : ∀ j, j ∈ J → ∀ W,
      4 * (2 * (globalPopulation g n xi r).n) *
          (globalExactHoles27 g xi r B omega j W).card ≤
        Fintype.card (GlobalExactPart27 g n xi r j.val W))
    (hn : (globalPopulation g n xi r).n ≠ 0)
    (hcopies : 0 < J.card / repairReserve (2 * (globalPopulation g n xi r).n)
      (fun W => Fintype.card (GlobalExactPart27 g n xi r j0.val W))) :
    let reserve := repairReserve (2 * (globalPopulation g n xi r).n)
      (fun W => Fintype.card (GlobalExactPart27 g n xi r j0.val W))
    Restricts (copiesZ (J.card / reserve) (globalExactITensor27 q g xi r j0.val)).tensor
      (dependentSumZ fun k : {k // k ∈ J} =>
        globalBrokenCopyZ q g n xi r M B omega k.val.val).tensor := by
  classical
  let parts := fun W => Fintype.card (GlobalExactPart27 g n xi r j0.val W)
  let reserve := repairReserve (2 * (globalPopulation g n xi r).n) parts
  let copies := J.card / reserve
  have hcopies0 : 0 < copies := by simpa only [parts, reserve, copies] using hcopies
  have hprefix : copies * reserve ≤ J.card := Nat.div_mul_le_self J.card reserve
  have hreserve : 0 < reserve := repairReserve_pos _ _
  let e := globalRepairGroupLabel27 J copies reserve hprefix
  have he : Function.Injective e :=
    globalRepairGroupLabel27_injective J copies reserve hprefix
  have hgroup (c : Fin copies) : Restricts (globalExactTensorZ27 q g n xi r j0.val)
      (dependentSumZ fun i : Fin reserve =>
        globalBrokenCopyZ q g n xi r M B omega (e (c, i)).val.val).tensor := by
    apply globalRepairExactGroup27 q g xi r B omega j0 hn
    intro i W
    exact hJcapacity (e (c, i)).val (e (c, i)).property W
  let U := fun k : {k // k ∈ J} =>
    globalBrokenCopyZ q g n xi r M B omega k.val.val
  have hgroups : Restricts
      (copiesZ copies (globalExactITensor27 q g xi r j0.val)).tensor
      (dependentSumZ fun c : Fin copies =>
        dependentSumZ fun i : Fin reserve => U (e (c, i))).tensor := by
    simpa only [copiesZ, globalExactITensor27] using
      famDS_restricts_dependentSumGR27
        (fun _c : Fin copies => globalExactTensorZ27 q g n xi r j0.val)
        (fun c : Fin copies => dependentSumZ fun i : Fin reserve => U (e (c, i))) hgroup
  have hreindex : Restricts
      (dependentSumZ fun c : Fin copies =>
        dependentSumZ fun i : Fin reserve => U (e (c, i))).tensor
      (dependentSumZ U).tensor := nestedDependentSumZ_restrictsGR27 U e he
  dsimp only
  have hparts : (fun W => Fintype.card (GlobalExactPart27 g n xi r j0.val W)) = parts := rfl
  rw [hparts]
  exact Tensor3.Restricts.trans hgroups hreindex

set_option maxHeartbeats 1000000 in
-- The exact-part family occurs in both the quotient divisor and dependent tensor sum.
/-- The paper-good labels repair once their cardinality contains one complete reserve group. -/
theorem globalRepairPaperGoodFamily27 {w b M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hw : 0 < w) (hb : GlobalIntegral g b)
    (m : ℕ) (hm : 0 < m) (xi : ExactGrid g (b * m)) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b * m) xi r) M)
    (j0 : GlobalTargetLabel27 g xi r)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (hcopies : 0 < (globalPaperGoodTargets27 g m xi r B omega j0).card /
      repairReserve (2 * (globalPopulation g (b * m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val W))) :
    let J := globalPaperGoodTargets27 g m xi r B omega j0
    let reserve := repairReserve (2 * (globalPopulation g (b * m) xi r).n)
      (fun W => Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val W))
    Restricts (copiesZ (J.card / reserve)
        (globalExactITensor27 q g xi r j0.val)).tensor
      (dependentSumZ fun k : {k // k ∈ J} =>
        globalBrokenCopyZ q g (b * m) xi r M B omega k.val.val).tensor := by
  let J := globalPaperGoodTargets27 g m xi r B omega j0
  have hcapacity : ∀ j, j ∈ J → ∀ W,
      4 * (2 * (globalPopulation g (b * m) xi r).n) *
          (globalExactHoles27 g xi r B omega j W).card ≤
        Fintype.card (GlobalExactPart27 g (b * m) xi r j.val W) := by
    intro j hj W
    have hjgood : ∀ S, ((globalExactHoles27 g xi r B omega j S).card : ℝ) ≤
        (1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
          Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val S) :=
      (Finset.mem_filter.mp (by simpa only [J, globalPaperGoodTargets27] using hj)).2
    apply globalPaperHole_capacity27 g hw hb m hm xi r B omega j
    intro S
    rw [← Fintype.card_congr (globalLabelExactPartEquiv27 q g xi r
      j0.val j.val j0.property j.property S)]
    exact hjgood S
  exact globalRepairRegionalQuotient27 q g xi r B omega J j0 hcapacity hn hcopies

end
end OmegaBound.ADVXXZGeneral
end
