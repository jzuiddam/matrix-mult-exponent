import OmegaBound.ADVXXZGeneralCExact33Population

set_option autoImplicit false

/-!
# Reserve domination

The grid-dependent regional reserve
`constituentRegionalReserve33` is dominated by the matching, grid-free factor of
`constituentRepairPool33`.  This is the lemma `constituent_pooled_positive33` needs in order to
pay for the repair out of the uniform pool.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
open StageCandidateRaw
noncomputable section

/-- `RawPopulation.n` is the cardinality of the position type. -/
theorem stagePopulation_n_card (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :
    (stagePopulationAt q p d b m r).n = Fintype.card (StagePos b m p d r) := by
  have h1 : (stagePopulationAt q p d b m r).n
      = @Fintype.card (StagePos b m p d r) (Fintype.ofFinite _) := rfl
  rw [h1]
  exact @Fintype.card_congr _ _ (Fintype.ofFinite _) _ (Equiv.refl _)

/-- Every side of the stage population has exactly `3^(w*N)` parts: the parts are the level-1
words `Pos → Chunk w`. -/
theorem stagePart_card (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) (W : Side) :
    Fintype.card ((stagePopulationAt q p d b m r).Part W)
      = 3 ^ (w * (stagePopulationAt q p d b m r).n) := by
  classical
  have h1 : Fintype.card ((stagePopulationAt q p d b m r).Part W)
      = @Fintype.card (StagePos b m p d r → Chunk w) inferInstance :=
    @Fintype.card_congr _ _ _ inferInstance (Equiv.refl _)
  have hchunk : Fintype.card (Chunk w) = 3 ^ w := by simp [Chunk]
  rw [h1, Fintype.card_fun, hchunk, ← stagePopulation_n_card, ← pow_mul]

/-- `repairReserve` is monotone in the part counts. -/
theorem repairReserve_mono (D : ℕ) (parts parts' : Side → ℕ)
    (hle : ∀ W, parts W ≤ parts' W) :
    repairReserve D parts ≤ repairReserve D parts' := by
  unfold repairReserve
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact Nat.add_le_add_right (Finset.sum_le_sum (fun W _ => Nat.log_mono_right (hle W))) 1

/-- The `r`-th factor of `constituentRepairPool33`, spelled out. -/
def constituentRepairPoolFactor33 (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) : ℕ :=
  if (stagePopulationAt q p d b m r).n = 0 then 1
  else repairReserve ((stagePopulationAt q p d b m r).n)
    (fun _ => 3 ^ (w * (stagePopulationAt q p d b m r).n))

theorem constituentRepairPool33_eq (q : ℕ) {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) :
    constituentRepairPool33 q p d b m
      = ∏ r : Fin 6, constituentRepairPoolFactor33 q p d b m r := rfl

/-- **Reserve domination.**  For every region, the grid-dependent
`constituentRegionalReserve33` is at most the matching grid-free factor of
`constituentRepairPool33`. -/
theorem constituent_reserve_dominated33 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) (r : Fin 6) :
    constituentRegionalReserve33 q P r ≤ constituentRepairPoolFactor33 q p d b m r := by
  classical
  set pg := constituentGridParent27 d hd m h with hpg
  set dg := constituentGridSpec27 d hd m h with hdg
  have hbody : constituentRegionalReserve33 q P r =
      (if (stagePopulationAt q pg dg b m r).n = 0 then 1
       else repairReserve ((stagePopulationAt q pg dg b m r).n)
         (fun W => (P.selected r).sup
           (fun j => (exactPartsAt q b m pg dg r j W).card))) := rfl
  have hN : (stagePopulationAt q pg dg b m r).n = (stagePopulationAt q p d b m r).n :=
    gridPopulation_n_eq q d hd m h r
  rw [hbody, constituentRepairPoolFactor33, hN]
  by_cases hz : (stagePopulationAt q p d b m r).n = 0
  · simp [hz]
  · rw [if_neg hz, if_neg hz]
    refine repairReserve_mono _ _ _ (fun W => ?_)
    refine Finset.sup_le (fun j _ => ?_)
    calc (exactPartsAt q b m pg dg r j W).card
        ≤ Fintype.card ((stagePopulationAt q pg dg b m r).Part W) := Finset.card_le_univ _
      _ = 3 ^ (w * (stagePopulationAt q pg dg b m r).n) := stagePart_card q pg dg b m r W
      _ = 3 ^ (w * (stagePopulationAt q p d b m r).n) := by rw [hN]

/-- The product form: the six grid-dependent reserves are paid for by the uniform pool. -/
theorem constituent_reserve_pool_dominated33 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) :
    (∏ r : Fin 6, constituentRegionalReserve33 q P r)
      ≤ constituentRepairPool33 q p d b m := by
  rw [constituentRepairPool33_eq]
  exact Finset.prod_le_prod' (fun r _ => constituent_reserve_dominated33 q P r)

end
end OmegaBound.ADVXXZGeneral
end
