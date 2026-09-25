import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixReduce

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- The three width-one level-one words. -/
theorem chunk1_sum32 {M : Type*} [AddCommMonoid M] (f : Chunk 1 → M) :
    ∑ σ : Chunk 1, f σ =
      f (fun _ => 0) + f (fun _ => 1) + f (fun _ => 2) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 3)).symm f, Fin.sum_univ_three]
  rfl

/-- The released ordinary child law at width one is the point mass on the level of the
child's own `V`-coordinate. -/
theorem ordinaryChildBeta_probR32 (V : Side) (v : Shape 1) (σ : Chunk 1) :
    (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ) =
      if (σ 0).val = coord V v then 1 else 0 := by
  simp only [ordinaryChildBeta, RatDist.prob]
  split_ifs with h <;> norm_num [h]

/-- A point-mass width-one child contributes no entropy and exactly one level-one digit
of value `1` when its `V`-coordinate is `1`. -/
theorem ordinary_pointmass_pieces32 (V : Side) (v : Shape 1) (hV : coord V v = 1) :
    entropyNats (fun σ : Chunk 1 => (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ)) = 0 ∧
      (∑ σ : Chunk 1, (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ) *
          ((Finset.univ.filter (fun i : Fin 1 => (σ i).val = 1)).card : ℝ)) = 1 := by
  have hp : ∀ σ : Chunk 1, (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ) =
      if (σ 0).val = 1 then 1 else 0 := by
    intro σ
    rw [ordinaryChildBeta_probR32 V v σ, hV]
  have h0 : ((fun _ => (0 : Fin 3)) (0 : Fin 1)).val = 0 := rfl
  have h1 : ((fun _ => (1 : Fin 3)) (0 : Fin 1)).val = 1 := rfl
  have h2 : ((fun _ => (2 : Fin 3)) (0 : Fin 1)).val = 2 := rfl
  have hc1 : ((Finset.univ.filter
      (fun i : Fin 1 => ((fun _ => (1 : Fin 3)) i).val = 1)).card : ℝ) = 1 := by
    norm_num
  constructor
  · unfold entropyNats
    rw [chunk1_sum32 (fun σ => (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ) *
      Real.log ((((ordinaryChildBeta V v).prob σ : ℚ) : ℝ)))]
    rw [hp, hp, hp, h0, h1, h2]
    norm_num
  · rw [chunk1_sum32 (fun σ => (((ordinaryChildBeta V v).prob σ : ℚ) : ℝ) *
      ((Finset.univ.filter (fun i : Fin 1 => (σ i).val = 1)).card : ℝ))]
    rw [hp, hp, hp, h0, h1, h2]
    norm_num

/-- **The level-two descendant atom rate.**  Every active width-one child of a released
ordinary level-two parent contributes exactly `outBase * log q`: its law is a point mass
(no entropy) carrying a single level-one digit of value `1`. -/
theorem ordinary_stage2_atom_rate32 (q : ℕ) (W : Side) (fr : ℚ) (v : Shape 1)
    (hact : match W with
      | .X => coord .Y v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Z v
      | .Y => coord .Z v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Y v
      | .Z => coord .X v = 0 ∧ 0 < coord .Y v ∧ 0 < coord .Z v) :
    ordinaryAtomRate q W (fr,
        (⟨1, v, fun V σ => (ordinaryChildBeta V v).prob σ⟩ : AtomKey)) =
      (fr : ℝ) * Real.log (q : ℝ) := by
  have hsum : coord .X v + coord .Y v + coord .Z v = 2 * 1 := v.2
  cases W
  · obtain ⟨hy, hx, hz⟩ := hact
    have hV : coord .X v = 1 := by omega
    obtain ⟨he, hn⟩ := ordinary_pointmass_pieces32 .X v hV
    simp only [ordinaryAtomRate]
    rw [if_pos (⟨hy, hx, hz⟩ : coord .Y v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Z v),
      he, hn]
    ring
  · obtain ⟨hz, hx, hy⟩ := hact
    have hV : coord .X v = 1 := by omega
    obtain ⟨he, hn⟩ := ordinary_pointmass_pieces32 .X v hV
    simp only [ordinaryAtomRate]
    rw [if_pos (⟨hz, hx, hy⟩ : coord .Z v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Y v),
      he, hn]
    ring
  · obtain ⟨hx, hy, hz⟩ := hact
    have hV : coord .Y v = 1 := by omega
    obtain ⟨he, hn⟩ := ordinary_pointmass_pieces32 .Y v hV
    simp only [ordinaryAtomRate]
    rw [if_pos (⟨hx, hy, hz⟩ : coord .X v = 0 ∧ 0 < coord .Y v ∧ 0 < coord .Z v),
      he, hn]
    ring

/-- The directional activity predicate of the ordinary inventory rate at width one. -/
def OrdinaryStage2Active (W : Side) (v : Shape 1) : Prop :=
  match W with
  | .X => coord .Y v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Z v
  | .Y => coord .Z v = 0 ∧ 0 < coord .X v ∧ 0 < coord .Y v
  | .Z => coord .X v = 0 ∧ 0 < coord .Y v ∧ 0 < coord .Z v

instance instDecidableOrdinaryStage2Active (W : Side) (v : Shape 1) :
    Decidable (OrdinaryStage2Active W v) := by
  unfold OrdinaryStage2Active
  cases W <;> infer_instance

/-- **The `Q2` descendant half of the matrix census.**  The level-two stage's whole
inventory rate is `log q` times the active out-base mass; no entropy term survives. -/
theorem ordinary_stage2_inventory_rate32 (W : Side) :
    ordinaryInventoryRate 5 W (QAt releasedOrdinaryCertificatePhysical ordinaryLevel2) =
      Real.log (5 : ℝ) * ∑ x : ConstituentTerm releasedOrdinaryParent,
        (if OrdinaryStage2Active W x.2.2.1 then
          (releasedOrdinaryData2.outBase x : ℝ) else 0) := by
  rw [ordinary_stage_inventory_rate32 W ordinaryLevel2 releasedOrdinaryStep2
    ordinary_stage2_eq32, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : OrdinaryStage2Active W x.2.2.1
  · rw [if_pos h, mul_comm]
    exact ordinary_stage2_atom_rate32 5 W
      ((releasedOrdinaryData2.outBase x : ℕ) : ℚ) x.2.2.1 h
  · rw [if_neg h, mul_zero]
    cases W
    · exact if_neg (fun hc => h hc)
    · exact if_neg (fun hc => h hc)
    · exact if_neg (fun hc => h hc)

/-- For every direction exactly one width-one child shape is active, and it is the shape
whose two nonzero coordinates are both `1`. -/
theorem ordinary_stage2_active_coords32 (W : Side) (v : Shape 1) :
    OrdinaryStage2Active W v ↔
      (match W with
       | .X => coord .X v = 1 ∧ coord .Y v = 0 ∧ coord .Z v = 1
       | .Y => coord .X v = 1 ∧ coord .Y v = 1 ∧ coord .Z v = 0
       | .Z => coord .X v = 0 ∧ coord .Y v = 1 ∧ coord .Z v = 1) := by
  have hsum : coord .X v + coord .Y v + coord .Z v = 2 * 1 := v.2
  cases W <;> unfold OrdinaryStage2Active <;>
    exact ⟨fun h => by omega, fun h => by omega⟩

end OmegaBound.ADVXXZGeneral
end
