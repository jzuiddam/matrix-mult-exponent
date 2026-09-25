import OmegaBound.ADVXXZGeneralAmend31BoundaryDimensionLowerRate

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

/- The dependent `outerN`/`LowerRate` rescaling exceeds Lean's default elaboration budget. -/
set_option maxHeartbeats 1000000 in
/-- Paper clauses:
`P/constituent.tex:28–39` and `P/numerical.tex:17–27`. -/
theorem accumulated_boundary_lowerRate31 (C : Certificate) (hC : AdmissibleAt C)
    (W : Side) :
  LowerRate (outerN C)
    (fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m W)
    (derivedMatrixRateAt C W) := by
  have hbase := boundary_dimension_lowerRate31 C.q 1 (accumulatedBoundary27 C) W
    hC.q_pos (by norm_num) (accumulated_boundary_admissible31 C hC)
  intro δ hδ
  have hDpos : (0 : ℝ) < (C.D : ℝ) := by exact_mod_cast hC.D_pos
  have hD4 : (0 : ℝ) < (C.D : ℝ)^4 := pow_pos hDpos _
  have hδ' : 0 < δ * (C.D : ℝ)^4 := mul_pos hδ hD4
  rcases hbase (δ * (C.D : ℝ)^4) hδ' with ⟨ε₀, hε₀, hbaseε⟩
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  rcases hbaseε ε hε hεle with ⟨M, hM⟩
  refine ⟨M, fun m hm => ?_⟩
  rcases hM m hm with ⟨hpos, hrate⟩
  refine ⟨by simpa only [one_mul] using hpos, ?_⟩
  have hrateId := accumulated_boundary_rate31 C W
  rw [← hrateId]
  unfold outerN
  have hD4nat : ((C.D^4 : ℕ) : ℝ) = (C.D : ℝ)^4 := by norm_cast
  norm_num at hrate
  rw [Nat.cast_mul, hD4nat]
  calc
    (boundaryRate C.q (accumulatedBoundary27 C) W / (C.D : ℝ)^4 - δ) *
          ((C.D : ℝ)^4 * (m : ℝ)) =
        (boundaryRate C.q (accumulatedBoundary27 C) W -
          δ * (C.D : ℝ)^4) * (m : ℝ) := by
            rw [← mul_assoc, sub_mul, div_mul_cancel₀ _ hD4.ne']
    _ ≤ Real.log (boundaryDimension31 C.q (accumulatedBoundary27 C) m W : ℝ) := hrate

end
end OmegaBound.ADVXXZGeneral
end
