import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixAtom

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6SplitTargetData (TargetNode wordId wordOfId wordEquiv targetDen)
open OmegaBound.ADVXXZT6Round82 (sideIndex)

/-- The `Q3` boundary cell for one fixed non-interior kind. -/
private def OrdinaryQ3Cell (kind : OmegaBound.ADVXXZLevel2Closure.Kind) : Prop :=
  ∀ (W : Side) (fr : ℚ) (v : Shape 2) (rot : Fin 3) (mu : ℕ),
    mu ≤ ordinaryD / 2 →
    (coord .X v, coord .Y v, coord .Z v) =
      OmegaBound.ADVXXZLevel2Closure.shapeAt kind rot →
    ordinaryAtomRate 5 W (fr, (⟨2, v, fun V σ =>
        (((TargetNode.mk kind rot mu).raw (sideIndex V)).nums (wordId σ) : ℚ) /
          (ordinaryD : ℚ)⟩ : AtomKey)) =
      (fr : ℝ) * OmegaBound.ADVXXZLevel2Closure.rotate
        (OmegaBound.ADVXXZLevel2Closure.matrixStandard 5 kind
          ((mu : ℝ) / (ordinaryD : ℝ)))
        rot (sideIndex W)

private theorem q3_cell_k022_32 : OrdinaryQ3Cell .k022 := by
  intro W fr v rot mu hmu hshape
  rw [ordinaryAtomRate_wordRate32 W fr v
    (fun V => ((TargetNode.mk .k022 rot mu).raw (sideIndex V)).nums)]
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot <;> cases W
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp only [ordinaryAtomSide32]
  all_goals split_ifs with hact
  all_goals first
    | (exfalso; obtain ⟨ha, hb, hc⟩ := hact; omega)
    | exact (hact ⟨by omega, by omega, by omega⟩).elim
    | (rw [wordRate_mu_32 _ mu hmu rfl rfl rfl rfl rfl rfl rfl rfl rfl]
       simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)
    | (simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)

private theorem q3_cell_k013_32 : OrdinaryQ3Cell .k013 := by
  intro W fr v rot mu hmu hshape
  rw [ordinaryAtomRate_wordRate32 W fr v
    (fun V => ((TargetNode.mk .k013 rot mu).raw (sideIndex V)).nums)]
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot <;> cases W
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp only [ordinaryAtomSide32]
  all_goals split_ifs with hact
  all_goals first
    | (exfalso; obtain ⟨ha, hb, hc⟩ := hact; omega)
    | exact (hact ⟨by omega, by omega, by omega⟩).elim
    | (rw [wordRate_13_32 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl]
       simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)
    | (rw [wordRate_57_32 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl]
       simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)
    | (simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)

private theorem q3_cell_k031_32 : OrdinaryQ3Cell .k031 := by
  intro W fr v rot mu hmu hshape
  rw [ordinaryAtomRate_wordRate32 W fr v
    (fun V => ((TargetNode.mk .k031 rot mu).raw (sideIndex V)).nums)]
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot <;> cases W
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp only [ordinaryAtomSide32]
  all_goals split_ifs with hact
  all_goals first
    | (exfalso; obtain ⟨ha, hb, hc⟩ := hact; omega)
    | exact (hact ⟨by omega, by omega, by omega⟩).elim
    | (rw [wordRate_13_32 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl]
       simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)
    | (rw [wordRate_57_32 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl]
       simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)
    | (simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)

private theorem q3_cell_k004_32 : OrdinaryQ3Cell .k004 := by
  intro W fr v rot mu hmu hshape
  rw [ordinaryAtomRate_wordRate32 W fr v
    (fun V => ((TargetNode.mk .k004 rot mu).raw (sideIndex V)).nums)]
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot <;> cases W
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp only [ordinaryAtomSide32]
  all_goals split_ifs with hact
  all_goals first
    | (exfalso; obtain ⟨ha, hb, hc⟩ := hact; omega)
    | (simp [OmegaBound.ADVXXZLevel2Closure.rotate,
         OmegaBound.ADVXXZLevel2Closure.matrixStandard, sideIndex] <;> ring)

/-- **The `Q3` boundary cell.**  A width-two atom whose released child law is the target row
of a NON-interior level-two node contributes exactly the `TermInfoLv2` matrix-size entry of
that node's kind, rotated as MATLAB rotates it. -/
theorem ordinary_boundary_atom_rate32 (W : Side) (fr : ℚ) (v : Shape 2)
    (d : TargetNode) (hmu : d.muNum ≤ ordinaryD / 2)
    (hshape : (coord .X v, coord .Y v, coord .Z v) =
      OmegaBound.ADVXXZLevel2Closure.shapeAt d.kind d.rot)
    (hk : d.kind ≠ .k112) :
    ordinaryAtomRate 5 W (fr, (⟨2, v, fun V σ =>
        ((d.raw (sideIndex V)).nums (wordId σ) : ℚ) / (ordinaryD : ℚ)⟩ : AtomKey)) =
      (fr : ℝ) * OmegaBound.ADVXXZLevel2Closure.rotate
        (OmegaBound.ADVXXZLevel2Closure.matrixStandard 5 d.kind
          ((d.muNum : ℝ) / (ordinaryD : ℝ)))
        d.rot (sideIndex W) := by
  obtain ⟨kind, rot, mu⟩ := d
  cases kind
  · exact absurd rfl hk
  · exact q3_cell_k022_32 W fr v rot mu hmu hshape
  · exact q3_cell_k013_32 W fr v rot mu hmu hshape
  · exact q3_cell_k031_32 W fr v rot mu hmu hshape
  · exact q3_cell_k004_32 W fr v rot mu hmu hshape

end OmegaBound.ADVXXZGeneral
end
