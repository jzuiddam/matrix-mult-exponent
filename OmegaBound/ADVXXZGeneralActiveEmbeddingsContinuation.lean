import OmegaBound.ADVXXZGeneralActiveEmbeddings

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable section

/- `ADVXXZGeneralActiveEmbeddings` keeps these declarations private.  This command
re-exports kernel-checked aliases of them in this module, selected by their unique suffix. -/
open Lean Elab Command in
private def findEmbeddingCheckpointName
    (env : Environment) (suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains "_private.OmegaBound.ADVXXZGeneralActiveEmbeddings." ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then
    return names[0]
  else
    throwError "expected one embedding-checkpoint declaration ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_embedding_checkpoint " id:ident " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findEmbeddingCheckpointName env suffix.getString
  let newName := (← getCurrNamespace) ++ id.getId
  let some info := env.find? oldName | throwError "embedding-checkpoint declaration vanished"
  let value := mkConst oldName (info.levelParams.map Level.param)
  match info with
  | .defnInfo d =>
      liftCoreM <| addDecl <| .defnDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value := if id.getId == `embedding_stageRegionFamily ∨
            id.getId == `embedding_sourcePairAt then d.value else value
        hints := .abbrev
        safety := .safe
      }
  | .thmInfo d =>
      liftCoreM <| addDecl <| .thmDecl {
        name := newName
        levelParams := d.levelParams
        type := d.type
        value
      }
  | _ => throwError "unsupported embedding-checkpoint declaration kind for {oldName}"

expose_embedding_checkpoint embedding_stageParentCount_eq_regionalCount :=
  ".OmegaBound.ADVXXZGeneral.stageParentCount_eq_regionalCount"
expose_embedding_checkpoint embedding_joinedCoord :=
  ".OmegaBound.ADVXXZGeneral.joinedCoord"
expose_embedding_checkpoint embedding_regionalLegValue :=
  ".OmegaBound.ADVXXZGeneral.regionalLegValue"
expose_embedding_checkpoint embedding_packPhysicalWords :=
  ".OmegaBound.ADVXXZGeneral.packPhysicalWords"
expose_embedding_checkpoint embedding_packPhysicalWords_apply :=
  ".OmegaBound.ADVXXZGeneral.packPhysicalWords_apply"
expose_embedding_checkpoint embedding_stageRegionFamily :=
  ".OmegaBound.ADVXXZGeneral.stageRegionFamily"
expose_embedding_checkpoint embedding_sourcePairAt :=
  ".OmegaBound.ADVXXZGeneral.sourcePairAt"
expose_embedding_checkpoint embedding_sourceWordAt :=
  ".OmegaBound.ADVXXZGeneral.sourceWordAt"
expose_embedding_checkpoint embedding_sourceLabelAt :=
  ".OmegaBound.ADVXXZGeneral.sourceLabelAt"
expose_embedding_checkpoint embedding_source_properties :=
  ".OmegaBound.ADVXXZGeneral.source_properties"
expose_embedding_checkpoint embedding_incidence_coarse :=
  ".OmegaBound.ADVXXZGeneral.incidence_coarse"
expose_embedding_checkpoint embedding_incidence_compatible :=
  ".OmegaBound.ADVXXZGeneral.incidence_compatible"
expose_embedding_checkpoint embedding_compatible_iff_parent25 :=
  ".OmegaBound.ADVXXZGeneral.compatible_iff_parent25"
expose_embedding_checkpoint embedding_source_part_keep :=
  ".OmegaBound.ADVXXZGeneral.source_part_keep"
expose_embedding_checkpoint embedding_activeMap :=
  ".OmegaBound.ADVXXZGeneral.activeMap"
expose_embedding_checkpoint embedding_activeMap_injective :=
  ".OmegaBound.ADVXXZGeneral.activeMap_injective"
expose_embedding_checkpoint embedding_physicalLabel :=
  ".OmegaBound.ADVXXZGeneral.physicalLabel"
expose_embedding_checkpoint embedding_physical_labels_align :=
  ".OmegaBound.ADVXXZGeneral.physical_labels_align"
expose_embedding_checkpoint embedding_regionalInput_cw_ne :=
  ".OmegaBound.ADVXXZGeneral.regionalInput_cw_ne"
expose_embedding_checkpoint embedding_source_label_sum :=
  ".OmegaBound.ADVXXZGeneral.source_label_sum"

end
end OmegaBound.ADVXXZGeneral
end
