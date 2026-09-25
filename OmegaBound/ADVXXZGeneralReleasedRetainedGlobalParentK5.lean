import OmegaBound.ADVXXZG1Parent

namespace OmegaBound.ADVXXZGeneral

set_option maxHeartbeats 4000000 in
theorem released_parentY_k_r5 : ∀ (l : Fin (2 * 4 + 1))
    (c : OmegaBound.ADVXXZ.Chunk 4),
    OmegaBound.ADVXXZG1.ParentOK
      OmegaBound.ADVXXZCertRegionalSemantic.avgY .Y 5 l c := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem released_parentZ_k_r5 : ∀ (l : Fin (2 * 4 + 1))
    (c : OmegaBound.ADVXXZ.Chunk 4),
    OmegaBound.ADVXXZG1.ParentOK
      OmegaBound.ADVXXZCertRegionalSemantic.avgZ .Z 5 l c := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem released_AtotY_pos_k_r5 : ∀ (l : Fin (2 * 4 + 1)),
    0 < OmegaBound.ADVXXZG1.Atot 5 .Y l := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem released_AtotZ_pos_k_r5 : ∀ (l : Fin (2 * 4 + 1)),
    0 < OmegaBound.ADVXXZG1.Atot 5 .Z l := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem released_betaY_support_k_r5 : ∀ (n : Fin 45)
    (c : OmegaBound.ADVXXZ.Chunk 4),
    (OmegaBound.ADVXXZG1.betaIdx 5 .Y n).num c ≠ 0 ↔
      OmegaBound.ADVXXZ.chunkLvl c = OmegaBound.ADVXXZG1.rowLvl .Y n := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem released_betaZ_support_k_r5 : ∀ (n : Fin 45)
    (c : OmegaBound.ADVXXZ.Chunk 4),
    (OmegaBound.ADVXXZG1.betaIdx 5 .Z n).num c ≠ 0 ↔
      OmegaBound.ADVXXZ.chunkLvl c = OmegaBound.ADVXXZG1.rowLvl .Z n := by
  decide +kernel

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_parentY_k_r5
#print axioms OmegaBound.ADVXXZGeneral.released_parentZ_k_r5
#print axioms OmegaBound.ADVXXZGeneral.released_AtotY_pos_k_r5
#print axioms OmegaBound.ADVXXZGeneral.released_AtotZ_pos_k_r5
#print axioms OmegaBound.ADVXXZGeneral.released_betaY_support_k_r5
#print axioms OmegaBound.ADVXXZGeneral.released_betaZ_support_k_r5
