import OmegaBound.ADVXXZGeneralGlobalExactEnvelope37

set_option autoImplicit false

open OmegaBound Tensor3 OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The unrestricted regional top contains any one exact regional copy. -/
theorem globalExactRegion_direct37 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (j : (globalPopulation g n xi r).Label) :
    Restricts (copiesZ 1 (globalExactITensor27 q g xi r j)).tensor
      (topZ q w (globalPopulation g n xi r).n).tensor := by
  apply ADVXXZ.restricts_of_sub (fun x => x.2.val) (fun y => y.2.val)
    (fun z => z.2.val)
  intro x y z
  have hxy : x.1 = y.1 := Subsingleton.elim _ _
  have hxz : x.1 = z.1 := Subsingleton.elim _ _
  have hyz : y.1 = z.1 := Subsingleton.elim _ _
  simp only [copiesZ, famDS, Finset.mem_univ, hxy, hxz, hyz, and_self, ↓reduceIte,
    globalExactITensor27, globalExactTensorZ27, topZ, tensorPower]
  apply Finset.prod_congr rfl
  intro i _
  unfold conZ
  rw [ADVXXZ.zoP_apply, if_pos]
  · rfl
  · exact ⟨by simpa only [levOf, globalPhysicalPart] using x.2.property.1 i,
      by simpa only [levOf, globalPhysicalPart] using y.2.property.1 i,
      by simpa only [levOf, globalPhysicalPart] using z.2.property.1 i⟩

theorem globalExactRegion_direct37_matches_display :
    GlobalExactEnvelope37.globalExactRegion_direct37 :=
  @globalExactRegion_direct37

end
end OmegaBound.ADVXXZGeneral
