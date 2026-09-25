/-
Frozen statement: a copy of a statement frozen in the development repository.
id: T8_F.1
paper_clause: ADVXXZ 2024 numerical.tex:57-60; the strict bound over every field: omega is below 2371339/10^6.
sha256: 326ade3088dcc81fe000c559b6a1276e70865e5451bc8fd6b5ba8005ba033f40
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralEndpointDefs

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
def S_T8_F_1 : Prop :=
  ∀ (F : Type u) [Field F], omegaMM F < (2371339:ℝ)/10^6
end OmegaBound.ADVXXZGeneral
end
