import OmegaBound.ADVXXZT2Paired
import OmegaBound.ADVXXZT6Selection
import OmegaBound.ADVXXZT6Round19PaperContract

/-!
# The released strictly-positive parent input

The positive-coordinate hypothesis used by the constituent stage is not obtained by retaining
all 270 global terms: 144 of those terms are boundary leaves.  The paper instead indexes the
constituent input by the non-corner parent terms.  This file makes that choice literally, using
the released list of all 126 general parents and their transported complete-split laws.

SOURCE: `global.tex:79-93,123-125` (global output parameter list and inherited constraints).
SOURCE: `constituent.tex:7-11,113-118` (non-corner input terms and positive tolerance).
-/

set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT9R16PositiveParents

open ADVXXZPaper

/-- The three released coordinates, in the paper's `X,Y,Z` order.

SOURCE: `global.tex:83-92`; `constituent.tex:7-11`.
-/
def releasedParentCoord (W : Side) (t : Fin 126) : Nat :=
  match W with
  | .X => (ADVXXZT2.parShapeOf t.1).1
  | .Y => (ADVXXZT2.parShapeOf t.1).2.1
  | .Z => (ADVXXZT2.parShapeOf t.1).2.2

/-- The transported complete-split law on a released parent's physical side.

SOURCE: `global.tex:89-92`; `constituent.tex:9-11`.
-/
def releasedParentBeta (W : Side) (t : Fin 126) : ADVXXZ.SplitDist 4 :=
  match W with
  | .X => ADVXXZT2.parBeta t.1 0
  | .Y => ADVXXZT2.parBeta t.1 1
  | .Z => ADVXXZT2.parBeta t.1 2

/-- One finite certificate for all arithmetic fields required by `ConstituentInput`.

The strict inequalities are exactly the reason for selecting `genList` rather than the 144
boundary leaves.

SOURCE: `constituent.tex:7-11,113-117`.
-/
def ReleasedParentArithmetic : Prop :=
  (forall t : Fin 126, 0 < ADVXXZT6Selection.parentMass t) /\
  (forall t : Fin 126, 0 < releasedParentCoord .X t /\
    0 < releasedParentCoord .Y t /\ 0 < releasedParentCoord .Z t) /\
  (forall t : Fin 126,
    releasedParentCoord .X t + releasedParentCoord .Y t + releasedParentCoord .Z t = 8)

instance : Decidable ReleasedParentArithmetic := by
  unfold ReleasedParentArithmetic releasedParentCoord ADVXXZT6Selection.parentMass
  infer_instance

set_option maxHeartbeats 3000000 in
-- Native finite verification of the released 126-parent census.
/-- The released census verifies all 126 parents in one native finite check.

SOURCE: `constituent.tex:7-11,113-117`.
-/
theorem releasedParentArithmetic : ReleasedParentArithmetic := by
  native_decide

/-- The released parent complete-split law has the level support required by the paper input.

SOURCE: `global.tex:89-92`; `constituent.tex:9-11`.
-/
theorem releasedParentBeta_supported (W : Side) (t : Fin 126) (sigma : ADVXXZ.Chunk 4) :
    (releasedParentBeta W t).probR sigma ≠ 0 ->
      ADVXXZ.chunkLvl sigma = releasedParentCoord W t := by
  intro h
  have hn : (releasedParentBeta W t).num sigma ≠ 0 := by
    intro hz
    apply h
    simp [ADVXXZ.RatDist.probR, hz]
  cases W with
  | X =>
      rw [ADVXXZT2.chunkLvl_split]
      simpa [releasedParentBeta, releasedParentCoord, ADVXXZT2.legs] using
        (ADVXXZT2.parBeta_support t.1 (0 : Fin 3) sigma hn)
  | Y =>
      rw [ADVXXZT2.chunkLvl_split]
      simpa [releasedParentBeta, releasedParentCoord, ADVXXZT2.legs] using
        (ADVXXZT2.parBeta_support t.1 (1 : Fin 3) sigma hn)
  | Z =>
      rw [ADVXXZT2.chunkLvl_split]
      simpa [releasedParentBeta, releasedParentCoord, ADVXXZT2.legs] using
        (ADVXXZT2.parBeta_support t.1 (2 : Fin 3) sigma hn)

/-- The concrete paper input indexed by every released non-corner parent.

SOURCE: `global.tex:79-93,123-125`; `constituent.tex:7-11,113-117`.
-/
noncomputable def releasedPositiveInput : ConstituentInput 2 126 where
  terms_nonempty := by decide
  baseN := ADVXXZT6Selection.parentMass
  baseN_pos := releasedParentArithmetic.1
  i := releasedParentCoord .X
  j := releasedParentCoord .Y
  k := releasedParentCoord .Z
  i_pos := fun t => (releasedParentArithmetic.2.1 t).1
  j_pos := fun t => (releasedParentArithmetic.2.1 t).2.1
  k_pos := fun t => (releasedParentArithmetic.2.1 t).2.2
  shape_sum := by
    intro t
    simpa using releasedParentArithmetic.2.2 t
  beta := releasedParentBeta
  beta_supported := releasedParentBeta_supported

/-- For the released parent list, the entire input-hypothesis record is equivalent to the
paper's outer `epsilon > 0` quantifier.

SOURCE: `global.tex:116-125`; `constituent.tex:113-118`.
-/
theorem releasedPositiveInput_hypotheses_iff (epsilon : Rat) :
    ADVXXZT6Round19.InputHypotheses epsilon releasedPositiveInput <-> 0 < epsilon := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun t =>
      ⟨releasedPositiveInput.i_pos t, releasedPositiveInput.j_pos t,
        releasedPositiveInput.k_pos t⟩⟩

end OmegaBound.ADVXXZT9R16PositiveParents
