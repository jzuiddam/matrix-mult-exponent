import OmegaBound.ADVXXZGeneralAmend27CExact
import OmegaBound.ADVXXZGeneralAmend27CRepair
import OmegaBound.ADVXXZGeneralPopulationFiniteAPI

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clauses:
`P/constituent.tex:113–149` and `H/analysis_constituent.tex:117–125,306–325`. -/
def constituentGridInputDensity29 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (r : Fin 6)
    (J : AlphaLabel (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b m r) (W : Side) : ℝ :=
  InputDensity q (constituentGridParent27 d hd m h)
    (constituentGridSpec27 d hd m h) b ε m J W

/-- Paper clauses:
`P/constituent.tex:113–149`, `H/analysis_constituent.tex:117–125,306–325`, and
`H/hole.tex:121–125`. -/
structure ConstituentGridProduction29 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ) (m : ℕ)
    (h : ConstituentExactGrid27 d m) where
  modulus : Fin 6 → ℕ
  bucketSet : (r : Fin 6) → Finset (ZMod (modulus r))
  outcome : (r : Fin 6) → HashOutcome
    (stagePopulationAt q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b m r) (modulus r)
  selected : (r : Fin 6) → Finset
    (stagePopulationAt q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b m r).Label
  valid : ValidStageHashes (constituentGridParent27 d hd m h)
    (constituentGridSpec27 d hd m h) b m modulus bucketSet
  good : ∀ r j, j ∈ selected r →
    stageGood25 q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b ε m r
      (modulus r) (bucketSet r) (outcome r) j
  regionalCopies : Fin 6 → ℕ
  regionalCopies_eq : ∀ r,
    regionalCopies r =
      let P := stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r
      if P.n = 0 then 1 else
        (selected r).card / repairReserve P.n
          (fun W => (selected r).sup (fun j =>
            (exactPartsAt q b m (constituentGridParent27 d hd m h)
              (constituentGridSpec27 d hd m h) r j W).card))
  copies : ℕ
  copies_eq : copies = ∏ r : Fin 6, regionalCopies r
  source_to_broken : Restricts
    (goodBrokenFamilyZ25 q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b ε m modulus bucketSet outcome selected).tensor
    (constituentInputZ q (constituentGridParent27 d hd m h) (b*m) ε).tensor
  repair : Restricts (copiesZ copies (constituentGridTensorZ27 q d m h)).tensor
    (goodBrokenFamilyZ25 q (constituentGridParent27 d hd m h)
      (constituentGridSpec27 d hd m h) b ε m modulus bucketSet outcome selected).tensor
  degree : ℕ
  polynomial : PolyDegeneratesAt ℤ degree
    (constituentPlainInputZ q p (b*m) (3*ε)).tensor
    (copiesZ copies (constituentGridTensorZ27 q d m h)).tensor

/-- Paper clauses:
`P/constituent.tex:473–479`, `P/prelim.tex:284–289`, and `H/hole.tex:121–125`. -/
def ConstituentFiniteLoss29 {w s : ℕ} (p : ConstituentInput w s) (b : ℕ)
    (ell : ℚ → ℕ → ℝ) : Prop :=
  Loss (cLength p b) ell ∧
    ∀ ε : ℚ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      let L : ℝ := cLength p b m
      ell ε m ≤ C * (L / Real.log (L+2) + Real.sqrt (L+1) + Real.log (L+2) + 1)
end
end OmegaBound.ADVXXZGeneral
end
