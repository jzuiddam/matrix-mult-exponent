import OmegaBound.ADVXXZGeneralAmend29CExact

set_option autoImplicit false

/-!
# Constituent regional copy bound, reserve and repair pool

The three definitions `RegionalCopyBound33`, `constituentRegionalReserve33` and
`constituentRepairPool33` used by the constituent-stage statements.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clause `P/constituent.tex:117-119,479`. -/
def RegionalCopyBound33 {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (delta : ℚ → ℝ)
    (ell : ℚ → ℕ → ℝ) (V : ℚ → ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    (∏ r : Fin 6,
      if (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0 then 1 else
        Nat.floor (Real.exp
          (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
            - delta ε * (cLength p b m : ℝ) - ell ε m))) ≤ V ε m

/-- Paper clause `H/hole.tex:121-125`. -/
def constituentRegionalReserve33 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) (r : Fin 6) : ℕ :=
  let pg := constituentGridParent27 d hd m h
  let dg := constituentGridSpec27 d hd m h
  let N := (stagePopulationAt q pg dg b m r).n
  if N = 0 then 1 else repairReserve N
    (fun W => (P.selected r).sup (fun j => (exactPartsAt q b m pg dg r j W).card))

-- A bound independent of the grid and its smallest nonzero probabilities.
/-- Paper clause `H/hole.tex:121-125`. -/
def constituentRepairPool33 (q : ℕ) {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b m : ℕ) : ℕ :=
  ∏ r : Fin 6,
    let N := (stagePopulationAt q p d b m r).n
    if N = 0 then 1 else repairReserve N (fun _ => 3^(w*N))

end
end OmegaBound.ADVXXZGeneral
end
