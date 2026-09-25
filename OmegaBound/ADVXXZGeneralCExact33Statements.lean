import OmegaBound.ADVXXZGeneralCExact33Defs

set_option autoImplicit false

/-!
# Constituent-stage statements

Five constituent-stage theorem statements as `Prop`-valued definitions.

* `S_constituent_grid_broken_supply33`: proved as `constituent_grid_broken_supply41`
  (`ADVXXZGeneralCExact41BrokenSupply`);
* `S_constituent_repair_pool_sublinear33`: proved as `S_constituent_repair_pool_sublinear33_holds`
  (`ADVXXZGeneralCExact33Supply`);
* `S_constituent_positive_exact_regional33`, `S_constituent_positive_positive_regional33`: the
  same statements as `S_V17_C_Exact_3` and `S_V17_C_Exact_4` of `PLATFORM/Statements`, which
  `ADVXXZGeneralCExact42RegionalExact` and `ADVXXZGeneralCExact42PositiveRegional` prove; these two
  definitions are not used elsewhere;
* `S_constituent_pooled_positive33`: proved as `constituent_pooled_positive33`
  (`ADVXXZGeneralCExact42Pooled`).
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

-- A real quotient before natural division, for broken-copy supply.
def S_constituent_grid_broken_supply33 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ ConstituentFiniteLoss29 p b ell ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ h : ConstituentFullGrid27 d m ε,
        (∀ x y z, (constituentGridTensorZ27 q d m h.val).tensor x y z = 0) ∨
        ∃ P : ConstituentGridProduction29 q d hd ε m h.val, ∀ r : Fin 6,
          Real.exp (Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
            - delta ε * (cLength p b m : ℝ) - ell ε m) ≤
          if (stagePopulationAt q (constituentGridParent27 d hd m h.val)
                (constituentGridSpec27 d hd m h.val) b m r).n = 0 then 1 else
            ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)

def S_constituent_repair_pool_sublinear33 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  Sublinear (cLength p b)
    (fun m => Real.log (constituentRepairPool33 q p d b m : ℝ))

def S_constituent_positive_exact_regional33 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧
    Loss (fun m => constituentBaseTotal p * (b*m)) ell ∧
    RegionalCopyBound33 p d b delta ell V ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ (F : Type u) [Field F],
        Degenerates F ((constituentInputZ q p (b*m) ε).over F)
          ((copiesZ (V ε m) (constituentOutputZ q d m 0)).over F)

def S_constituent_positive_positive_regional33 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (Q V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ Loss (cLength p b) ell ∧
    RegionalCopyBound33 p d b delta ell V ∧
    (∀ ε, 0 < ε → Sublinear (cLength p b) (fun m => Real.log (Q ε m:ℝ))) ∧
    ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
      1 ≤ Q ε m ∧ Q ε m ≤ (cLength p b m+1)^ConstituentGridDimension p d ∧
      ∀ (F : Type u) [Field F],
        Degenerates F ((copiesZ (Q ε m) (constituentPlainInputZ q p (b*m) (3*ε))).over F)
          ((copiesZ (V ε m) (constituentOutputZ q d m ε)).over F)

-- Used by the recursion: repair on extra input copies, before recursion.
def S_constituent_pooled_positive33 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (Q V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ Loss (cLength p b) ell ∧
    CopyBound (cLength p b) (cRate d) delta ell V ∧
    (∀ ε, 0 < ε → Sublinear (cLength p b) (fun m => Real.log (Q ε m : ℝ))) ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      1 ≤ Q ε m ∧
      Q ε m ≤ constituentRepairPool33 q p d b m *
        (cLength p b m+1)^ConstituentGridDimension p d ∧
      ∃ degree : ℕ, PolyDegeneratesAt ℤ degree
        (copiesZ (Q ε m) (constituentPlainInputZ q p (b*m) (3*ε))).tensor
        (copiesZ (V ε m) (constituentOutputZ q d m ε)).tensor

end OmegaBound.ADVXXZGeneral
end
