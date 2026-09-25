import OmegaBound.ADVXXZGeneralGlobalExactGridReindex
import OmegaBound.ADVXXZGeneralGlobalExactCopiesBound
import OmegaBound.ADVXXZGeneralGlobalExactExponentIdentities

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral.GlobalExactEnvelope37
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def globalExactRegion_direct37 : Prop :=
  ∀ {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (j : (globalPopulation g n xi r).Label),
  Restricts (copiesZ 1 (globalExactITensor27 q g xi r j)).tensor
    (topZ q w (globalPopulation g n xi r).n).tensor

def globalSelectedRegion_restrict_top37 : Prop :=
  ∀ {w b M : ℕ} [NeZero M]
    (q m : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (hb : GlobalIntegral g b) (xi : ExactGrid g (b*m))
    (hxi : GridBoundaryCompatible xi) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b*m) xi r) M)
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hgrade : (globalPopulation g (b*m) xi r).grade < M)
    (hAP : HashAPFree B),
  Restricts (globalSelectedRegionFamily27 q g xi r B omega).tensor
    (topZ q w (globalPopulation g (b*m) xi r).n).tensor

def globalRegionCopies_fallback37 : Prop :=
  ∀ {w b M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (hb : GlobalIntegral g b) (floor m : ℕ) (hm : 0 < m)
    (xi : ExactGrid g (b*m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hgrade : (globalPopulation g (b*m) xi r).grade < M)
    (hAP : HashAPFree B) (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (j0 : GlobalTargetLabel27 g xi r) (b0 : GlobalBucketLabel27 B)
    (hn : (globalPopulation g (b*m) xi r).n ≠ 0),
  ∃ V : ℕ, 0 < V ∧
    (11 / 40 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
      Fintype.card (GlobalBucketLabel27 B) /
      ((M : ℝ)^2 * (repairReserve (2 * (globalPopulation g (b*m) xi r).n)
        (fun W => Fintype.card (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ))
      ≤ (V : ℝ) ∧
    Restricts (copiesZ V (globalExactITensor27 q g xi r j0.val)).tensor
      (topZ q w (globalPopulation g (b*m) xi r).n).tensor

def globalRepairBudget_uniform37 : Prop :=
  ∀ {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hw : 0 < w) (hb : GlobalIntegral g b),
  ∃ ell : ℕ → ℝ, (∀ m, 0 ≤ ell m) ∧ Sublinear (fun m => b*m) ell ∧
    ∃ L : ℕ, ∀ m, L ≤ m → 0 < m → ∀ xi : ExactGrid g (b*m),
      GridBoundaryCompatible xi →
      ∃ (k : Fin 6 → ℕ) (B : (r : Fin 6) → Finset (ZMod (2*k r+1))),
        ValidGlobalHashes g (b*m) xi (fun r => 2*k r+1) B ∧
        (∀ r, 2 * globalDemand g b 0 m xi r ≤ 2*k r+1) ∧
        (∀ r, (B r).Nonempty) ∧
        ∀ r, (globalPopulation g (b*m) xi r).n ≠ 0 →
          ∀ j0 : GlobalTargetLabel27 g xi r,
          Real.exp (((globalPopulation g (b*m) xi r).n : ℝ) * Real.log 2 *
            globalRegionRate (globalExactGridData27 g xi) r - ell m) ≤
          (11 / 40 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
            Fintype.card (GlobalBucketLabel27 (B r)) /
            (((2*k r+1 : ℕ) : ℝ)^2 *
              (repairReserve (2 * (globalPopulation g (b*m) xi r).n)
                (fun W => Fintype.card
                  (GlobalExactPart27 g (b*m) xi r j0.val W)) : ℝ))

def globalRegionalTop_exactGrid37 : Prop :=
  ∀ {w b : ℕ} (q m : ℕ)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b)
    (xi : ExactGrid g (b*m))
    (j : (r : Fin 6) → GlobalTargetLabel27 g xi r) (V : Fin 6 → ℕ)
    (hregion : ∀ r,
      Restricts (copiesZ (V r) (globalExactITensor27 q g xi r (j r).val)).tensor
        (topZ q w (globalPopulation g (b*m) xi r).n).tensor),
  PolyDegeneratesAt ℤ 0 (topZ q w (b*m)).tensor
    (copiesZ (∏ r, V r) (exactGridTensor q g (b*m) xi)).tensor

end
end OmegaBound.ADVXXZGeneral.GlobalExactEnvelope37
end
