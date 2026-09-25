import OmegaBound.ADVXXZGeneralAmend25Rates
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def GridBoundaryCompatible {w n : ℕ} {g : GlobalSpec w} (ξ : ExactGrid g n) : Prop :=
  ∀ r u (Z X Y : Side), X ≠ Y → X ≠ Z → Y ≠ Z → coord Z u = 0 →
    ∀ σ, ξ.count X r u σ = ξ.count Y r u (reflect σ)

end OmegaBound.ADVXXZGeneral
namespace OmegaBound.ADVXXZGeneral.GlobalBridge25
noncomputable section

def side {w : ℕ} (g : GlobalSpec w) (r : Fin 6) (W : Fin 2) : Side :=
  g.perm r (if W = 0 then .Y else .Z)

def boundary {w : ℕ} (g : GlobalSpec w) (r : Fin 6) (W : Fin 2) (u : Shape w) : Prop :=
  if W = 0 then coord (g.perm r .Z) u = 0
  else coord (g.perm r .X) u = 0 ∨ coord (g.perm r .Y) u = 0

abbrev Cell (w : ℕ) := Shape w ⊕ Fin (2*w+1)

def key {w : ℕ} (g : GlobalSpec w) (r : Fin 6) (W : Fin 2) (u : Shape w) : Cell w := by
  classical
  exact if boundary g r W u then .inl u else .inr (Parent25.coordFin (side g r W) u)

def histogram {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n)
    (r : Fin 6) (W : Fin 2) (c : Cell w) (σ : Chunk w) : ℕ := by
  classical
  exact ∑ u : Shape w, if key g r W u = c then ξ.count (side g r W) r u σ else 0

def pExponent {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n)
    (r : Fin 6) (W : Fin 2) (β : GlobalRepresentedLaw g n ξ r W) : ℝ :=
  let N := (globalPopulation g n ξ r).n
  (N : ℝ) * (entropyNats (fun σ => (β.val σ : ℝ) / N) -
    entropyNats (fun k => (projectedCount Parent25.grade β.val k : ℝ) / N))

def qExponent {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n)
    (r : Fin 6) (W : Fin 2) : ℝ :=
  ∑ c : Cell w, let N := ∑ σ, histogram g n ξ r W c σ
    (N : ℝ) * entropyNats (fun σ => (histogram g n ξ r W c σ : ℝ) / N)

def FiniteBounds : Prop :=
  ∀ {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n),
    GridBoundaryCompatible ξ → ∀ r W (β : GlobalRepresentedLaw g n ξ r W),
    let P := globalPopulation g n ξ r
    let A := (P.target.card : ℝ)
    let C := (Fintype.card (GlobalLawSample g n ξ r W) : ℝ)
    let poly := ((P.n : ℝ) + 1) ^ Fintype.card (Chunk w)
    let coarsePoly := ((P.n : ℝ) + 1) ^ Fintype.card (Fin (2*w+1))
    0 < globalJointP g n ξ r W β ∧
    C * globalJointP g n ξ r W β =
      ∑ j : {j // j ∈ P.target}, (Nat.card {a : P.Part (side g r W) //
        globalCoarseContains g n ξ r (side g r W) j.val a ∧
        globalEmpiricalLaw g n ξ r (side g r W) a = β.val} : ℝ) ∧
    C * globalJointQ g n ξ r W β =
      ∑ j : {j // j ∈ P.target}, (Nat.card {a : P.Part (side g r W) //
        globalCoarseContains g n ξ r (side g r W) j.val a ∧
        globalEmpiricalLaw g n ξ r (side g r W) a = β.val ∧
        globalCompatible g n ξ r W j.val a} : ℝ) ∧
    A * Real.exp (pExponent g n ξ r W β) / poly ≤ C * globalJointP g n ξ r W β ∧
    C * globalJointP g n ξ r W β ≤ A * Real.exp (pExponent g n ξ r W β) * coarsePoly ∧
    C * globalJointQ g n ξ r W β ≤ A * Real.exp (qExponent g n ξ r W)

end
end OmegaBound.ADVXXZGeneral.GlobalBridge25

