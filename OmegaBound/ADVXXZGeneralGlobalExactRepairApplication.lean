import OmegaBound.ADVXXZGeneralGlobalExactRepairTransport
import OmegaBound.ADVXXZGeneralRepairFibresApplication
import OmegaBound.ADVXXZGeneralHRepair

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

/-- Every exact part over a target global label is inhabited. -/
theorem globalExactPart_nonempty27 {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target) (W : Side) :
    Nonempty (GlobalExactPart27 g n xi r j W) := by
  have hsum : ∀ (_t : PUnit) (u : Shape w),
      ∑ sigma, globalCounts27 g n xi r W PUnit.unit u sigma =
        Nat.card {i : Fin (globalPopulation g n xi r).n //
          globalColour27 g n xi r j PUnit.unit i = u} := by
    intro _t u
    simp only [globalCounts27]
    rw [xi.total W r u]
    rw [← globalTargetHistogram27 g xi r j hj u]
    simp only [globalColour27, histogram27,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hlevel : ∀ (_t : PUnit) (u : Shape w) (sigma : Chunk w),
      0 < globalCounts27 g n xi r W PUnit.unit u sigma →
        chunkLvl sigma = coord W u := by
    intro _t u sigma hpos
    by_contra hne
    have hz := xi.graded W r u sigma hne
    unfold globalCounts27 at hpos
    omega
  have hpart := partitionExact_nonempty27
    (globalColour27 g n xi r j) (fun _ u => u)
    (globalCounts27 g n xi r) W hsum hlevel
  exact ⟨(globalPartEquiv27 g n xi r j W).symm (Classical.choice hpart)⟩

/--
The literal application of finite hole repair to one target label of a compatible global grid.
All capacity and reserve hypotheses are stated on the actual exact-interface parts.
-/
theorem global_exact_repair_application {w n : ℕ} (q : ℕ) (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (hj : j ∈ (globalPopulation g n xi r).target)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (D : ℕ) (hD : 2 ≤ D)
    (holes : iota → (W : Side) → Finset (GlobalExactPart27 g n xi r j W))
    (hcapacity : ∀ i W,
      4*D*(holes i W).card ≤ Fintype.card (GlobalExactPart27 g n xi r j W))
    (I : Finset iota)
    (hI : 4^(Nat.log D (Fintype.card (GlobalExactPart27 g n xi r j .X)) +
      Nat.log D (Fintype.card (GlobalExactPart27 g n xi r j .Y)) +
      Nat.log D (Fintype.card (GlobalExactPart27 g n xi r j .Z)) + 1) ≤ I.card) :
    Restricts (globalExactTensorZ27 q g n xi r j)
      (famDS I (fun i => boxZO
        (globalExactPart27 q g n xi r j .X)
        (globalExactPart27 q g n xi r j .Y)
        (globalExactPart27 q g n xi r j .Z)
        (holes i .X)ᶜ (holes i .Y)ᶜ (holes i .Z)ᶜ
        (globalExactTensorZ27 q g n xi r j))) := by
  letI : Nonempty (GlobalExactPart27 g n xi r j .X) :=
    globalExactPart_nonempty27 q g xi r j hj .X
  letI : Nonempty (GlobalExactPart27 g n xi r j .Y) :=
    globalExactPart_nonempty27 q g xi r j hj .Y
  letI : Nonempty (GlobalExactPart27 g n xi r j .Z) :=
    globalExactPart_nonempty27 q g xi r j hj .Z
  exact fix_holes_general (globalExactTensorZ27 q g n xi r j)
    (globalExactPart27 q g n xi r j .X)
    (globalExactPart27 q g n xi r j .Y)
    (globalExactPart27 q g n xi r j .Z)
    (global_exact_interface_shuffles27 q g n xi r j) D hD
    (fun i => holes i .X) (fun i => holes i .Y) (fun i => holes i .Z)
    (fun i => hcapacity i .X) (fun i => hcapacity i .Y)
    (fun i => hcapacity i .Z) I hI

end
end OmegaBound.ADVXXZGeneral
end
