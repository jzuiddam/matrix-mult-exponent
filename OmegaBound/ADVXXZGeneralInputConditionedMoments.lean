import OmegaBound.ADVXXZGeneralInputMarkov

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem inputConditioned_avg_equiv {A B : Type*}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- A statistic of one cell remains uniformly distributed after transporting an
arbitrary finite conditioning fibre to a nonempty nested dependent product.  Keeping
the fibre and the product abstract prevents downstream stage specializations from
normalizing the full `StageExactPart27` type in this declaration. -/
theorem avg_conditioned_pi_pi_apply
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (J : I → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (A : (i : I) → J i → Type*) [∀ i j, Fintype (A i j)]
    (hA : ∀ i j, Nonempty (A i j))
    (e : Ω ≃ ((i : I) → (j : J i) → A i j))
    (i : I) (j : J i) (f : A i j → ℝ) :
    avg (fun x : Ω => f (e x i j)) = avg f := by
  have hPi : ∀ i, Nonempty ((j : J i) → A i j) := fun i =>
    ⟨fun j => Classical.choice (hA i j)⟩
  calc
    avg (fun x : Ω => f (e x i j)) =
        avg (fun x : (i : I) → (j : J i) → A i j => f (x i j)) :=
      inputConditioned_avg_equiv e
        (fun x : (i : I) → (j : J i) → A i j => f (x i j))
    _ = avg (fun x : (j : J i) → A i j => f (x j)) :=
      avg_pi_apply (fun i => (j : J i) → A i j) hPi i (fun x => f (x j))
    _ = avg f := avg_pi_apply (A i) (hA i) j f

/-- Two different cells under the same outer block remain a uniform product after
transporting an arbitrary finite conditioning fibre to a nonempty nested dependent
product. -/
theorem avg_conditioned_pi_pi_apply₂
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (J : I → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (A : (i : I) → J i → Type*) [∀ i j, Fintype (A i j)]
    (hA : ∀ i j, Nonempty (A i j))
    (e : Ω ≃ ((i : I) → (j : J i) → A i j))
    (i : I) (j k : J i) (hjk : j ≠ k) (f : A i j → A i k → ℝ) :
    avg (fun x : Ω => f (e x i j) (e x i k)) =
      avg (fun z : A i j × A i k => f z.1 z.2) := by
  have hPi : ∀ i, Nonempty ((j : J i) → A i j) := fun i =>
    ⟨fun j => Classical.choice (hA i j)⟩
  calc
    avg (fun x : Ω => f (e x i j) (e x i k)) =
        avg (fun x : (i : I) → (j : J i) → A i j => f (x i j) (x i k)) :=
      inputConditioned_avg_equiv e
        (fun x : (i : I) → (j : J i) → A i j => f (x i j) (x i k))
    _ = avg (fun x : (j : J i) → A i j => f (x j) (x k)) :=
      avg_pi_apply (fun i => (j : J i) → A i j) hPi i
        (fun x => f (x j) (x k))
    _ = avg (fun z : A i j × A i k => f z.1 z.2) :=
      avg_pi_apply₂ (A i) (hA i) j k hjk f

end OmegaBound.ADVXXZGeneral
end
