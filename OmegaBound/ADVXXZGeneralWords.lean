import OmegaBound.ADVXXZGeneralPopulationConstructorsV22

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
def typeCnt {α : Type*} [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) : ℕ :=
  (Finset.univ.filter (fun i => x i = a)).card

abbrev Words {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (k : α → ℕ) :=
  {x : Fin n → α // ∀ a, typeCnt x a = k a}

abbrev PairWords {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (n : ℕ) (k : α → ℕ) (l : β → ℕ) := Words n k × Words n l

def pairCount {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} {k : α → ℕ} {l : β → ℕ} (e : Equiv.Perm (Fin n)) (a : α) (b : β)
    (z : PairWords n k l) : ℕ :=
  (Finset.univ.filter (fun i => z.1.val i = a ∧ z.2.val (e i) = b)).card

noncomputable def avg {D : Type*} [Fintype D] (f : D → ℝ) : ℝ :=
  (∑ z, f z) / (Fintype.card D : ℝ)
end OmegaBound.ADVXXZGeneral
end
