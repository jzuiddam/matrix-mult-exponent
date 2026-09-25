import OmegaBound.ADVXXZGeneralIterateInfraPolySum
import OmegaBound.ADVXXZGeneralIterateInfraPolyTrans

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- Apply one polynomial degeneration independently in each of `Q` labelled copies. -/
theorem polyDegeneratesAt_copies (Q : ℕ) {T U : ITensor} {N : ℕ}
    (h : PolyDegeneratesAt ℤ N T.tensor U.tensor) :
    PolyDegeneratesAt ℤ N (copiesZ Q T).tensor (copiesZ Q U).tensor := by
  classical
  simpa only [copiesZ] using
    (polyDegeneratesAt_famDS_common (R := ℤ) N (J := Fin Q)
      (fun _ => T.tensor) (fun _ => U.tensor) (fun _ => h))

private noncomputable def copiesMulEquiv (Q V : ℕ) : Fin (Q * V) ≃ Fin Q × Fin V :=
  Fintype.equivOfCardEq (by simp)

/-- Flattening nested labelled copies is a restriction (indeed, a reindexing). -/
theorem copiesZ_mul_restricts_nested (Q V : ℕ) (T : ITensor) :
    Restricts (copiesZ (Q * V) T).tensor (copiesZ Q (copiesZ V T)).tensor := by
  classical
  let e := copiesMulEquiv Q V
  refine ADVXXZ.restricts_of_sub
    (fun p => ((e p.1).1, ((e p.1).2, p.2)))
    (fun p => ((e p.1).1, ((e p.1).2, p.2)))
    (fun p => ((e p.1).1, ((e p.1).2, p.2))) ?_
  rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  simp only [copiesZ, famDS, Finset.mem_univ, and_true]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp
    · by_cases h₁ : (e i).1 = (e k).1
      · have h₂ : ¬ (e i).2 = (e k).2 := by
          intro h₂
          exact hik (e.injective (Prod.ext h₁ h₂))
        simp [hik, h₁, h₂]
      · simp [hik, h₁]
  · by_cases h₁ : (e i).1 = (e j).1
    · have h₂ : ¬ (e i).2 = (e j).2 := by
        intro h₂
        exact hij (e.injective (Prod.ext h₁ h₂))
      simp [hij, h₁, h₂]
    · simp [hij, h₁]

/-- The inverse flattening reindexing. -/
theorem copiesZ_nested_restricts_mul (Q V : ℕ) (T : ITensor) :
    Restricts (copiesZ Q (copiesZ V T)).tensor (copiesZ (Q * V) T).tensor := by
  classical
  let e := copiesMulEquiv Q V
  refine ADVXXZ.restricts_of_sub
    (fun p => (e.symm (p.1, p.2.1), p.2.2))
    (fun p => (e.symm (p.1, p.2.1), p.2.2))
    (fun p => (e.symm (p.1, p.2.1), p.2.2)) ?_
  rintro ⟨i, ⟨a, x⟩⟩ ⟨j, ⟨b, y⟩⟩ ⟨k, ⟨c, z⟩⟩
  simp only [copiesZ, famDS, Finset.mem_univ, and_true]
  have hpair₁ : e.symm (i, a) = e.symm (j, b) ↔ i = j ∧ a = b := by
    constructor
    · intro h
      have h' := e.symm.injective h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hpair₂ : e.symm (j, b) = e.symm (k, c) ↔ j = k ∧ b = c := by
    constructor
    · intro h
      have h' := e.symm.injective h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [hpair₁, hpair₂]
  rw [← ite_and]
  congr 1
  apply propext
  aesop

/-- Arbitrary-copy lifting: `Q` independent uses of a witness producing `V` copies produce
`Q*V` copies, with both nested copy indices flattened. -/
theorem polyDegeneratesAt_arbitraryCopies (Q V : ℕ) {T S : ITensor} {N : ℕ}
    (h : PolyDegeneratesAt ℤ N T.tensor (copiesZ V S).tensor) :
    ∃ M, PolyDegeneratesAt ℤ M (copiesZ Q T).tensor (copiesZ (Q * V) S).tensor := by
  classical
  have hcopies := polyDegeneratesAt_copies Q h
  have hflat := polyDegeneratesAt_of_restricts (copiesZ_mul_restricts_nested Q V S)
  exact integral_polyDegeneratesAt_trans hcopies hflat

end OmegaBound.ADVXXZGeneral
end
