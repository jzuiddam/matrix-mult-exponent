import OmegaBound.ADVXXZT6Round130fEvaluator

/-!
# Release compaction: generic soundness shared by the compact row cohorts

Emitted by `release/emitters/emit_compact_rows.py`.  One kernel theorem, independent of every
released row: a `LinearQ130f` row's real value depends only on its constant and on the total
coefficient of each formal atom.  Cohort checks certify `SameCoefs130f` natively and obtain the
real-valued equality between a literal row and its compact (merged, zero-free) form from here.
-/

namespace OmegaBound.ReleaseCompactRows

open OmegaBound.ADVXXZT6Round130f

/-- Total coefficient of the formal atom `a` in a term list. -/
def coefSum130f : List (AtomQ130f × ℚ) → AtomQ130f → ℚ
  | [], _ => 0
  | x :: xs, a => (if x.1 = a then x.2 else 0) + coefSum130f xs a

/-- Equal constants and equal coefficient totals at every atom occurring in either row. -/
def SameCoefs130f (e f : LinearQ130f) : Prop :=
  e.constant = f.constant ∧
    ∀ x ∈ e.terms ++ f.terms, coefSum130f e.terms x.1 = coefSum130f f.terms x.1

instance (e f : LinearQ130f) : Decidable (SameCoefs130f e f) := by
  unfold SameCoefs130f
  infer_instance

theorem termsValue130f_eq_sum (xs : List (AtomQ130f × ℚ)) (S : Finset AtomQ130f)
    (hS : ∀ x ∈ xs, x.1 ∈ S) :
    termsValue130f xs = ∑ a ∈ S, (coefSum130f xs a : ℝ) * a.value := by
  induction xs with
  | nil => simp [termsValue130f, coefSum130f]
  | cons x xs ih =>
    have hx : x.1 ∈ S := hS x (by simp)
    have hrest := ih (fun y hy => hS y (by simp [hy]))
    have hcons : termsValue130f (x :: xs) = (x.2 : ℝ) * x.1.value + termsValue130f xs := by
      simp [termsValue130f]
    rw [hcons, hrest]
    simp only [coefSum130f, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem x.1 hx]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]

theorem value_eq_of_sameCoefs130f (e f : LinearQ130f) (h : SameCoefs130f e f) :
    e.value = f.value := by
  classical
  obtain ⟨hc, hall⟩ := h
  let S : Finset AtomQ130f := ((e.terms ++ f.terms).map Prod.fst).toFinset
  have hS : ∀ x ∈ e.terms ++ f.terms, x.1 ∈ S := fun x hx =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  unfold LinearQ130f.value
  rw [hc, termsValue130f_eq_sum e.terms S (fun x hx => hS x (List.mem_append_left _ hx)),
    termsValue130f_eq_sum f.terms S (fun x hx => hS x (List.mem_append_right _ hx))]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
  rw [hall x hx]

end OmegaBound.ReleaseCompactRows
