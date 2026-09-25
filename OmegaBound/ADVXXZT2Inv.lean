import OmegaBound.ADVXXZT1IncRange
import OmegaBound.ADVXXZT2Mult

/-!
# The typed inventory equality

This module turns the addressing law of `ADVXXZT1Inc`/`ADVXXZT1IncRange` into a typed
`Function.Bijective` object, with no new decision procedure.  `ADVXXZT1.inc_left_ranges` says
each released `(parent, region)` block's left ids, insertion-sorted, are exactly that block's
own contiguous range and that the running offset ends at `5508`.  Sorting is a permutation
(`isort_perm`), the block ranges concatenate (`List.range'_append`), and the blocks reassemble
the released list (`ADVXXZT1.inc_blocks_flatten`), so

```text
level3Incidence.map (·.left.val)  ~  List.range 5508,
```

hence `Nodup`, hence `leftOcc : Fin 5508 → Level2TermId` is injective, hence bijective on equal
finite cardinalities, which is `leftOcc_bijective`; `ADVXXZT2.leftEquiv : Fin 5508 ≃ Level2TermId`
is the resulting equivalence.
-/

set_option maxRecDepth 4000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT2

open ADVXXZCertSemantic (Level3Incidence level3Incidence Level2TermId)
open ADVXXZT1 (blocks ins isort inc_length inc_blocks_flatten inc_left_ranges)

/-! ## §1  Insertion sort is a permutation -/

theorem ins_perm (a : ℕ) : ∀ l : List ℕ, List.Perm (ins a l) (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      show List.Perm (if a ≤ b then a :: b :: l else b :: ins a l) (a :: b :: l)
      split
      · exact List.Perm.refl _
      · exact ((ins_perm a l).cons b).trans (List.Perm.swap a b l)

theorem isort_perm : ∀ l : List ℕ, List.Perm (isort l) l
  | [] => List.Perm.refl _
  | a :: l => (ins_perm a (isort l)).trans ((isort_perm l).cons a)

/-! ## §2  The range walk forces a permutation of the whole id range -/

/-- The step of `ADVXXZT1.rangeWalk`, named so that the fold can be inducted on. -/
def stepL (f : Level3Incidence → ℕ) (st : ℕ × Bool) (B : List Level3Incidence) : ℕ × Bool :=
  (st.1 + B.length, st.2 && (isort (B.map f) == List.range' st.1 B.length))


/-- Once the accumulator is `false` it stays `false`. -/
theorem foldl_false (f : Level3Incidence → ℕ) :
    ∀ (BL : List (List Level3Incidence)) (o : ℕ), (BL.foldl (stepL f) (o, false)).2 = false
  | [], _ => rfl
  | B :: BL, o => by
      have h : stepL f (o, false) B = (o + B.length, false) := by
        simp only [stepL, Bool.false_and]
      show (BL.foldl (stepL f) (stepL f (o, false) B)).2 = false
      rw [h]
      exact foldl_false f BL (o + B.length)

/-- **THE WALK IS A PERMUTATION STATEMENT.**  If the running offset survives with verdict `true`,
the concatenated ids are a permutation of the contiguous range starting at the initial offset. -/
theorem foldl_perm (f : Level3Incidence → ℕ) :
    ∀ (BL : List (List Level3Incidence)) (o : ℕ), (BL.foldl (stepL f) (o, true)).2 = true →
      List.Perm (BL.flatten.map f) (List.range' o BL.flatten.length)
  | [], o, _ => by simp
  | B :: BL, o, h => by
      have hstep : stepL f (o, true) B
          = (o + B.length, isort (B.map f) == List.range' o B.length) := by
        simp only [stepL, Bool.true_and]
      rw [List.foldl_cons, hstep] at h
      have hb : (isort (B.map f) == List.range' o B.length) = true := by
        by_contra hne
        have hf : (isort (B.map f) == List.range' o B.length) = false := by
          simpa using hne
        rw [hf, foldl_false f BL (o + B.length)] at h
        exact absurd h (by simp)
      have hsorted : isort (B.map f) = List.range' o B.length := by simpa using hb
      rw [hb] at h
      have hIH := foldl_perm f BL (o + B.length) h
      have hB : List.Perm (B.map f) (List.range' o B.length) := by
        rw [← hsorted]; exact (isort_perm _).symm
      have e1 : (B :: BL).flatten.map f = B.map f ++ BL.flatten.map f := by
        rw [List.flatten_cons, List.map_append]
      have e4 : (B :: BL).flatten.length = B.length + BL.flatten.length := by
        rw [List.flatten_cons, List.length_append]
      have e3 : List.range' o B.length ++ List.range' (o + B.length) BL.flatten.length
          = List.range' o (B.length + BL.flatten.length) := by
        have := @List.range'_append o B.length BL.flatten.length 1
        simpa using this
      rw [e1, e4, ← e3]
      exact hB.append hIH

/-! ## §3  The two released id maps are permutations of the level-2 inventory -/

/-- The blocks carry the same numeric field as the released list. -/
theorem flatten_map_eq (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ) :
    (blocks level3Incidence).flatten.map (fun e => g (ADVXXZG2.l3sig e))
      = level3Incidence.map (fun e => g (ADVXXZG2.l3sig e)) := by
  have h := inc_blocks_flatten
  have h1 : (blocks level3Incidence).flatten.map (fun e => g (ADVXXZG2.l3sig e))
      = ((blocks level3Incidence).flatten.map ADVXXZG2.l3sig).map g := by
    rw [List.map_map]; rfl
  have h2 : level3Incidence.map (fun e => g (ADVXXZG2.l3sig e))
      = (level3Incidence.map ADVXXZG2.l3sig).map g := by
    rw [List.map_map]; rfl
  rw [h1, h2, h]

theorem blocks_flatten_length : (blocks level3Incidence).flatten.length = 5508 := by
  have h := congrArg List.length (flatten_map_eq (fun t => t.1))
  rw [List.length_map, List.length_map] at h
  rw [h, inc_length]

/-- **THE LEFT IDS ARE A PERMUTATION OF THE WHOLE LEVEL-2 INVENTORY.** -/
theorem left_perm_range :
    List.Perm (level3Incidence.map (fun e => e.left.val)) (List.range 5508) := by
  have h0 : (blocks level3Incidence).foldl (stepL (fun e => e.left.val)) (0, true)
      = (5508, true) := inc_left_ranges
  have h := foldl_perm (fun e => e.left.val) (blocks level3Incidence) 0 (by rw [h0])
  rw [blocks_flatten_length] at h
  have he : (blocks level3Incidence).flatten.map (fun e => e.left.val)
      = level3Incidence.map (fun e => e.left.val) := flatten_map_eq (fun t => t.2.2.2.2.1)
  rw [he] at h
  simpa [List.range_eq_range'] using h

/-! ## §4  The typed equivalences -/

/-- The released incidence occurrence carrier: one occurrence per released split. -/
abbrev Occ := Fin 5508

/-- The released split at an occurrence. -/
def rowOf (i : Occ) : Level3Incidence :=
  level3Incidence[(i : ℕ)]'(by rw [inc_length]; exact i.isLt)

/-- The released left-half `Level2TermId` of an occurrence. -/
def leftOcc (i : Occ) : Level2TermId := (rowOf i).left


private theorem nodup_of_perm_range (f : Level3Incidence → Level2TermId)
    (h : List.Perm (level3Incidence.map (fun e => (f e).val)) (List.range 5508)) :
    (level3Incidence.map f).Nodup := by
  have hn : (level3Incidence.map (fun e => (f e).val)).Nodup :=
    h.nodup_iff.mpr List.nodup_range
  have he : level3Incidence.map (fun e => (f e).val)
      = (level3Incidence.map f).map Fin.val := by rw [List.map_map]; rfl
  rw [he] at hn
  exact List.Nodup.of_map _ hn

private theorem occ_inj (f : Level3Incidence → Level2TermId)
    (h : List.Perm (level3Incidence.map (fun e => (f e).val)) (List.range 5508)) :
    Function.Injective (fun i : Occ => f (rowOf i)) := by
  have hn := nodup_of_perm_range f h
  have hget : Function.Injective (level3Incidence.map f).get :=
    List.nodup_iff_injective_get.mp hn
  have hlen : (level3Incidence.map f).length = 5508 := by
    rw [List.length_map, inc_length]
  have key : ∀ (c : Occ) (hc : (c : ℕ) < (level3Incidence.map f).length),
      (level3Incidence.map f).get ⟨(c : ℕ), hc⟩ = f (rowOf c) := by
    intro c hc
    rw [List.get_eq_getElem, List.getElem_map]
    rfl
  intro a b hab
  have ha : (a : ℕ) < (level3Incidence.map f).length := by rw [hlen]; exact a.isLt
  have hb : (b : ℕ) < (level3Incidence.map f).length := by rw [hlen]; exact b.isLt
  have hmk : (⟨(a : ℕ), ha⟩ : Fin (level3Incidence.map f).length) = ⟨(b : ℕ), hb⟩ :=
    hget (by rw [key a ha, key b hb]; exact hab)
  rw [Fin.mk.injEq] at hmk
  exact Fin.ext hmk

/-- **THE LEFT-ID MAP IS A BIJECTION.**  Every released `Level2TermId` is the left half of
exactly one released split — the typed inventory equality, as a `Function.Bijective` object. -/
theorem leftOcc_bijective : Function.Bijective leftOcc :=
  Finite.injective_iff_bijective.mp (occ_inj (fun e => e.left) left_perm_range)


/-- **THE TYPED OCCURRENCE / LEVEL-2-INVENTORY EQUIVALENCE**, left halves. -/
noncomputable def leftEquiv : Occ ≃ Level2TermId := Equiv.ofBijective leftOcc leftOcc_bijective

end ADVXXZT2
end OmegaBound
