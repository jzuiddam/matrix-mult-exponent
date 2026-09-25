import OmegaBound.ADVXXZGeneralPopulation

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem conditional_collision_union {Ω J : Type*} [DecidableEq Ω] [DecidableEq J]
    (E : Finset Ω) (hE : E.Nonempty) (rivals : Finset J)
    (hits : J → Finset Ω) (M : ℕ) (hM : 0 < M)
    (pair : ∀ j ∈ rivals, cond E (hits j) ≤ 1/(M:ℝ)) :
  cond E (rivals.biUnion hits) ≤ (rivals.card : ℝ)/M := by
  unfold cond at pair ⊢
  rw [Finset.inter_biUnion]
  calc
    (((rivals.biUnion fun j => E ∩ hits j).card : ℕ) : ℝ) / E.card ≤
        (∑ j ∈ rivals, (((E ∩ hits j).card : ℕ) : ℝ)) / E.card := by
          gcongr
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ rivals, ((((E ∩ hits j).card : ℕ) : ℝ) / E.card) := by
          rw [Finset.sum_div]
    _ ≤ ∑ j ∈ rivals, (1 / (M : ℝ)) := by
          exact Finset.sum_le_sum fun j hj => pair j hj
    _ = (rivals.card : ℝ) / M := by
          simp [div_eq_mul_inv]

theorem exists_good_subfamily
    {Ω J B : Type*} [Fintype Ω] [Fintype J] [Fintype B]
    [DecidableEq Ω] [DecidableEq J] [DecidableEq B]
    [Nonempty Ω] [Nonempty J]
    (bucket : J → B → Finset Ω) (selected : Ω → Finset J)
    (h : Ω → J → Side → ℕ) (P : Side → ℕ) (t : Side → ℝ)
    (M : ℕ) (hM : 0 < M) (a : ℝ) (debit : Side → ℝ)
    (bucket_size : ∀ j b,
      ((bucket j b).card : ℝ) * M^2 = Fintype.card Ω)
    (bucket_disjoint : ∀ j,
      Pairwise (fun b c => Disjoint (bucket j b) (bucket j c)))
    (survival : ∀ j b, a ≤ cond (bucket j b)
      (Finset.univ.filter (fun ω => j ∈ selected ω)))
    (failure : ∀ j b W, cond (bucket j b)
      (Finset.univ.filter (fun ω => t W * (P W : ℝ) < (h ω j W : ℝ)))
      ≤ debit W)
    (margin : 0 < a - ∑ W, debit W) :
  ∃ ω : Ω,
    (a - ∑ W, debit W) * Fintype.card J * Fintype.card B / (M : ℝ)^2 ≤
      (((selected ω).filter (fun j =>
        ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ))).card : ℝ) := by
  classical
  let present : J → Finset Ω := fun j =>
    Finset.univ.filter (fun ω => j ∈ selected ω)
  let bad : J → Side → Finset Ω := fun j W =>
    Finset.univ.filter (fun ω => t W * (P W : ℝ) < (h ω j W : ℝ))
  let good : J → Finset Ω := fun j =>
    Finset.univ.filter (fun ω =>
      j ∈ selected ω ∧ ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ))
  let score : Ω → Finset J := fun ω =>
    (selected ω).filter (fun j =>
      ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ))
  have hMreal : 0 < (M : ℝ) ^ 2 := by positivity
  have hΩreal : 0 < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have bucket_card_eq (j : J) (b : B) :
      ((bucket j b).card : ℝ) = (Fintype.card Ω : ℝ) / (M : ℝ) ^ 2 := by
    apply (eq_div_iff (ne_of_gt hMreal)).2
    exact bucket_size j b
  have bucket_card_pos (j : J) (b : B) : 0 < ((bucket j b).card : ℝ) := by
    rw [bucket_card_eq j b]
    positivity
  have bucket_lower (j : J) (b : B) :
      (a - ∑ W, debit W) * ((bucket j b).card : ℝ) ≤
        ((bucket j b ∩ good j).card : ℝ) := by
    have hsurv :
        a * ((bucket j b).card : ℝ) ≤ ((bucket j b ∩ present j).card : ℝ) := by
      apply (le_div_iff₀ (bucket_card_pos j b)).mp
      simpa [present, cond] using survival j b
    have hfail (W : Side) :
        ((bucket j b ∩ bad j W).card : ℝ) ≤
          debit W * ((bucket j b).card : ℝ) := by
      apply (div_le_iff₀ (bucket_card_pos j b)).mp
      simpa [bad, cond] using failure j b W
    have hcover :
        bucket j b ∩ present j ⊆
          (bucket j b ∩ good j) ∪
            (Finset.univ.biUnion fun W => bucket j b ∩ bad j W) := by
      intro ω hω
      have hωbucket := (Finset.mem_inter.mp hω).1
      have hωselected : j ∈ selected ω := by
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hω).2).2
      by_cases hall : ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
          ⟨hωbucket, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hωselected, hall⟩⟩)
      · push_neg at hall
        obtain ⟨W, hW⟩ := hall
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨W, Finset.mem_univ _, Finset.mem_inter.mpr
            ⟨hωbucket, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW⟩⟩⟩)
    have hcoverNat :
        (bucket j b ∩ present j).card ≤
          (bucket j b ∩ good j).card +
            ∑ W : Side, (bucket j b ∩ bad j W).card := by
      calc
        (bucket j b ∩ present j).card ≤
            ((bucket j b ∩ good j) ∪
              (Finset.univ.biUnion fun W => bucket j b ∩ bad j W)).card :=
          Finset.card_le_card hcover
        _ ≤ (bucket j b ∩ good j).card +
              (Finset.univ.biUnion fun W => bucket j b ∩ bad j W).card :=
          Finset.card_union_le _ _
        _ ≤ (bucket j b ∩ good j).card +
              ∑ W : Side, (bucket j b ∩ bad j W).card := by
          exact Nat.add_le_add_left Finset.card_biUnion_le _
    have hcoverReal :
        ((bucket j b ∩ present j).card : ℝ) ≤
          ((bucket j b ∩ good j).card : ℝ) +
            ∑ W : Side, ((bucket j b ∩ bad j W).card : ℝ) := by
      exact_mod_cast hcoverNat
    have hfailSum :
        (∑ W : Side, ((bucket j b ∩ bad j W).card : ℝ)) ≤
          (∑ W, debit W) * ((bucket j b).card : ℝ) := by
      calc
        (∑ W : Side, ((bucket j b ∩ bad j W).card : ℝ)) ≤
            ∑ W : Side, debit W * ((bucket j b).card : ℝ) := by
          exact Finset.sum_le_sum fun W _ => hfail W
        _ = (∑ W, debit W) * ((bucket j b).card : ℝ) := by
          rw [Finset.sum_mul]
    calc
      (a - ∑ W, debit W) * ((bucket j b).card : ℝ) =
          a * ((bucket j b).card : ℝ) -
            (∑ W, debit W) * ((bucket j b).card : ℝ) := by ring
      _ ≤ ((bucket j b ∩ present j).card : ℝ) -
            ∑ W : Side, ((bucket j b ∩ bad j W).card : ℝ) :=
        sub_le_sub hsurv hfailSum
      _ ≤ ((bucket j b ∩ good j).card : ℝ) := by linarith
  have bucket_good_disjoint (j : J) :
      ((Finset.univ : Finset B) : Set B).PairwiseDisjoint
        (fun b => bucket j b ∩ good j) := by
    intro b _ c _ hbc
    exact (bucket_disjoint j hbc).mono Finset.inter_subset_left Finset.inter_subset_left
  have bucket_good_union_subset (j : J) :
      (Finset.univ.biUnion fun b => bucket j b ∩ good j) ⊆ good j := by
    intro ω hω
    obtain ⟨b, _, hωb⟩ := Finset.mem_biUnion.mp hω
    exact (Finset.mem_inter.mp hωb).2
  have per_label (j : J) :
      (a - ∑ W, debit W) * (Fintype.card B : ℝ) *
          (Fintype.card Ω : ℝ) / (M : ℝ)^2 ≤ ((good j).card : ℝ) := by
    calc
      (a - ∑ W, debit W) * (Fintype.card B : ℝ) *
            (Fintype.card Ω : ℝ) / (M : ℝ)^2 =
          ∑ b : B, (a - ∑ W, debit W) * ((bucket j b).card : ℝ) := by
        simp_rw [bucket_card_eq]
        simp
        ring
      _ ≤ ∑ b : B, ((bucket j b ∩ good j).card : ℝ) := by
        exact Finset.sum_le_sum fun b _ => bucket_lower j b
      _ = ((Finset.univ.biUnion fun b => bucket j b ∩ good j).card : ℝ) := by
        rw [Finset.card_biUnion (bucket_good_disjoint j), Nat.cast_sum]
      _ ≤ ((good j).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (bucket_good_union_subset j)
  have double_count :
      (∑ j : J, ((good j).card : ℝ)) =
        ∑ ω : Ω, ((score ω).card : ℝ) := by
    calc
      (∑ j : J, ((good j).card : ℝ)) =
          ∑ j : J, ∑ ω : Ω,
            if j ∈ selected ω ∧
              (∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simpa [good] using
          (Finset.natCast_card_filter
            (R := ℝ)
            (fun ω : Ω => j ∈ selected ω ∧
              ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) Finset.univ)
      _ = ∑ ω : Ω, ∑ j : J,
            if j ∈ selected ω ∧
              (∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ ω : Ω, ((score ω).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro ω _
        calc
          (∑ j : J,
              if j ∈ selected ω ∧
                (∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) then (1 : ℝ) else 0) =
              ((Finset.univ.filter (fun j : J =>
                j ∈ selected ω ∧
                  ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ))).card : ℝ) := by
            exact (Finset.natCast_card_filter
              (R := ℝ)
              (fun j : J => j ∈ selected ω ∧
                ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) Finset.univ).symm
          _ = ((score ω).card : ℝ) := by
            have hscore :
                Finset.univ.filter (fun j : J =>
                  j ∈ selected ω ∧
                    ∀ W, (h ω j W : ℝ) ≤ t W * (P W : ℝ)) = score ω := by
              ext j
              simp [score]
            rw [hscore]
  have total :
      (∑ _ω : Ω,
        (a - ∑ W, debit W) * Fintype.card J * Fintype.card B / (M : ℝ)^2) ≤
        ∑ ω : Ω, ((score ω).card : ℝ) := by
    calc
      (∑ _ω : Ω,
          (a - ∑ W, debit W) * Fintype.card J * Fintype.card B / (M : ℝ)^2) =
          ∑ j : J,
            (a - ∑ W, debit W) * (Fintype.card B : ℝ) *
              (Fintype.card Ω : ℝ) / (M : ℝ)^2 := by
        simp
        ring
      _ ≤ ∑ j : J, ((good j).card : ℝ) := by
        exact Finset.sum_le_sum fun j _ => per_label j
      _ = ∑ ω : Ω, ((score ω).card : ℝ) := double_count
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset Ω)) Finset.univ_nonempty total
  exact ⟨ω, by simpa [score] using hω⟩

end OmegaBound.ADVXXZGeneral
end
