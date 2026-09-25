import OmegaBound.ADVXXZGeneralIterateInfraCopies
import OmegaBound.ADVXXZGeneralIterateInfraRates

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- Tensor product packaged as an integral physical tensor. -/
def tensorProdZ (B P : ITensor) : ITensor :=
  { X := B.X × P.X
    Y := B.Y × P.Y
    Z := B.Z × P.Z
    tensor := tensorProd B.tensor P.tensor }

private noncomputable def poolRegroupEquiv (R Q : ℕ) : Fin (R * Q) ≃ Fin R × Fin Q :=
  Fintype.equivOfCardEq (by simp)

/-- `R*Q` copies of `B⊗P` and `R` copies of `B⊗(Q copies of P)` are the same
labelled direct sum up to reindexing.  The old `B` factor is carried once in each labelled
summand; it is not exponentiated by a copy count. -/
theorem copiesZ_tensorProdZ_regroup (R Q : ℕ) (B P : ITensor) :
    Restricts (copiesZ (R * Q) (tensorProdZ B P)).tensor
        (copiesZ R (tensorProdZ B (copiesZ Q P))).tensor ∧
      Restricts (copiesZ R (tensorProdZ B (copiesZ Q P))).tensor
        (copiesZ (R * Q) (tensorProdZ B P)).tensor := by
  classical
  let e := poolRegroupEquiv R Q
  constructor
  · refine ADVXXZ.restricts_of_sub
      (fun p => ((e p.1).1, (p.2.1, ((e p.1).2, p.2.2))))
      (fun p => ((e p.1).1, (p.2.1, ((e p.1).2, p.2.2))))
      (fun p => ((e p.1).1, (p.2.1, ((e p.1).2, p.2.2)))) ?_
    rintro ⟨i, ⟨bx, px⟩⟩ ⟨j, ⟨byy, py⟩⟩ ⟨k, ⟨bz, pz⟩⟩
    simp only [copiesZ, tensorProdZ, famDS, tensorProd, Finset.mem_univ, and_true]
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
  · refine ADVXXZ.restricts_of_sub
      (fun p => (e.symm (p.1, p.2.2.1), (p.2.1, p.2.2.2)))
      (fun p => (e.symm (p.1, p.2.2.1), (p.2.1, p.2.2.2)))
      (fun p => (e.symm (p.1, p.2.2.1), (p.2.1, p.2.2.2))) ?_
    rintro ⟨i, ⟨bx, ⟨a, px⟩⟩⟩ ⟨j, ⟨byy, ⟨b, py⟩⟩⟩
      ⟨k, ⟨bz, ⟨c, pz⟩⟩⟩
    simp only [copiesZ, tensorProdZ, famDS, tensorProd, Finset.mem_univ, and_true]
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
    by_cases ho : i = j ∧ j = k
    · by_cases hp : a = b ∧ b = c
      · rcases ho with ⟨rfl, rfl⟩
        rcases hp with ⟨rfl, rfl⟩
        simp
      · have hr : ¬((i = j ∧ a = b) ∧ j = k ∧ b = c) := by
          rintro ⟨⟨_, hab⟩, _, hbc⟩
          exact hp ⟨hab, hbc⟩
        simp [ho, hp, hr]
    · have hr : ¬((i = j ∧ a = b) ∧ j = k ∧ b = c) := by
        rintro ⟨⟨hij, _⟩, hjk, _⟩
        exact ho ⟨hij, hjk⟩
      simp [ho, hr]

private theorem tensorProdZ_left_refl (B : ITensor) :
    PolyDegeneratesAt ℤ 0 B.tensor B.tensor := by
  classical
  apply polyDegeneratesAt_of_restricts
  exact ADVXXZ.restricts_of_sub id id id (fun _ _ _ => rfl)

/-- Pool accounting.  A prefix producing `V_p` copies of `B⊗P` is run on `Q_s`
independent top-input batches; the stage is then applied inside each of the `V_p` outputs.
The resulting top pool is `Q_s*Q_p`, the result has `V_p*V_s` copies, and `B` is carried
exactly once per result. -/
theorem integral_pool_accounting
    (Qp Vp Qs Vs : ℕ) (Top B P S : ITensor)
    (hprefix : ∃ Np, PolyDegeneratesAt ℤ Np (copiesZ Qp Top).tensor
      (copiesZ Vp (tensorProdZ B P)).tensor)
    (hstage : ∃ Ns, PolyDegeneratesAt ℤ Ns (copiesZ Qs P).tensor
      (copiesZ Vs S).tensor) :
    ∃ N, PolyDegeneratesAt ℤ N (copiesZ (Qs * Qp) Top).tensor
      (copiesZ (Vp * Vs) (tensorProdZ B S)).tensor := by
  classical
  obtain ⟨Np, hp⟩ := hprefix
  obtain ⟨Ns, hs⟩ := hstage
  have hpBatches := polyDegeneratesAt_copies Qs hp
  have hsource : PolyDegeneratesAt ℤ 0 (copiesZ (Qs * Qp) Top).tensor
      (copiesZ Qs (copiesZ Qp Top)).tensor :=
    polyDegeneratesAt_of_restricts (copiesZ_nested_restricts_mul Qs Qp Top)
  obtain ⟨N₁, h₁⟩ := integral_polyDegeneratesAt_trans hsource hpBatches
  have htarget : PolyDegeneratesAt ℤ 0
      (copiesZ Qs (copiesZ Vp (tensorProdZ B P))).tensor
      (copiesZ (Qs * Vp) (tensorProdZ B P)).tensor :=
    polyDegeneratesAt_of_restricts
      (copiesZ_mul_restricts_nested Qs Vp (tensorProdZ B P))
  obtain ⟨N₂, h₂⟩ := integral_polyDegeneratesAt_trans h₁ htarget
  rw [Nat.mul_comm Qs Vp] at h₂
  have hregroup : PolyDegeneratesAt ℤ 0
      (copiesZ (Vp * Qs) (tensorProdZ B P)).tensor
      (copiesZ Vp (tensorProdZ B (copiesZ Qs P))).tensor := by
    apply polyDegeneratesAt_of_restricts
    exact (copiesZ_tensorProdZ_regroup Vp Qs B P).2
  obtain ⟨N₃, h₃⟩ := integral_polyDegeneratesAt_trans h₂ hregroup
  have hinside : PolyDegeneratesAt ℤ Ns
      (tensorProdZ B (copiesZ Qs P)).tensor
      (tensorProdZ B (copiesZ Vs S)).tensor := by
    simpa only [tensorProdZ, zero_add] using
      (polyDegeneratesAt_tensorProd (tensorProdZ_left_refl B) hs)
  have hinsideCopies := polyDegeneratesAt_copies Vp hinside
  obtain ⟨N₄, h₄⟩ := integral_polyDegeneratesAt_trans h₃ hinsideCopies
  have hfinal : PolyDegeneratesAt ℤ 0
      (copiesZ Vp (tensorProdZ B (copiesZ Vs S))).tensor
      (copiesZ (Vp * Vs) (tensorProdZ B S)).tensor :=
    polyDegeneratesAt_of_restricts (copiesZ_tensorProdZ_regroup Vp Vs B S).1
  exact integral_polyDegeneratesAt_trans h₄ hfinal

end OmegaBound.ADVXXZGeneral
end
