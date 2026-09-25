import OmegaBound.ADVXXZGeneralGridInput29Facts
import OmegaBound.ADVXXZGeneralInputCellAggregation
import OmegaBound.ADVXXZGeneralInputTransportCont3
import OmegaBound.ADVXXZGeneralPProjectionParent25

set_option autoImplicit false

/-!
# The weakened hypotheses of the input-concentration chain, and the grid instance

`ConstituentAdmissibleAt` and `StepIntegralAt` are consumed by the input-concentration chain only
through four admissibility fields (`pair_mixture`, `regional_support`, `child_support`,
`out_eq`) and two integrality consequences (exact alpha counts, exact chunk counts).  The
empirical grid spec satisfies all of them, at its own scale `m`, even though it satisfies
neither `child_boundary` nor `StepIntegralAt`.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The part of `ConstituentAdmissibleAt` the input-concentration chain uses.  It omits
`roles`, `mixture` (both unused) and, crucially, `child_boundary`, which the empirical grid
does not satisfy. -/
structure InputAdm29 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) : Prop where
  pair_mixture : ∀ W t r σ, (d.betaRegion W t r).prob σ =
    ∑ u, (d.alpha t r).prob u *
      (d.betaChild W t r u).prob (leftHalf σ) *
      (d.betaChild W t r (complement p t u)).prob (rightHalf σ)
  regional_support : ∀ W t r, Supported (d.betaRegion W t r)
    (match W with | .X => p.i t | .Y => p.j t | .Z => p.k t)
  child_support : ∀ W t r u, Supported (d.betaChild W t r u) (coord W u.1)
  out_eq : ∀ t r u, (d.outBase ⟨t,r,u⟩ : ℚ) =
    (b : ℚ) * p.baseN t * (d.A t).prob r *
      ((d.alpha t r).prob u + (d.alpha t r).prob (complement p t u))

/-- The part of `StepIntegralAt` the input-concentration chain uses, **at one scale `m`**.
The chunk-count clause is stated as the conclusion the fixed-spec proof derives from
integrality; at the grid it is an identity, because the grid law's denominator is exactly
`m * outBase`. -/
structure InputInt29 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b m : ℕ) : Prop where
  bpos : 0 < b
  alphaIntegral : ∀ (t : Fin s) (r : Fin 6) (u : ChildShape p t),
    integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u)
  countsExact : ∀ (r : Fin 6) (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ

theorem rat_floor_natCast29 (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

/-! ## The fixed spec satisfies both weakened hypotheses -/


theorem inputInt29_of_stepIntegralAt {w s b : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} (hb : StepIntegralAt p d b) (m : ℕ) :
    InputInt29 d b m := by
  refine { bpos := hb.1, alphaIntegral := ?_, countsExact := ?_ }
  · intro t r u; exact ((hb.2 t r).2 u).1
  · intro r W t u σ
    rcases ((hb.2 t r).2 u).2.2 W σ with ⟨n, hn⟩
    have hscaled :
        (((m * d.outBase ⟨t,r,u⟩ : ℕ) : ℚ) * (d.betaChild W t r u).prob σ) =
          ((m * n : ℕ) : ℚ) := by
      calc
        _ = (m : ℚ) * ((d.outBase ⟨t,r,u⟩ : ℚ) * (d.betaChild W t r u).prob σ) := by
              push_cast; ring
        _ = (m : ℚ) * n := by rw [hn]
        _ = ((m * n : ℕ) : ℚ) := by norm_cast
    unfold stageCounts27
    rw [hscaled, rat_floor_natCast29]
    calc
      ((m * n : ℕ) : ℚ) = (m : ℚ) * n := by norm_cast
      _ = (m : ℚ) * ((d.outBase ⟨t,r,u⟩ : ℚ) * (d.betaChild W t r u).prob σ) :=
            congrArg (fun x : ℚ => (m : ℚ) * x) hn.symm
      _ = (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ := by ring

/-! ## The grid instance -/

/-- The empirical grid spec satisfies the four used admissibility clauses. -/
theorem gridInputAdm29 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b) (m : ℕ)
    (h : ConstituentExactGrid27 d m) :
    InputAdm29 (constituentGridSpec27 d hd m h) b := by
  refine { pair_mixture := ?_, regional_support := ?_, child_support := ?_,
           out_eq := ?_ }
  · intro W t r σ
    exact constituentGridSpec27_pair_mixture d m h W t r σ
  · intro W t r
    exact constituentGridRegion_supported27 d hd m h W t r
  · intro W t r u
    exact constituentGridBeta_supported27 d hd m h W t r u
  · intro t r u
    exact hd.out_eq t r u

/-- **No floor defect at the grid.**  The per-cell chunk count of the empirical grid spec is
exactly the grid histogram, so the chunk-count clause of `InputInt29` holds at the grid's own
scale `m` as an identity — this is what replaces the perturbed `StepIntegralAt`, which does
not hold. -/
theorem gridStageCounts_cast {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b) (m : ℕ)
    (h : ConstituentExactGrid27 d m) (r : Fin 6) (W : Side) (t : Fin s)
    (u : ChildShape p t) (σ : Chunk w) :
    (stageCounts27 m (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) r W t u σ : ℚ) =
      (m : ℚ) * (constituentGridSpec27 d hd m h).outBase ⟨t,r,u⟩ *
        ((constituentGridSpec27 d hd m h).betaChild W t r u).prob σ := by
  show ((((m * d.outBase ⟨t,r,u⟩ : ℕ) : ℚ) *
      (constituentGridBeta27 d m h W t r u).prob σ).floor.toNat : ℚ) =
    (m : ℚ) * (d.outBase ⟨t,r,u⟩ : ℚ) *
      (constituentGridBeta27 d m h W t r u).prob σ
  by_cases hn : 0 < constituentOutN d.toPaper m
      (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩)
  · have hN : constituentOutN d.toPaper m
        (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) = d.outBase ⟨t,r,u⟩ * m :=
      constituentOutN_grid_index d m t r u
    have hpos : 0 < d.outBase ⟨t,r,u⟩ * m := by rw [← hN]; exact hn
    have hob0 : (d.outBase ⟨t,r,u⟩ : ℚ) ≠ 0 := by
      have hgt : 0 < d.outBase ⟨t,r,u⟩ := Nat.pos_of_ne_zero (by
        intro hz; rw [hz, Nat.zero_mul] at hpos; exact absurd hpos (lt_irrefl 0))
      positivity
    have hm0 : (m : ℚ) ≠ 0 := by
      have : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm, Nat.mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        · exact hm
      positivity
    set H : ℕ := ((h.val (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) W σ).val : ℕ)
      with hH
    have hprob : (constituentGridBeta27 d m h W t r u).prob σ =
        (H : ℚ) / ((constituentOutN d.toPaper m
          (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) : ℕ) : ℚ) :=
      constituentGridBeta27_prob_pos d m h W t r u σ hn
    have hNQ : ((constituentOutN d.toPaper m
        (Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩) : ℕ) : ℚ) =
        (d.outBase ⟨t,r,u⟩ : ℚ) * (m : ℚ) := by
      rw [hN]; push_cast; ring
    have hkey : (((m * d.outBase ⟨t,r,u⟩ : ℕ) : ℚ) *
        (constituentGridBeta27 d m h W t r u).prob σ) = ((H : ℕ) : ℚ) := by
      rw [hprob, hNQ]
      push_cast
      field_simp
    rw [hkey, rat_floor_natCast29, hprob, hNQ]
    field_simp
  · have hzero : d.outBase ⟨t,r,u⟩ * m = 0 := by
      by_contra hc
      exact hn (by rw [constituentOutN_grid_index]; exact Nat.pos_of_ne_zero hc)
    have hmz : m * d.outBase ⟨t,r,u⟩ = 0 := by rw [Nat.mul_comm]; exact hzero
    have hR : (m : ℚ) * (d.outBase ⟨t,r,u⟩ : ℚ) = 0 := by
      have hc := congrArg (fun n : ℕ => (n : ℚ)) hmz
      push_cast at hc
      exact hc
    rw [hmz, hR, zero_mul]
    norm_num

/-- The empirical grid spec satisfies the weakened integrality at its own scale `m`. -/
theorem gridInputInt29 {w s b : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (hd : ConstituentAdmissibleAt d b)
    (hb : StepIntegralAt p d b) (m : ℕ) (h : ConstituentExactGrid27 d m) :
    InputInt29 (constituentGridSpec27 d hd m h) b m := by
  refine { bpos := hb.1, alphaIntegral := ?_, countsExact := ?_ }
  · intro t r u
    exact ((hb.2 t r).2 u).1
  · intro r W t u σ
    exact gridStageCounts_cast d hd m h r W t u σ

end
end OmegaBound.ADVXXZGeneral
end
