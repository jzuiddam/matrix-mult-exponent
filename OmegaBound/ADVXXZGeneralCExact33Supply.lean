import OmegaBound.ADVXXZGeneralCExact33Sublinear
import OmegaBound.ADVXXZGeneralCExact33Statements

set_option autoImplicit false

/-!
# The two case-analysis halves of `S_constituent_grid_broken_supply33`

`S_constituent_grid_broken_supply33` splits, region by region, on whether the
grid population `N_r` vanishes.

* On `N_r = 0` the displayed right-hand side is the literal `1`, so the obligation is
  `Real.exp (log 2 · E_r · b·m − δ ε · cLength − ell ε m) ≤ 1`, i.e. a NON-POSITIVE exponent.
  `regionRate_eq_zero_of_mass_zero` supplies the only source of that: a region of zero mass has
  `E_r = 0`, whence the exponent is `−δ ε · cLength − ell ε m ≤ 0`.
* On `N_r ≠ 0` the displayed right-hand side is a REAL quotient, and
  `constituent_regional_quotient33` turns it into the multiplicative form
  `reserve_r · exp(…) ≤ #(P.selected r)` that the counting argument actually produces.

Both are proved here.  The counting argument itself is `constituent_grid_selection_count41`
(`ADVXXZGeneralCExact41SelectionCount`).
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
open StageCandidateRaw
noncomputable section

theorem probR_eq_cast_prob33 {ι : Type*} [Fintype ι]
    (P : RatDist ι) (a : ι) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

/-- **A zero-mass region has zero rate.**  Every row of `constituentRegionRate` carries the factor
`A_{t,r} · n_t`, so the guard `∑ t, n_t · A_{t,r} = 0` of `RegionalCopyBound33` forces `E_r = 0`. -/
theorem regionRate_eq_zero_of_mass_zero {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6)
    (hmass : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0) :
    constituentRegionRate d.toPaper r = 0 := by
  have hterm : ∀ t : Fin s, (p.baseN t : ℚ) * (d.A t).prob r = 0 := by
    intro t
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin s)),
        0 ≤ (p.baseN i : ℚ) * (d.A i).prob r :=
      fun i _ => mul_nonneg (by positivity) ((d.A i).prob_nonneg r)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hmass t (Finset.mem_univ t)
  have htermR : ∀ t : Fin s, d.toPaper.A t r * (p.baseN t : ℝ) = 0 := by
    intro t
    have h0 : (p.baseN t : ℝ) * (((d.A t).prob r : ℚ) : ℝ) = 0 := by
      have hc := congrArg (fun x : ℚ => (x : ℝ)) (hterm t)
      push_cast at hc
      exact hc
    show (d.A t).probR r * (p.baseN t : ℝ) = 0
    rw [probR_eq_cast_prob33, mul_comm]
    exact h0
  have hX : constituentRowX d.toPaper r (d.toPaper.perm r .X) = 0 := by
    unfold constituentRowX
    exact Finset.sum_eq_zero (fun t _ => by rw [htermR t, zero_mul])
  have hY : constituentRowY d.toPaper r (d.toPaper.perm r .X) (d.toPaper.perm r .Y)
      (d.toPaper.perm r .Z) = 0 := by
    unfold constituentRowY
    exact Finset.sum_eq_zero (fun t _ => by rw [htermR t, zero_mul])
  have hZ : constituentRowZ d.toPaper r (d.toPaper.perm r .X) (d.toPaper.perm r .Y)
      (d.toPaper.perm r .Z) = 0 := by
    unfold constituentRowZ
    exact Finset.sum_eq_zero (fun t _ => by rw [htermR t, zero_mul])
  have hsplit : constituentRegionRate d.toPaper r
      = min (constituentRowX d.toPaper r (d.toPaper.perm r .X))
          (min (constituentRowY d.toPaper r (d.toPaper.perm r .X) (d.toPaper.perm r .Y)
              (d.toPaper.perm r .Z))
            (constituentRowZ d.toPaper r (d.toPaper.perm r .X) (d.toPaper.perm r .Y)
              (d.toPaper.perm r .Z))) := rfl
  rw [hsplit, hX, hY, hZ]
  simp

theorem constituentRegionalReserve33_pos (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) (r : Fin 6) :
    0 < constituentRegionalReserve33 q P r := by
  have hbody : constituentRegionalReserve33 q P r =
      (if (stagePopulationAt q (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) b m r).n = 0 then 1
       else repairReserve ((stagePopulationAt q (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) b m r).n)
         (fun W => (P.selected r).sup
           (fun j => (exactPartsAt q b m (constituentGridParent27 d hd m h)
             (constituentGridSpec27 d hd m h) r j W).card))) := rfl
  rw [hbody]
  split_ifs
  · norm_num
  · exact repairReserve_pos _ _

/-- **The displayed real quotient, from the multiplicative form.**  This is the only arithmetic
content of the conclusion of `S_constituent_grid_broken_supply33`; the two hypotheses are exactly what a
counting argument has to deliver. -/
theorem constituent_regional_quotient33 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} {d : ConstituentSpec p}
    {hd : ConstituentAdmissibleAt d b} {ε : ℚ} {m : ℕ}
    {h : ConstituentExactGrid27 d m}
    (P : ConstituentGridProduction29 q d hd ε m h) (r : Fin 6) (x : ℝ)
    (hzero : (stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r).n = 0 → x ≤ 0)
    (hmul : (stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r).n ≠ 0 →
      (constituentRegionalReserve33 q P r : ℝ) * Real.exp x
        ≤ ((P.selected r).card : ℝ)) :
    Real.exp x ≤
      (if (stagePopulationAt q (constituentGridParent27 d hd m h)
            (constituentGridSpec27 d hd m h) b m r).n = 0 then 1 else
        ((P.selected r).card : ℝ) / (constituentRegionalReserve33 q P r : ℝ)) := by
  split_ifs with hz
  · exact Real.exp_le_one_iff.mpr (hzero hz)
  · have hres : (0:ℝ) < (constituentRegionalReserve33 q P r : ℝ) := by
      exact_mod_cast constituentRegionalReserve33_pos q P r
    rw [le_div_iff₀ hres, mul_comm]
    exact hmul hz

/-- The exponent in `S_constituent_grid_broken_supply33` is non-positive on a zero-mass
region, whatever the tolerance debit and the loss (both are non-negative). -/
theorem grid_broken_exponent_nonpos_of_mass_zero {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (r : Fin 6) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ)
    (hdelta : VanishesWithTolerance delta) (hell : ∀ ε m, 0 ≤ ell ε m)
    (hmass : (∑ t, (p.baseN t : ℚ) * (d.A t).prob r) = 0) (ε : ℚ) (m : ℕ) :
    Real.log 2 * constituentRegionRate d.toPaper r * (b*m : ℝ)
      - delta ε * (cLength p b m : ℝ) - ell ε m ≤ 0 := by
  rw [regionRate_eq_zero_of_mass_zero p d r hmass]
  have h1 : 0 ≤ delta ε * (cLength p b m : ℝ) :=
    mul_nonneg (hdelta.1 ε) (by positivity)
  have h2 : 0 ≤ ell ε m := hell ε m
  simp only [mul_zero, zero_mul]
  linarith

/-- Type check: the proved `constituent_repair_pool_sublinear33` inhabits the statement
`S_constituent_repair_pool_sublinear33`. -/
theorem S_constituent_repair_pool_sublinear33_holds :
    S_constituent_repair_pool_sublinear33 :=
  fun q w s b hq hw p d hd hb => constituent_repair_pool_sublinear33 q w s b hq hw p d hd hb

end
end OmegaBound.ADVXXZGeneral
end
