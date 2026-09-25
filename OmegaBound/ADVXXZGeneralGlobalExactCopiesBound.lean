import OmegaBound.ADVXXZGeneralGlobalExactModulusBranches

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem gcb_div_lower27 {a s : ℕ} (hs : 0 < s) (hpos : 0 < a / s) :
    a < 2 * (a / s) * s := by
  have hmod : a % s < s := Nat.mod_lt _ hs
  have hdiv : s * (a / s) + a % s = a := Nat.div_add_mod _ _
  have hle : s ≤ s * (a / s) := by
    have := Nat.mul_le_mul (le_refl s) hpos
    simpa using this
  calc a = s * (a / s) + a % s := hdiv.symm
    _ < s * (a / s) + s := Nat.add_lt_add_left hmod _
    _ ≤ s * (a / s) + s * (a / s) := Nat.add_le_add_left hle _
    _ = 2 * (a / s) * s := by ring

/-- The abstract arithmetic behind the copy count: a good family covering at least
    `(11/20)*T*Bc/M2` labels, cut into reserve groups, leaves at least
    `(11/40)*T*Bc/(M2*R)` complete groups. -/
private theorem gcb_arith27 {T Bc M2 R Jc Cc : ℝ}
    (hM2 : 0 < M2) (hR : 0 < R)
    (hgood : (11 / 20 : ℝ) * T * Bc / M2 ≤ Jc)
    (hlt : Jc < 2 * Cc * R) :
    (11 / 40 : ℝ) * T * Bc / (M2 * R) ≤ Cc := by
  have hkey : (11 / 20 : ℝ) * T * Bc / M2 < 2 * Cc * R := lt_of_le_of_lt hgood hlt
  rw [div_lt_iff₀ hM2] at hkey
  rw [div_le_iff₀ (mul_pos hM2 hR)]
  nlinarith [hkey]

set_option maxHeartbeats 1000000 in
-- The dependent good family and the regional broken family share label-indexed leg types.
/--
**Quantitative occupied-region repair.**  Re-running the three paper gates and the reserve quotient
keeps the count: at least half the good-family/reserve quotient survives, which is the number
needed by the exact-grid product bound.
-/
theorem globalGoodFamily_repair_selected_region_bound27 {w b M : ℕ} [NeZero M]
    (q : ℕ) (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (hb : GlobalIntegral g b) (floor m : ℕ) (hm : 0 < m)
    (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (j0 : GlobalTargetLabel27 g xi r) (b0 : GlobalBucketLabel27 B)
    (hn : (globalPopulation g (b * m) xi r).n ≠ 0)
    (hreserve :
      (repairReserve (2 * (globalPopulation g (b * m) xi r).n)
        (fun W => Fintype.card
          (GlobalExactPart27 g (b * m) xi r j0.val W)) : ℝ) ≤
      (11 / 20 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
        Fintype.card (GlobalBucketLabel27 B) / (M : ℝ) ^ 2) :
    ∃ (omega : HashOutcome (globalPopulation g (b * m) xi r) M) (copies : ℕ),
      0 < copies ∧
      (11 / 40 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
          Fintype.card (GlobalBucketLabel27 B) /
          ((M : ℝ) ^ 2 * (repairReserve (2 * (globalPopulation g (b * m) xi r).n)
            (fun W => Fintype.card
              (GlobalExactPart27 g (b * m) xi r j0.val W)) : ℝ)) ≤ (copies : ℝ) ∧
      Restricts (copiesZ copies (globalExactITensor27 q g xi r j0.val)).tensor
        (globalSelectedRegionFamily27 q g xi r B omega).tensor := by
  classical
  obtain ⟨omega, hgood⟩ := global_compatible_grid_good_family_paper27
    g hg hw floor m hm xi hxi r B hprime hodd hfloor hdemand hb.1 j0 b0
  set J := globalPaperGoodTargets27 g m xi r B omega j0 with hJdef
  set reserve := repairReserve (2 * (globalPopulation g (b * m) xi r).n)
    (fun W => Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val W)) with hRdef
  have hreserveCardReal : (reserve : ℝ) ≤ (J.card : ℝ) := le_trans hreserve hgood
  have hreserveCard : reserve ≤ J.card := by exact_mod_cast hreserveCardReal
  have hreservePos : 0 < reserve := by rw [hRdef]; exact repairReserve_pos _ _
  have hcopies : 0 < J.card / reserve := Nat.div_pos hreserveCard hreservePos
  refine ⟨omega, J.card / reserve, hcopies, ?_, ?_⟩
  · have hM0 : (0 : ℝ) < (M : ℝ) := by
      have : 0 < M := by omega
      exact_mod_cast this
    have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
    have hR0 : (0 : ℝ) < (reserve : ℝ) := by exact_mod_cast hreservePos
    have hlt2 : J.card < 2 * (J.card / reserve) * reserve :=
      gcb_div_lower27 hreservePos hcopies
    have hltR : (J.card : ℝ) < 2 * ((J.card / reserve : ℕ) : ℝ) * (reserve : ℝ) := by
      exact_mod_cast hlt2
    exact gcb_arith27 hM2 hR0 hgood hltR
  · exact Tensor3.Restricts.trans
      (globalRepairPaperGoodFamily27 q g hw hb m hm xi r B omega j0 hn hcopies)
      (globalPaperGoodTargets_restricts_region27 q g m xi r B omega j0 hn)


end
end OmegaBound.ADVXXZGeneral
end
