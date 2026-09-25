import OmegaBound.ADVXXZGeneralGridInput29Counts

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral.Grid29
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem stageAlphaCount_cast27 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : InputInt29 d b m) (r : Fin 6)
    (t : Fin s) (u : ChildShape p t) :
    (((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
      (d.alpha t r).prob u).floor.toNat : ℕ) : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u := by
  rcases hb.alphaIntegral t r u with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob u =
        ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) * ((b : ℚ) * p.baseN t * (d.A t).prob r *
          (d.alpha t r).prob u) := by push_cast; ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  rw [hscaled, rat_floor_natCast29]

private theorem stageCounts27_cast {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : InputInt29 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w) :
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ := by
  exact hb.countsExact r W t u σ

theorem stageCounts27_sum {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hb : InputInt29 d b m) (r : Fin 6)
    (W : Side) (t : Fin s) (u : ChildShape p t) :
    ∑ σ, stageCounts27 m p d r W t u σ = m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sum]
  simp_rw [stageCounts27_cast p d hb r W t u]
  rw [← Finset.mul_sum, RatDist.sum_prob]
  push_cast
  ring

theorem stageAlphaPair27 {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (t : Fin s) (u : ChildShape p t) :
    ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob u).floor.toNat +
      ((((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
        (d.alpha t r).prob (complement p t u)).floor.toNat)) =
      m * d.outBase ⟨t,r,u⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_add, stageAlphaCount_cast27 p d hb r t u,
    stageAlphaCount_cast27 p d hb r t (complement p t u)]
  push_cast
  rw [hd.out_eq t r u]
  ring

end
end OmegaBound.ADVXXZGeneral.Grid29
end
