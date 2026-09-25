import OmegaBound.CW90Block
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Coppersmith–Winograd 1990, §6: the hashing step

CW90 selects the blocks of `T_q^{⊗3N}` that survive by a hash.  Writing `I`, `J`, `K` for
the block indices (`0`/`1` strings of length `3N`) of an `x`-, `y`- and `z`-block, and
`w₀, w₁, …, w_{3N}` for uniformly random elements of `ℤ/M`, the hashes are

  `b_X(I) = ∑_p I_p w_p`,  `b_Y(J) = w₀ + ∑_p J_p w_p`,
  `b_Z(K) = (w₀ + ∑_p (2 - K_p) w_p) / 2`,

and one keeps only the blocks whose hash lies in a Salem–Spencer (3AP-free) set `B`.
CW90's equation (6) is the observation that a *compatible* triple satisfies
`I_p + J_p + K_p = 2` at every position, hence

  `b_X(I) + b_Y(J) = 2 b_Z(K)`.

Since `B` contains no three-term arithmetic progression, the three hashes of a surviving
compatible triple must coincide.

The proved content of this file is the bridge from Mathlib's Salem–Spencer machinery over `ℕ`
(`ThreeAPFree`, `rothNumberNat`, `Behrend.roth_lower_bound`) to the 3AP-free property in
`ZMod (2 * M₀ + 1)` that the hash needs: `CW90.apFree_zmod_image` and
`CW90.exists_apFree_zmod`.  This is CW90's remark (4): a 3AP-free set of integers below
`M/2` stays 3AP-free modulo `M`.

## Main results

* `CW90.apFree_zmod_image` — CW90 remark (4): 3AP-freeness survives reduction mod `2*M₀+1`.
* `CW90.exists_apFree_zmod` — a 3AP-free subset of `ZMod (2*M₀+1)` of size
  `rothNumberNat M₀ ≥ M₀ · exp(-4√(log M₀))` (Behrend, from Mathlib).
-/

open Finset

namespace OmegaBound

namespace CW90

/-! ## The hash -/

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The block index of an `x`-variable at a position: `0` where the `x`-variable is `x₀`
(colour `0`), `1` elsewhere. -/
def iX (R : Type*) [CommRing R] (σ : Blk N) (p : Fin (3 * N)) : R :=
  if col σ p = 0 then 0 else 1

/-- The block index of a `y`-variable at a position. -/
def iY (R : Type*) [CommRing R] (σ : Blk N) (p : Fin (3 * N)) : R :=
  if col σ p = 1 then 0 else 1

/-- `b_X(I) = ∑_p I_p w_p`. -/
def hashX (w : Fin (3 * N) → R) (σ : Blk N) : R := ∑ p, iX R σ p * w p

/-- `b_Y(J) = w₀ + ∑_p J_p w_p`. -/
def hashY (w₀ : R) (w : Fin (3 * N) → R) (σ : Blk N) : R := w₀ + ∑ p, iY R σ p * w p

/-! ## From Mathlib's Salem–Spencer sets over `ℕ` to `ZMod (2 M₀ + 1)` -/

/-- **CW90, remark (4).**  A 3AP-free set of naturals below `M₀` stays free of three-term
progressions in `ZMod (2 * M₀ + 1)`, because no wrap-around can occur. -/
theorem apFree_zmod_image {M₀ : ℕ} (B₀ : Finset ℕ) (hlt : ∀ x ∈ B₀, x < M₀)
    (hB₀ : ThreeAPFree (B₀ : Set ℕ)) :
    ∀ a ∈ (B₀.image (fun x : ℕ => (x : ZMod (2 * M₀ + 1))) : Set (ZMod (2 * M₀ + 1))),
    ∀ b ∈ (B₀.image (fun x : ℕ => (x : ZMod (2 * M₀ + 1))) : Set (ZMod (2 * M₀ + 1))),
    ∀ c ∈ (B₀.image (fun x : ℕ => (x : ZMod (2 * M₀ + 1))) : Set (ZMod (2 * M₀ + 1))),
    a + b = 2 * c → a = b ∧ b = c := by
  intro a ha b hb c hc hap
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb hc
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  obtain ⟨z, hz, rfl⟩ := hc
  have hxlt := hlt x hx
  have hylt := hlt y hy
  have hzlt := hlt z hz
  -- the progression holds already in `ℕ`, since both sides are `< 2 M₀ + 1`
  have hnat : x + y = 2 * z := by
    have hcast : ((x + y : ℕ) : ZMod (2 * M₀ + 1)) = ((2 * z : ℕ) : ZMod (2 * M₀ + 1)) := by
      push_cast
      exact hap
    have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  have hxz : x = z := hB₀ hx hz hy (by omega)
  have hyz : y = z := by omega
  exact ⟨by rw [hxz, hyz], by rw [hyz]⟩

/-- **A Salem–Spencer set in `ZMod (2 M₀ + 1)` of size `rothNumberNat M₀`.**

The size bound is Behrend's, imported from Mathlib
(`Behrend.roth_lower_bound : N * exp (-4 √(log N)) ≤ rothNumberNat N`); it is stated here
as `rothNumberNat M₀` so that the analytic estimate can be applied downstream. -/
theorem exists_apFree_zmod (M₀ : ℕ) :
    ∃ B : Finset (ZMod (2 * M₀ + 1)),
      B.card = rothNumberNat M₀ ∧
      (∀ a ∈ (B : Set (ZMod (2 * M₀ + 1))), ∀ b ∈ (B : Set (ZMod (2 * M₀ + 1))),
        ∀ c ∈ (B : Set (ZMod (2 * M₀ + 1))), a + b = 2 * c → a = b ∧ b = c) := by
  obtain ⟨B₀, hsub, hcard, hfree⟩ := rothNumberNat_spec M₀
  have hlt : ∀ x ∈ B₀, x < M₀ := fun x hx => Finset.mem_range.mp (hsub hx)
  refine ⟨B₀.image (fun x : ℕ => (x : ZMod (2 * M₀ + 1))), ?_,
    apFree_zmod_image B₀ hlt hfree⟩
  rw [Finset.card_image_of_injOn, hcard]
  intro x hx y hy hxy
  have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hxy
  rwa [Nat.mod_eq_of_lt (by have := hlt x hx; omega),
    Nat.mod_eq_of_lt (by have := hlt y hy; omega)] at h

/-- Behrend's lower bound, restated for the modulus that the hash uses. -/
theorem card_apFree_zmod_lower (M₀ : ℕ) :
    (M₀ : ℝ) * Real.exp (-4 * Real.sqrt (Real.log M₀)) ≤ rothNumberNat M₀ :=
  Behrend.roth_lower_bound

end CW90

end OmegaBound
