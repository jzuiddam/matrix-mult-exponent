import OmegaBound.ADVXXZHashPat
import OmegaBound.CW90Hash
import Mathlib.Data.List.GetD
import Mathlib.NumberTheory.Bertrand

/-!
# ADVXXZ / DWZ hashing, level `ℓ`: the prime modulus

`exists_prime_modulus` is Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`, as the
sources use it) in the shape `M = 2k+1` that `CW90.exists_apFree_zmod` consumes: for `2 ≤ L`
there is an odd prime exceeding both `L` and `2P`, and at most twice their maximum.  It supplies
the hashing modulus of ADVXXZ (`global.tex:180-200`) and DWZ (`hashing.tex:29-58`).
-/

open Finset

namespace OmegaBound

namespace ADVXXZHash


/-! ## The modulus -/

/-- **Bertrand, in the form the Salem–Spencer construction consumes.**  For `2 ≤ L` there is
an odd prime `2k+1` exceeding both `L` and `2P`, and at most twice their maximum.  Oddness
is automatic: the prime exceeds `L ≥ 2`. -/
theorem exists_prime_modulus (L P : ℕ) (hL : 2 ≤ L) :
    ∃ k : ℕ, Nat.Prime (2 * k + 1) ∧ L < 2 * k + 1 ∧ 2 * P ≤ 2 * k + 1 ∧
      2 * k + 1 ≤ 2 * max L (2 * P) := by
  have hL' : L ≤ max L (2 * P) := le_max_left _ _
  have hP' : 2 * P ≤ max L (2 * P) := le_max_right _ _
  have hn0 : max L (2 * P) ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (max L (2 * P)) hn0
  have hne2 : p ≠ 2 := by omega
  have hmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne2)
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  exact ⟨k, hp, by omega, by omega, by omega⟩

variable {L : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

end ADVXXZHash

end OmegaBound
