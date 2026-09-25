import OmegaBound.ADVXXZG1Laws

/-!
# G1, part 4: the exact released parent marginal of every regional table

The released global data carries, besides the `6 * 3 * 45` per-node residual tables
`splres^{(r)}_{W,i,j,k}`, six pairs of **aggregate rows** `avgY`, `avgZ`, indexed by region and by
one level `l ∈ {0, …, 2 * 4}`.  These are ADVXXZ's `splresavg`:

```text
  splresavg_{Y,*,j,*} = (1 / α(*,j,*)) · Σ_{i+k = 2^ℓ - j} α(i,j,k) · splres_{Y,i,j,k}
  splresavg_{Z,*,*,k} = (1 / α(*,*,k)) · Σ_{i+j = 2^ℓ - k} α(i,j,k) · splres_{Z,i,j,k}
```

(`global.tex`, the notation table; the entropies `H(splavg_Y)`, `H(splavg_Z)` of
`prop:global-stage-no-eps` are taken against exactly these rows.)  This is the **parent marginal**
of a regional family: the mixture, at the parent's own level, of all the node tables that sit
above that level, weighted by the region's own shape simplex `α^{(r)}`.

This module builds that mixture over `ℕ` and states it cross-multiplied against the released
rational row, with no rational formed inside the kernel check; the modules
`ADVXXZGeneralReleasedRetainedGlobalParentK0`–`K5` decide it, and `prob_parent_mixture` reads the kernel result back as the
rational identity above.

## The role permutation is load-bearing

`prop:global-stage-no-eps` writes `E_r` with the permutation `π_r` **inside** the marginal:
`H(α^{(r)}_{π_r(X)})`, `H(splavg_{π_r(Y)}^{(r)})`, `H(splavg_{π_r(Z)}^{(r)})`.  Concretely, in the
released data the residual tables `res{X,Y,Z}` are indexed by the logical paper-role triple
`(i, j, k)`, while the certificate's regional shape simplex
`ADVXXZCertificateGlobalData.Certificate.shapeDist r` is indexed in **physical MATLAB dimension
order** — the order of `ADVXXZCertRegionalSemantic.physicalSide`.  Reading `α^{(r)}` at the
logical row is therefore wrong for every `r ≠ 0`, and `physRow` is the transport that repairs it.
-/

set_option maxHeartbeats 1000000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZG1

open ADVXXZ (Chunk SplitDist)
open ADVXXZHash (Pat Ix Jy Kz)
open ADVXXZPaper (Side Shape)
open ADVXXZRA (regionalSplit)
open ADVXXZCertRegionalSemantic (shapeIndex shapeOffset physicalSide)

/-! ## §1  The regional families, addressed by released row index -/

/-- Region `r`'s own residual tables, addressed by the released row index rather than by the
level triple. -/
def betaIdx (r : Fin 6) (S : Side) (n : Fin 45) : SplitDist 4 :=
  match (r : ℕ) with
  | 0 => ADVXXZRegionalCertificateSplitData.certificateSplitByIndex S n
  | 1 => ADVXXZR1CertificateSplitData.certificateSplitByIndex S n
  | 2 => ADVXXZR2CertificateSplitData.certificateSplitByIndex S n
  | 3 => ADVXXZR3CertificateSplitData.certificateSplitByIndex S n
  | 4 => ADVXXZR4CertificateSplitData.certificateSplitByIndex S n
  | _ => ADVXXZR5CertificateSplitData.certificateSplitByIndex S n

/-- The row-indexed family is literally `ADVXXZRA.regionalSplit`. -/
theorem betaIdx_shapeIndex (r : Fin 6) (S : Side) (u : Pat (2 * 4)) :
    betaIdx r S (shapeIndex u) = regionalSplit r S u := by
  fin_cases r <;> rfl

/-- The level triple carried by a released row index. -/
def rowShape (n : Fin 45) : ℕ × ℕ × ℕ :=
  match (n : ℕ) with
  | 0 => (0, 0, 8) | 1 => (0, 1, 7) | 2 => (0, 2, 6) | 3 => (0, 3, 5) | 4 => (0, 4, 4)
  | 5 => (0, 5, 3) | 6 => (0, 6, 2) | 7 => (0, 7, 1) | 8 => (0, 8, 0)
  | 9 => (1, 0, 7) | 10 => (1, 1, 6) | 11 => (1, 2, 5) | 12 => (1, 3, 4) | 13 => (1, 4, 3)
  | 14 => (1, 5, 2) | 15 => (1, 6, 1) | 16 => (1, 7, 0)
  | 17 => (2, 0, 6) | 18 => (2, 1, 5) | 19 => (2, 2, 4) | 20 => (2, 3, 3) | 21 => (2, 4, 2)
  | 22 => (2, 5, 1) | 23 => (2, 6, 0)
  | 24 => (3, 0, 5) | 25 => (3, 1, 4) | 26 => (3, 2, 3) | 27 => (3, 3, 2) | 28 => (3, 4, 1)
  | 29 => (3, 5, 0)
  | 30 => (4, 0, 4) | 31 => (4, 1, 3) | 32 => (4, 2, 2) | 33 => (4, 3, 1) | 34 => (4, 4, 0)
  | 35 => (5, 0, 3) | 36 => (5, 1, 2) | 37 => (5, 2, 1) | 38 => (5, 3, 0)
  | 39 => (6, 0, 2) | 40 => (6, 1, 1) | 41 => (6, 2, 0)
  | 42 => (7, 0, 1) | 43 => (7, 1, 0)
  | _ => (8, 0, 0)

/-- **THE ROW INDEX CARRIES THE NODE.**  The released row index of a level-3 node determines,
and is determined by, that node's level triple. -/
theorem rowShape_shapeIndex : ∀ u : Pat (2 * 4),
    rowShape (shapeIndex u) = ((Ix u).val, (Jy u).val, (Kz u).val) := by
  native_decide

/-- The coordinate a side reads off a level triple. -/
def coordAt (t : ℕ × ℕ × ℕ) : Side → ℕ
  | .X => t.1
  | .Y => t.2.1
  | .Z => t.2.2

/-- The level at which leg `S`'s table of the released row `n` must live. -/
def rowLvl (S : Side) (n : Fin 45) : ℕ := coordAt (rowShape n) S

theorem rowLvl_shapeIndex (S : Side) (u : Pat (2 * 4)) :
    rowLvl S (shapeIndex u) = lvlOf S u := by
  have h := rowShape_shapeIndex u
  cases S <;> simp only [rowLvl, coordAt, h, lvlOf]

/-! ## §2  The regional shape simplex and the role permutation -/

/-- The certificate's own regional shape simplex numerator, addressed by row index. -/
def alphaIdx (r : Fin 6) (n : Fin 45) : ℕ :=
  (ADVXXZCertSemantic.globalSpec
    (ADVXXZCertificateGlobalData.Certificate.shapeId r)).nums.getD n.val 0

/-- **THE WEIGHT IS THE CERTIFICATE'S OWN REGIONAL SHAPE SIMPLEX.** -/
theorem alphaIdx_eq_shapeDist (r : Fin 6) : ∀ u : Pat (2 * 4),
    alphaIdx r (shapeIndex u) = (ADVXXZCertificateGlobalData.Certificate.shapeDist r).num u := by
  fin_cases r <;> decide +kernel

/-- The logical role that region `r` assigns to physical dimension `d`; the inverse of
`ADVXXZCertRegionalSemantic.physicalSide r`. -/
def roleAt (r : Fin 6) (d : Fin 3) : Side :=
  if physicalSide r .X = d then .X else if physicalSide r .Y = d then .Y else .Z

/-- `roleAt r` really inverts `physicalSide r`, so the six regions carry the six role
permutations. -/
theorem roleAt_physicalSide : ∀ (r : Fin 6) (S : Side), roleAt r (physicalSide r S) = S := by
  native_decide

/-- **THE ROLE TRANSPORT.**  `physRow r n` is the row of the certificate's regional shape simplex
that carries the logical node of released row `n`: the simplex is stored in physical dimension
order, the residual tables in logical paper-role order. -/
def physRow (r : Fin 6) (n : Fin 45) : Fin 45 :=
  Fin.ofNat 45
    (shapeOffset (coordAt (rowShape n) (roleAt r 0)) + coordAt (rowShape n) (roleAt r 1))

/-- Region `r`'s shape weight of the logical node at released row `n`. -/
def aw (r : Fin 6) (n : Fin 45) : ℕ := alphaIdx r (physRow r n)

/-- At region zero the role permutation is the identity, so no transport happens. -/
theorem physRow_zero : ∀ n : Fin 45, physRow 0 n = n := by native_decide

/-! ## §3  The parent mixture -/

/-- The released rows sitting above level `l` on leg `S`. -/
def grp (S : Side) (l : Fin (2 * 4 + 1)) : Finset (Fin 45) :=
  Finset.univ.filter fun n => rowLvl S n = l.val

/-- `α^{(r)}(*, l, *)` — the total shape weight of that level. -/
def Atot (r : Fin 6) (S : Side) (l : Fin (2 * 4 + 1)) : ℕ := ∑ n ∈ grp S l, aw r n

/-- A common denominator for the mixture: the product of the group's own denominators. -/
def Dprod (r : Fin 6) (S : Side) (l : Fin (2 * 4 + 1)) : ℕ := ∏ n ∈ grp S l, (betaIdx r S n).den

/-- The mixture numerator over that common denominator. -/
def MixNum (r : Fin 6) (S : Side) (l : Fin (2 * 4 + 1)) (c : Chunk 4) : ℕ :=
  ∑ n ∈ grp S l, aw r n * (betaIdx r S n).num c * (Dprod r S l / (betaIdx r S n).den)

/-- **THE PARENT-MARGINAL CLAUSE** at one released `(region, level, word)` slot, cross-multiplied
so that the kernel never forms a rational. -/
def ParentOK (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4) : Prop :=
  (avg r l c).num * ((Atot r S l : ℤ) * (Dprod r S l : ℤ))
    = (MixNum r S l c : ℤ) * ((avg r l c).den : ℤ)

instance instDecParentOK (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4) : Decidable (ParentOK avg S r l c) := by
  unfold ParentOK; infer_instance

/-- Every level group carries positive shape mass, so the mixture is never `0/0`. -/
theorem Atot_pos : ∀ (r : Fin 6) (S : Side) (l : Fin (2 * 4 + 1)), 0 < Atot r S l := by
  native_decide

theorem Dprod_pos (r : Fin 6) (S : Side) (l : Fin (2 * 4 + 1)) : 0 < Dprod r S l :=
  Finset.prod_pos fun n _ => (betaIdx r S n).den_pos

/-! ## §4  Reading the kernel result back as the paper's identity -/

private theorem eq_div_of_cross {q : ℚ} {A M : ℕ} (hA : 0 < A)
    (h : q.num * (A : ℤ) = (M : ℤ) * ((q.den : ℤ))) : q = (M : ℚ) / (A : ℚ) := by
  have hA' : ((A : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hd : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos q).ne'
  have h' : ((q.num : ℚ)) * (A : ℚ) = (M : ℚ) * (q.den : ℚ) := by exact_mod_cast h
  rw [eq_div_iff hA']
  calc q * (A : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * (A : ℚ) := by rw [Rat.num_div_den]
    _ = ((q.num : ℚ) * (A : ℚ)) / (q.den : ℚ) := by ring
    _ = ((M : ℚ) * (q.den : ℚ)) / (q.den : ℚ) := by rw [h']
    _ = (M : ℚ) := by field_simp

/-- **THE PARENT MARGINAL, AS THE PAPER WRITES IT.**  Given the kernel-decided cross-multiplied
clause, the released aggregate row is exactly the `α^{(r)}`-weighted mixture of the regional
node tables at that level. -/
theorem prob_parent_mixture (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4) (h : ParentOK avg S r l c) :
    avg r l c
      = (∑ n ∈ grp S l, (aw r n : ℚ) * (betaIdx r S n).prob c) / (Atot r S l : ℚ) := by
  classical
  have hA : 0 < Atot r S l := Atot_pos r S l
  have hD : 0 < Dprod r S l := Dprod_pos r S l
  have hA' : ((Atot r S l : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hD' : ((Dprod r S l : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  -- the mixture numerator is `Dprod` times the rational mixture
  have hkey : ((MixNum r S l c : ℕ) : ℚ)
      = (Dprod r S l : ℚ) * ∑ n ∈ grp S l, (aw r n : ℚ) * (betaIdx r S n).prob c := by
    simp only [MixNum]
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hdvd : (betaIdx r S n).den ∣ Dprod r S l :=
      Finset.dvd_prod_of_mem (fun m => (betaIdx r S m).den) hn
    have hden : (((betaIdx r S n).den : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (betaIdx r S n).den_pos.ne'
    have hcast : ((Dprod r S l / (betaIdx r S n).den : ℕ) : ℚ)
        = (Dprod r S l : ℚ) / ((betaIdx r S n).den : ℚ) := Nat.cast_div hdvd hden
    rw [Nat.cast_mul, Nat.cast_mul, hcast]
    simp only [ADVXXZ.RatDist.prob]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hcross : (avg r l c).num * ((Atot r S l * Dprod r S l : ℕ) : ℤ)
      = (MixNum r S l c : ℤ) * ((avg r l c).den : ℤ) := by
    rw [Nat.cast_mul]; exact h
  have hq := eq_div_of_cross (Nat.mul_pos hA hD) hcross
  have hlast : (Dprod r S l : ℚ) * (∑ n ∈ grp S l, (aw r n : ℚ) * (betaIdx r S n).prob c)
        / ((Atot r S l : ℚ) * (Dprod r S l : ℚ))
      = (∑ n ∈ grp S l, (aw r n : ℚ) * (betaIdx r S n).prob c) / (Atot r S l : ℚ) := by
    rw [div_eq_div_iff (mul_ne_zero hA' hD') hA']
    ring
  rw [hq, Nat.cast_mul, hkey, hlast]

end ADVXXZG1
end OmegaBound
