import OmegaBound.ADVXXZGeneralInputSelfMoment

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def selfFall (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => (x - r) * selfFall x r

private theorem self_cast_descFactorial (x r : ℕ) :
    (x.descFactorial r : ℝ) = selfFall x r := by
  induction r with
  | zero => simp [selfFall]
  | succ r ih =>
      rw [Nat.descFactorial_succ, Nat.cast_mul, selfFall, ih]
      by_cases hrx : r ≤ x
      · rw [Nat.cast_sub hrx]
      · have hz : x.descFactorial r = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hrx)
        have hfall : selfFall x r = 0 := by
          rw [← ih, hz]
          norm_num
        rw [hfall]
        ring

private def selfMomentFromFactorials (F : ℕ → ℝ) : ℝ :=
  (F 4 + 6*F 3 + 7*F 2 + F 1) -
    4*(F 1)*(F 3 + 3*F 2 + F 1) +
    6*(F 1)^2*(F 2 + F 1) - 4*(F 1)^3*(F 1) + (F 1)^4

private noncomputable def selfSameMoment (N S A : ℝ) : ℝ :=
  selfMomentFromFactorials fun r =>
    selfFall S r * selfFall A (2*r) / selfFall N (2*r)

private noncomputable def selfDistinctMoment (N S A B : ℝ) : ℝ :=
  selfMomentFromFactorials fun r =>
    selfFall S r * (selfFall A r * selfFall B r) / selfFall N (2*r)

private def selfMomentNumerator (N u1 u2 u3 u4 : ℝ) : ℝ :=
  let d2 := selfFall N 2
  let d8 := selfFall N 8
  let c6 := (N-6)*(N-7)
  let c4 := (N-4)*(N-5)*(N-6)*(N-7)
  let c2 := (N-2)*(N-3)*(N-4)*(N-5)*(N-6)*(N-7)
  u4*d2^3 + 6*u3*c6*d2^3 + 7*u2*c4*d2^3 + u1*c2*d2^3 -
    4*u1*u3*c6*d2^2 - 12*u1*u2*c4*d2^2 - 4*u1^2*d8*d2 +
    6*u1^2*u2*c4*d2 + 6*u1^3*d8 - 3*u1^4*c2

private def selfSameNumerator (N S A : ℝ) : ℝ :=
  selfMomentNumerator N
    (selfFall S 1 * selfFall A 2)
    (selfFall S 2 * selfFall A 4)
    (selfFall S 3 * selfFall A 6)
    (selfFall S 4 * selfFall A 8)

private def selfDistinctNumerator (N S A B : ℝ) : ℝ :=
  selfMomentNumerator N
    (selfFall S 1 * (selfFall A 1 * selfFall B 1))
    (selfFall S 2 * (selfFall A 2 * selfFall B 2))
    (selfFall S 3 * (selfFall A 3 * selfFall B 3))
    (selfFall S 4 * (selfFall A 4 * selfFall B 4))

private def selfMomentDenominator (N : ℝ) : ℝ :=
  selfFall N 8 * (selfFall N 2)^3

private theorem self_monomial_nonneg (N S A B : ℝ)
    (hN0 : 0 ≤ N) (hS0 : 0 ≤ S) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (i j k l : ℕ) : 0 ≤ N^i*S^j*A^k*B^l := by
  positivity

private theorem self_monomial_le_pow_sixteen (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N)
    (i j k l : ℕ) (hdeg : i + j + k + l ≤ 16) :
    N^i*S^j*A^k*B^l ≤ N^16 := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN1
  calc
    N^i*S^j*A^k*B^l ≤ N^i*N^j*N^k*N^l := by
      gcongr
    _ = N^(i+j+k+l) := by ring
    _ ≤ N^16 := pow_le_pow_right₀ hN1 hdeg

-- SELF-CHUNKS
private def selfSameChunk0 (N S A B : ℝ) : ℝ :=
  1*N^12*S^1*A^2*B^0
    - 1*N^12*S^1*A^1*B^0
    - 30*N^11*S^1*A^2*B^0
    + 30*N^11*S^1*A^1*B^0
    + 3*N^10*S^2*A^4*B^0
    - 34*N^10*S^2*A^3*B^0
    + 73*N^10*S^2*A^2*B^0
    - 42*N^10*S^2*A^1*B^0
    - 7*N^10*S^1*A^4*B^0
    + 42*N^10*S^1*A^3*B^0
    + 302*N^10*S^1*A^2*B^0
    - 337*N^10*S^1*A^1*B^0
    - 59*N^9*S^2*A^4*B^0
    + 818*N^9*S^2*A^3*B^0
    - 1809*N^9*S^2*A^2*B^0
    + 1050*N^9*S^2*A^1*B^0
    + 175*N^9*S^1*A^4*B^0
    - 1050*N^9*S^1*A^3*B^0

private theorem selfSameChunk0_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk0 N S A B ≤ 2494*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk0
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 12 1 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 12 1 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 11 1 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 11 1 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 2 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 2 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 2 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 2 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 1 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 1 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 1 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 1 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 2 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 2 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 2 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 2 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 1 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 1 3 0]

private def selfSameChunk1 (N S A B : ℝ) : ℝ :=
  -707*N^9*S^1*A^2*B^0
    + 1582*N^9*S^1*A^1*B^0
    - 24*N^8*S^3*A^5*B^0
    + 324*N^8*S^3*A^4*B^0
    - 1152*N^8*S^3*A^3*B^0
    + 1572*N^8*S^3*A^2*B^0
    - 720*N^8*S^3*A^1*B^0
    - 6*N^8*S^2*A^6*B^0
    + 186*N^8*S^2*A^5*B^0
    - 990*N^8*S^2*A^4*B^0
    - 3770*N^8*S^2*A^3*B^0
    + 12836*N^8*S^2*A^2*B^0
    - 8256*N^8*S^2*A^1*B^0
    + 12*N^8*S^1*A^6*B^0
    - 180*N^8*S^1*A^5*B^0
    - 716*N^8*S^1*A^4*B^0
    + 7716*N^8*S^1*A^3*B^0
    - 4797*N^8*S^1*A^2*B^0

private theorem selfSameChunk1_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk1 N S A B ≤ 24228*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk1
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 1 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 1 1 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 4 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 1 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 5 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 2 0]

private def selfSameChunk2 (N S A B : ℝ) : ℝ :=
  -2035*N^8*S^1*A^1*B^0
    + 24*N^7*S^3*A^6*B^0
    - 72*N^7*S^3*A^5*B^0
    - 3768*N^7*S^3*A^4*B^0
    + 16872*N^7*S^3*A^3*B^0
    - 24576*N^7*S^3*A^2*B^0
    + 11520*N^7*S^3*A^1*B^0
    - 2304*N^7*S^2*A^5*B^0
    + 20018*N^7*S^2*A^4*B^0
    - 25996*N^7*S^2*A^3*B^0
    - 9322*N^7*S^2*A^2*B^0
    + 17604*N^7*S^2*A^1*B^0
    - 192*N^7*S^1*A^6*B^0
    + 2880*N^7*S^1*A^5*B^0
    - 7626*N^7*S^1*A^4*B^0
    - 8964*N^7*S^1*A^3*B^0
    + 14396*N^7*S^1*A^2*B^0
    - 494*N^7*S^1*A^1*B^0

private theorem selfSameChunk2_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk2 N S A B ≤ 83314*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk2
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 1 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 5 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 1 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 3 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 1 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 1 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 4 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 1 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 1 0]

private def selfSameChunk3 (N S A B : ℝ) : ℝ :=
  48*N^6*S^4*A^6*B^0
    - 912*N^6*S^4*A^5*B^0
    + 4908*N^6*S^4*A^4*B^0
    - 11592*N^6*S^4*A^3*B^0
    + 12588*N^6*S^4*A^2*B^0
    - 5040*N^6*S^4*A^1*B^0
    + 24*N^6*S^3*A^7*B^0
    - 1128*N^6*S^3*A^6*B^0
    + 13704*N^6*S^3*A^5*B^0
    - 31824*N^6*S^3*A^4*B^0
    + 4464*N^6*S^3*A^3*B^0
    + 45000*N^6*S^3*A^2*B^0
    - 30240*N^6*S^3*A^1*B^0
    + 3*N^6*S^2*A^8*B^0
    - 180*N^6*S^2*A^7*B^0
    + 3918*N^6*S^2*A^6*B^0
    - 15216*N^6*S^2*A^5*B^0
    - 24082*N^6*S^2*A^4*B^0

private theorem selfSameChunk3_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk3 N S A B ≤ 84657*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk3
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 1 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 1 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 5 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 4 0]

private def selfSameChunk4 (N S A B : ℝ) : ℝ :=
  83890*N^6*S^2*A^3*B^0
    - 35187*N^6*S^2*A^2*B^0
    - 13146*N^6*S^2*A^1*B^0
    - 6*N^6*S^1*A^8*B^0
    + 168*N^6*S^1*A^7*B^0
    - 924*N^6*S^1*A^6*B^0
    - 3360*N^6*S^1*A^5*B^0
    + 21875*N^6*S^1*A^4*B^0
    - 8862*N^6*S^1*A^3*B^0
    - 11216*N^6*S^1*A^2*B^0
    + 2325*N^6*S^1*A^1*B^0
    - 96*N^5*S^4*A^7*B^0
    + 2208*N^5*S^4*A^6*B^0
    - 8352*N^5*S^4*A^5*B^0
    + 6540*N^5*S^4*A^4*B^0
    + 16584*N^5*S^4*A^3*B^0
    - 32004*N^5*S^4*A^2*B^0
    + 15120*N^5*S^4*A^1*B^0

private theorem selfSameChunk4_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk4 N S A B ≤ 148710*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk4
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 2 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 6 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 3 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 1 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 4 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 1 0 (by norm_num)]

private def selfSameChunk5 (N S A B : ℝ) : ℝ :=
  -24*N^5*S^3*A^8*B^0
    + 1272*N^5*S^3*A^7*B^0
    - 9432*N^5*S^3*A^6*B^0
    - 19464*N^5*S^3*A^5*B^0
    + 122928*N^5*S^3*A^4*B^0
    - 138096*N^5*S^3*A^3*B^0
    + 14016*N^5*S^3*A^2*B^0
    + 28800*N^5*S^3*A^1*B^0
    + 87*N^5*S^2*A^8*B^0
    - 996*N^5*S^2*A^7*B^0
    - 7854*N^5*S^2*A^6*B^0
    + 68172*N^5*S^2*A^5*B^0
    - 69876*N^5*S^2*A^4*B^0
    - 44014*N^5*S^2*A^3*B^0
    + 52975*N^5*S^2*A^2*B^0
    + 1506*N^5*S^2*A^1*B^0
    + 18*N^5*S^1*A^8*B^0
    - 504*N^5*S^1*A^7*B^0

private theorem selfSameChunk5_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk5 N S A B ≤ 289774*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk5
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 6 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 2 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 7 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 4 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 2 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 7 0]

private def selfSameChunk6 (N S A B : ℝ) : ℝ :=
  3804*N^5*S^1*A^6*B^0
    - 5400*N^5*S^1*A^5*B^0
    - 15187*N^5*S^1*A^4*B^0
    + 18078*N^5*S^1*A^3*B^0
    + 309*N^5*S^1*A^2*B^0
    - 1118*N^5*S^1*A^1*B^0
    + 48*N^4*S^4*A^8*B^0
    - 1776*N^4*S^4*A^7*B^0
    - 3000*N^4*S^4*A^6*B^0
    + 42216*N^4*S^4*A^5*B^0
    - 90564*N^4*S^4*A^4*B^0
    + 62112*N^4*S^4*A^3*B^0
    + 6084*N^4*S^4*A^2*B^0
    - 15120*N^4*S^4*A^1*B^0
    - 396*N^4*S^3*A^8*B^0
    - 3096*N^4*S^3*A^7*B^0
    + 61968*N^4*S^3*A^6*B^0
    - 121968*N^4*S^3*A^5*B^0

private theorem selfSameChunk6_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk6 N S A B ≤ 194619*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk6
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 5 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 1 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 7 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 2 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 8 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 5 0]

private def selfSameChunk7 (N S A B : ℝ) : ℝ :=
  -11856*N^4*S^3*A^4*B^0
    + 157296*N^4*S^3*A^3*B^0
    - 72588*N^4*S^3*A^2*B^0
    - 9360*N^4*S^3*A^1*B^0
    - 519*N^4*S^2*A^8*B^0
    + 7908*N^4*S^2*A^7*B^0
    - 19536*N^4*S^2*A^6*B^0
    - 48810*N^4*S^2*A^5*B^0
    + 120745*N^4*S^2*A^4*B^0
    - 44134*N^4*S^2*A^3*B^0
    - 16938*N^4*S^2*A^2*B^0
    + 1284*N^4*S^2*A^1*B^0
    - 18*N^4*S^1*A^8*B^0
    + 504*N^4*S^1*A^7*B^0
    - 4128*N^4*S^1*A^6*B^0
    + 10260*N^4*S^1*A^5*B^0
    - 2168*N^4*S^1*A^4*B^0
    - 6288*N^4*S^1*A^3*B^0

private theorem selfSameChunk7_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk7 N S A B ≤ 297997*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk7
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 2 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 1 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 6 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 3 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 1 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 4 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 3 0]

private def selfSameChunk8 (N S A B : ℝ) : ℝ :=
  1790*N^4*S^1*A^2*B^0
    + 48*N^4*S^1*A^1*B^0
    + 480*N^3*S^4*A^8*B^0
    + 13056*N^3*S^4*A^7*B^0
    - 49200*N^3*S^4*A^6*B^0
    + 28368*N^3*S^4*A^5*B^0
    + 79092*N^3*S^4*A^4*B^0
    - 110328*N^3*S^4*A^3*B^0
    + 33492*N^3*S^4*A^2*B^0
    + 5040*N^3*S^4*A^1*B^0
    + 3744*N^3*S^3*A^8*B^0
    - 20760*N^3*S^3*A^7*B^0
    - 48048*N^3*S^3*A^6*B^0
    + 227856*N^3*S^3*A^5*B^0
    - 212400*N^3*S^3*A^4*B^0
    + 13032*N^3*S^3*A^3*B^0
    + 36576*N^3*S^3*A^2*B^0
    + 765*N^3*S^2*A^8*B^0

private theorem selfSameChunk8_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk8 N S A B ≤ 443339*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk8
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 2 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 8 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 5 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 3 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 2 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 1 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 7 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 2 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 8 0 (by norm_num)]

private def selfSameChunk9 (N S A B : ℝ) : ℝ :=
  -12108*N^3*S^2*A^7*B^0
    + 46998*N^3*S^2*A^6*B^0
    - 35628*N^3*S^2*A^5*B^0
    - 29295*N^3*S^2*A^4*B^0
    + 31896*N^3*S^2*A^3*B^0
    - 2628*N^3*S^2*A^2*B^0
    + 6*N^3*S^1*A^8*B^0
    - 168*N^3*S^1*A^7*B^0
    + 1428*N^3*S^1*A^6*B^0
    - 4200*N^3*S^1*A^5*B^0
    + 3654*N^3*S^1*A^4*B^0
    - 672*N^3*S^1*A^3*B^0
    - 48*N^3*S^1*A^2*B^0
    - 6612*N^2*S^4*A^8*B^0
    - 7008*N^2*S^4*A^7*B^0
    + 104160*N^2*S^4*A^6*B^0
    - 188184*N^2*S^4*A^5*B^0
    + 104820*N^2*S^4*A^4*B^0

private theorem selfSameChunk9_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk9 N S A B ≤ 292962*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk9
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 5 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 2 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 3 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 2 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 8 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 4 0 (by norm_num)]

private def selfSameChunk10 (N S A B : ℝ) : ℝ :=
  12984*N^2*S^4*A^3*B^0
    - 20160*N^2*S^4*A^2*B^0
    - 8364*N^2*S^3*A^8*B^0
    + 62880*N^2*S^3*A^7*B^0
    - 94104*N^2*S^3*A^6*B^0
    - 19392*N^2*S^3*A^5*B^0
    + 111396*N^2*S^3*A^4*B^0
    - 52416*N^2*S^3*A^3*B^0
    - 336*N^2*S^2*A^8*B^0
    + 5376*N^2*S^2*A^7*B^0
    - 23520*N^2*S^2*A^6*B^0
    + 33600*N^2*S^2*A^5*B^0
    - 16464*N^2*S^2*A^4*B^0
    + 1344*N^2*S^2*A^3*B^0
    + 19044*N^1*S^4*A^8*B^0
    - 56016*N^1*S^4*A^7*B^0
    + 23544*N^1*S^4*A^6*B^0
    + 75024*N^1*S^4*A^5*B^0

private theorem selfSameChunk10_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk10 N S A B ≤ 345192*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk10
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 3 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 2 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 6 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 3 0,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 4 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 6 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 5 0 (by norm_num)]

private def selfSameChunk11 (N S A B : ℝ) : ℝ :=
  -91836*N^1*S^4*A^4*B^0
    + 30240*N^1*S^4*A^3*B^0
    + 5040*N^1*S^3*A^8*B^0
    - 40320*N^1*S^3*A^7*B^0
    + 90720*N^1*S^3*A^6*B^0
    - 80640*N^1*S^3*A^5*B^0
    + 25200*N^1*S^3*A^4*B^0
    - 15120*N^0*S^4*A^8*B^0
    + 60480*N^0*S^4*A^7*B^0
    - 90720*N^0*S^4*A^6*B^0
    + 60480*N^0*S^4*A^5*B^0
    - 15120*N^0*S^4*A^4*B^0

private theorem selfSameChunk11_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameChunk11 N S A B ≤ 272160*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfSameChunk11
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 4 4 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 3 0 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 3 8 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 3 7 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 3 6 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 3 5 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 3 4 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 0 4 8 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 0 4 7 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 0 4 6 0,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 0 4 5 0 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 0 4 4 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem selfSameNumerator_eq_chunks (N S A B : ℝ) :
    selfSameNumerator N S A =
        selfSameChunk0 N S A B
      + selfSameChunk1 N S A B
      + selfSameChunk2 N S A B
      + selfSameChunk3 N S A B
      + selfSameChunk4 N S A B
      + selfSameChunk5 N S A B
      + selfSameChunk6 N S A B
      + selfSameChunk7 N S A B
      + selfSameChunk8 N S A B
      + selfSameChunk9 N S A B
      + selfSameChunk10 N S A B
      + selfSameChunk11 N S A B
    := by
  unfold selfSameNumerator selfMomentNumerator
  unfold selfSameChunk0
  unfold selfSameChunk1
  unfold selfSameChunk2
  unfold selfSameChunk3
  unfold selfSameChunk4
  unfold selfSameChunk5
  unfold selfSameChunk6
  unfold selfSameChunk7
  unfold selfSameChunk8
  unfold selfSameChunk9
  unfold selfSameChunk10
  unfold selfSameChunk11
  simp only [selfFall]
  ring

private theorem selfSameNumerator_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfSameNumerator N S A ≤ 2479446*N^16 := by
  rw [selfSameNumerator_eq_chunks N S A B]
  have h0 := selfSameChunk0_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h1 := selfSameChunk1_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h2 := selfSameChunk2_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h3 := selfSameChunk3_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h4 := selfSameChunk4_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h5 := selfSameChunk5_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h6 := selfSameChunk6_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h7 := selfSameChunk7_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h8 := selfSameChunk8_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h9 := selfSameChunk9_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h10 := selfSameChunk10_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h11 := selfSameChunk11_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

private def selfDistinctChunk0 (N S A B : ℝ) : ℝ :=
  1*N^12*S^1*A^1*B^1
    - 30*N^11*S^1*A^1*B^1
    + 3*N^10*S^2*A^2*B^2
    - 7*N^10*S^2*A^2*B^1
    - 7*N^10*S^2*A^1*B^2
    + 7*N^10*S^2*A^1*B^1
    - 7*N^10*S^1*A^2*B^2
    + 7*N^10*S^1*A^2*B^1
    + 7*N^10*S^1*A^1*B^2
    + 372*N^10*S^1*A^1*B^1
    - 59*N^9*S^2*A^2*B^2
    + 175*N^9*S^2*A^2*B^1
    + 175*N^9*S^2*A^1*B^2
    - 175*N^9*S^2*A^1*B^1
    + 175*N^9*S^1*A^2*B^2
    - 175*N^9*S^1*A^2*B^1
    - 175*N^9*S^1*A^1*B^2
    - 2457*N^9*S^1*A^1*B^1

private theorem selfDistinctChunk0_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk0 N S A B ≤ 922*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk0
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 12 1 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 11 1 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 2 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 2 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 2 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 2 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 10 1 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 1 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 1 1 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 10 1 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 2 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 2 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 2 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 2 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 9 1 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 1 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 1 1 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 9 1 1 1]

private def selfDistinctChunk1 (N S A B : ℝ) : ℝ :=
  -6*N^8*S^3*A^3*B^2
    + 12*N^8*S^3*A^3*B^1
    - 6*N^8*S^3*A^2*B^3
    + 42*N^8*S^3*A^2*B^2
    - 36*N^8*S^3*A^2*B^1
    + 12*N^8*S^3*A^1*B^3
    - 36*N^8*S^3*A^1*B^2
    + 24*N^8*S^3*A^1*B^1
    - 6*N^8*S^2*A^3*B^3
    + 42*N^8*S^2*A^3*B^2
    - 36*N^8*S^2*A^3*B^1
    + 42*N^8*S^2*A^2*B^3
    + 186*N^8*S^2*A^2*B^2
    - 1628*N^8*S^2*A^2*B^1
    - 36*N^8*S^2*A^1*B^3
    - 1628*N^8*S^2*A^1*B^2
    + 1664*N^8*S^2*A^1*B^1
    + 12*N^8*S^1*A^3*B^3

private theorem selfDistinctChunk1_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk1 N S A B ≤ 2036*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk1
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 3 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 2 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 2 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 1 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 3 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 3 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 2 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 2 1 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 3 3 (by norm_num)]

private def selfDistinctChunk2 (N S A B : ℝ) : ℝ :=
  -36*N^8*S^1*A^3*B^2
    + 24*N^8*S^1*A^3*B^1
    - 36*N^8*S^1*A^2*B^3
    - 1628*N^8*S^1*A^2*B^2
    + 1664*N^8*S^1*A^2*B^1
    + 24*N^8*S^1*A^1*B^3
    + 1664*N^8*S^1*A^1*B^2
    + 9323*N^8*S^1*A^1*B^1
    + 24*N^7*S^3*A^3*B^3
    - 192*N^7*S^3*A^3*B^1
    - 576*N^7*S^3*A^2*B^2
    + 576*N^7*S^3*A^2*B^1
    - 192*N^7*S^3*A^1*B^3
    + 576*N^7*S^3*A^1*B^2
    - 384*N^7*S^3*A^1*B^1
    - 576*N^7*S^2*A^3*B^2
    + 576*N^7*S^2*A^3*B^1
    - 576*N^7*S^2*A^2*B^3

private theorem selfDistinctChunk2_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk2 N S A B ≤ 14451*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk2
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 3 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 8 1 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 1 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 1 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 8 1 1 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 3 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 2 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 1 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 3 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 3 1 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 3 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 2 3]

private def selfDistinctChunk3 (N S A B : ℝ) : ℝ :=
  2738*N^7*S^2*A^2*B^2
    + 6966*N^7*S^2*A^2*B^1
    + 576*N^7*S^2*A^1*B^3
    + 6966*N^7*S^2*A^1*B^2
    - 7542*N^7*S^2*A^1*B^1
    - 192*N^7*S^1*A^3*B^3
    + 576*N^7*S^1*A^3*B^2
    - 384*N^7*S^1*A^3*B^1
    + 576*N^7*S^1*A^2*B^3
    + 6966*N^7*S^1*A^2*B^2
    - 7542*N^7*S^1*A^2*B^1
    - 384*N^7*S^1*A^1*B^3
    - 7542*N^7*S^1*A^1*B^2
    - 20704*N^7*S^1*A^1*B^1
    + 3*N^6*S^4*A^4*B^2
    - 6*N^6*S^4*A^4*B^1
    + 6*N^6*S^4*A^3*B^3
    - 42*N^6*S^4*A^3*B^2

private theorem selfDistinctChunk3_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk3 N S A B ≤ 25373*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk3
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 1 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 2 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 2 1 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 1 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 1 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 7 1 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 1 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 7 1 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 4 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 4 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 3 2]

private def selfDistinctChunk4 (N S A B : ℝ) : ℝ :=
  36*N^6*S^4*A^3*B^1
    + 3*N^6*S^4*A^2*B^4
    - 42*N^6*S^4*A^2*B^3
    + 105*N^6*S^4*A^2*B^2
    - 66*N^6*S^4*A^2*B^1
    - 6*N^6*S^4*A^1*B^4
    + 36*N^6*S^4*A^1*B^3
    - 66*N^6*S^4*A^1*B^2
    + 36*N^6*S^4*A^1*B^1
    + 6*N^6*S^3*A^4*B^3
    - 42*N^6*S^3*A^4*B^2
    + 36*N^6*S^3*A^4*B^1
    + 6*N^6*S^3*A^3*B^4
    - 366*N^6*S^3*A^3*B^3
    + 1500*N^6*S^3*A^3*B^2
    + 792*N^6*S^3*A^3*B^1
    - 42*N^6*S^3*A^2*B^4
    + 1500*N^6*S^3*A^2*B^3

private theorem selfDistinctChunk4_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk4 N S A B ≤ 4056*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk4
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 3 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 2 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 2 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 1 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 1 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 4 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 4 1 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 4 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 4 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 3 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 3 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 2 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 2 3 (by norm_num)]

private def selfDistinctChunk5 (N S A B : ℝ) : ℝ :=
  1170*N^6*S^3*A^2*B^2
    - 2628*N^6*S^3*A^2*B^1
    + 36*N^6*S^3*A^1*B^4
    + 792*N^6*S^3*A^1*B^3
    - 2628*N^6*S^3*A^1*B^2
    + 1800*N^6*S^3*A^1*B^1
    + 3*N^6*S^2*A^4*B^4
    - 42*N^6*S^2*A^4*B^3
    + 105*N^6*S^2*A^4*B^2
    - 66*N^6*S^2*A^4*B^1
    - 42*N^6*S^2*A^3*B^4
    + 1500*N^6*S^2*A^3*B^3
    + 1170*N^6*S^2*A^3*B^2
    - 2628*N^6*S^2*A^3*B^1
    + 105*N^6*S^2*A^2*B^4
    + 1170*N^6*S^2*A^2*B^3
    - 21346*N^6*S^2*A^2*B^2
    - 14845*N^6*S^2*A^2*B^1

private theorem selfDistinctChunk5_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk5 N S A B ≤ 7851*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk5
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 2 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 1 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 1 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 3 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 3 1 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 4 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 4 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 3 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 3 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 2 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 2 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 2 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 2 1]

private def selfDistinctChunk6 (N S A B : ℝ) : ℝ :=
  -66*N^6*S^2*A^1*B^4
    - 2628*N^6*S^2*A^1*B^3
    - 14845*N^6*S^2*A^1*B^2
    + 17539*N^6*S^2*A^1*B^1
    - 6*N^6*S^1*A^4*B^4
    + 36*N^6*S^1*A^4*B^3
    - 66*N^6*S^1*A^4*B^2
    + 36*N^6*S^1*A^4*B^1
    + 36*N^6*S^1*A^3*B^4
    + 792*N^6*S^1*A^3*B^3
    - 2628*N^6*S^1*A^3*B^2
    + 1800*N^6*S^1*A^3*B^1
    - 66*N^6*S^1*A^2*B^4
    - 2628*N^6*S^1*A^2*B^3
    - 14845*N^6*S^1*A^2*B^2
    + 17539*N^6*S^1*A^2*B^1
    + 36*N^6*S^1*A^1*B^4
    + 1800*N^6*S^1*A^1*B^3

private theorem selfDistinctChunk6_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk6 N S A B ≤ 39614*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk6
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 2 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 2 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 4 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 4 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 4 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 3 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 3 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 6 1 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 1 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 1 3 (by norm_num)]

private def selfDistinctChunk7 (N S A B : ℝ) : ℝ :=
  17539*N^6*S^1*A^1*B^2
    + 26726*N^6*S^1*A^1*B^1
    - 24*N^5*S^4*A^4*B^3
    + 87*N^5*S^4*A^4*B^2
    + 18*N^5*S^4*A^4*B^1
    - 24*N^5*S^4*A^3*B^4
    + 294*N^5*S^4*A^3*B^3
    - 162*N^5*S^4*A^3*B^2
    - 108*N^5*S^4*A^3*B^1
    + 87*N^5*S^4*A^2*B^4
    - 162*N^5*S^4*A^2*B^3
    - 123*N^5*S^4*A^2*B^2
    + 198*N^5*S^4*A^2*B^1
    + 18*N^5*S^4*A^1*B^4
    - 108*N^5*S^4*A^1*B^3
    + 198*N^5*S^4*A^1*B^2
    - 108*N^5*S^4*A^1*B^1
    - 24*N^5*S^3*A^4*B^4

private theorem selfDistinctChunk7_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk7 N S A B ≤ 45165*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk7
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 1 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 6 1 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 4 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 4 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 3 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 2 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 1 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 1 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 4 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 4 1 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 4 4]

private def selfDistinctChunk8 (N S A B : ℝ) : ℝ :=
  294*N^5*S^3*A^4*B^3
    - 162*N^5*S^3*A^4*B^2
    - 108*N^5*S^3*A^4*B^1
    + 294*N^5*S^3*A^3*B^4
    - 1374*N^5*S^3*A^3*B^3
    - 9336*N^5*S^3*A^3*B^2
    - 1344*N^5*S^3*A^3*B^1
    - 162*N^5*S^3*A^2*B^4
    - 9336*N^5*S^3*A^2*B^3
    + 4710*N^5*S^3*A^2*B^2
    + 4788*N^5*S^3*A^2*B^1
    - 108*N^5*S^3*A^1*B^4
    - 1344*N^5*S^3*A^1*B^3
    + 4788*N^5*S^3*A^1*B^2
    - 3336*N^5*S^3*A^1*B^1
    + 87*N^5*S^2*A^4*B^4
    - 162*N^5*S^2*A^4*B^3
    - 123*N^5*S^2*A^4*B^2

private theorem selfDistinctChunk8_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk8 N S A B ≤ 14961*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk8
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 4 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 4 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 3 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 3 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 3 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 2 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 2 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 1 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 3 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 3 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 4 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 4 2]

private def selfDistinctChunk9 (N S A B : ℝ) : ℝ :=
  198*N^5*S^2*A^4*B^1
    - 162*N^5*S^2*A^3*B^4
    - 9336*N^5*S^2*A^3*B^3
    + 4710*N^5*S^2*A^3*B^2
    + 4788*N^5*S^2*A^3*B^1
    - 123*N^5*S^2*A^2*B^4
    + 4710*N^5*S^2*A^2*B^3
    + 58476*N^5*S^2*A^2*B^2
    + 16541*N^5*S^2*A^2*B^1
    + 198*N^5*S^2*A^1*B^4
    + 4788*N^5*S^2*A^1*B^3
    + 16541*N^5*S^2*A^1*B^2
    - 21527*N^5*S^2*A^1*B^1
    + 18*N^5*S^1*A^4*B^4
    - 108*N^5*S^1*A^4*B^3
    + 198*N^5*S^1*A^4*B^2
    - 108*N^5*S^1*A^4*B^1
    - 108*N^5*S^1*A^3*B^4

private theorem selfDistinctChunk9_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk9 N S A B ≤ 111166*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk9
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 4 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 3 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 2 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 1 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 1 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 2 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 2 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 4 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 4 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 3 4]

private def selfDistinctChunk10 (N S A B : ℝ) : ℝ :=
  -1344*N^5*S^1*A^3*B^3
    + 4788*N^5*S^1*A^3*B^2
    - 3336*N^5*S^1*A^3*B^1
    + 198*N^5*S^1*A^2*B^4
    + 4788*N^5*S^1*A^2*B^3
    + 16541*N^5*S^1*A^2*B^2
    - 21527*N^5*S^1*A^2*B^1
    - 108*N^5*S^1*A^1*B^4
    - 3336*N^5*S^1*A^1*B^3
    - 21527*N^5*S^1*A^1*B^2
    - 19337*N^5*S^1*A^1*B^1
    + 48*N^4*S^4*A^4*B^4
    - 396*N^4*S^4*A^4*B^3
    - 519*N^4*S^4*A^4*B^2
    - 18*N^4*S^4*A^4*B^1
    - 396*N^4*S^4*A^3*B^4
    - 1170*N^4*S^4*A^3*B^3
    + 1458*N^4*S^4*A^3*B^2

private theorem selfDistinctChunk10_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk10 N S A B ≤ 27821*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk10
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 2 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 5 1 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 1 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 5 1 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 4 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 4 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 4 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 3 2 (by norm_num)]

private def selfDistinctChunk11 (N S A B : ℝ) : ℝ :=
  108*N^4*S^4*A^3*B^1
    - 519*N^4*S^4*A^2*B^4
    + 1458*N^4*S^4*A^2*B^3
    - 741*N^4*S^4*A^2*B^2
    - 198*N^4*S^4*A^2*B^1
    - 18*N^4*S^4*A^1*B^4
    + 108*N^4*S^4*A^1*B^3
    - 198*N^4*S^4*A^1*B^2
    + 108*N^4*S^4*A^1*B^1
    - 396*N^4*S^3*A^4*B^4
    - 1170*N^4*S^3*A^4*B^3
    + 1458*N^4*S^3*A^4*B^2
    + 108*N^4*S^3*A^4*B^1
    - 1170*N^4*S^3*A^3*B^4
    + 19506*N^4*S^3*A^3*B^3
    + 21258*N^4*S^3*A^3*B^2
    + 1020*N^4*S^3*A^3*B^1
    + 1458*N^4*S^3*A^2*B^4

private theorem selfDistinctChunk11_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk11 N S A B ≤ 46590*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk11
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 2 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 2 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 2 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 1 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 1 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 4 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 4 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 4 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 4 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 4 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 3 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 3 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 3 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 3 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 2 4 (by norm_num)]

private def selfDistinctChunk12 (N S A B : ℝ) : ℝ :=
  21258*N^4*S^3*A^2*B^3
    - 18900*N^4*S^3*A^2*B^2
    - 3816*N^4*S^3*A^2*B^1
    + 108*N^4*S^3*A^1*B^4
    + 1020*N^4*S^3*A^1*B^3
    - 3816*N^4*S^3*A^1*B^2
    + 2688*N^4*S^3*A^1*B^1
    - 519*N^4*S^2*A^4*B^4
    + 1458*N^4*S^2*A^4*B^3
    - 741*N^4*S^2*A^4*B^2
    - 198*N^4*S^2*A^4*B^1
    + 1458*N^4*S^2*A^3*B^4
    + 21258*N^4*S^2*A^3*B^3
    - 18900*N^4*S^2*A^3*B^2
    - 3816*N^4*S^2*A^3*B^1
    - 741*N^4*S^2*A^2*B^4
    - 18900*N^4*S^2*A^2*B^3
    - 75887*N^4*S^2*A^2*B^2

private theorem selfDistinctChunk12_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk12 N S A B ≤ 49248*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk12
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 2 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 2 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 2 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 1 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 1 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 3 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 3 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 4 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 4 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 4 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 3 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 3 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 2 2]

private def selfDistinctChunk13 (N S A B : ℝ) : ℝ :=
  -9272*N^4*S^2*A^2*B^1
    - 198*N^4*S^2*A^1*B^4
    - 3816*N^4*S^2*A^1*B^3
    - 9272*N^4*S^2*A^1*B^2
    + 13286*N^4*S^2*A^1*B^1
    - 18*N^4*S^1*A^4*B^4
    + 108*N^4*S^1*A^4*B^3
    - 198*N^4*S^1*A^4*B^2
    + 108*N^4*S^1*A^4*B^1
    + 108*N^4*S^1*A^3*B^4
    + 1020*N^4*S^1*A^3*B^3
    - 3816*N^4*S^1*A^3*B^2
    + 2688*N^4*S^1*A^3*B^1
    - 198*N^4*S^1*A^2*B^4
    - 3816*N^4*S^1*A^2*B^3
    - 9272*N^4*S^1*A^2*B^2
    + 13286*N^4*S^1*A^2*B^1
    + 108*N^4*S^1*A^1*B^4

private theorem selfDistinctChunk13_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk13 N S A B ≤ 30712*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk13
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 2 1 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 2 1 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 4 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 4 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 4 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 3 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 3 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 3 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 3 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 4 1 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 1 4 (by norm_num)]

private def selfDistinctChunk14 (N S A B : ℝ) : ℝ :=
  2688*N^4*S^1*A^1*B^3
    + 13286*N^4*S^1*A^1*B^2
    + 7066*N^4*S^1*A^1*B^1
    + 480*N^3*S^4*A^4*B^4
    + 3744*N^3*S^4*A^4*B^3
    + 765*N^3*S^4*A^4*B^2
    + 6*N^3*S^4*A^4*B^1
    + 3744*N^3*S^4*A^3*B^4
    - 1446*N^3*S^4*A^3*B^3
    - 2262*N^3*S^4*A^3*B^2
    - 36*N^3*S^4*A^3*B^1
    + 765*N^3*S^4*A^2*B^4
    - 2262*N^3*S^4*A^2*B^3
    + 1431*N^3*S^4*A^2*B^2
    + 66*N^3*S^4*A^2*B^1
    + 6*N^3*S^4*A^1*B^4
    - 36*N^3*S^4*A^1*B^3
    + 66*N^3*S^4*A^1*B^2

private theorem selfDistinctChunk14_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk14 N S A B ≤ 34113*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk14
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 1 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 1 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 4 1 1 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 4 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 4 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 4 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 4 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 3 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 3 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 2 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 2 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 1 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 1 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 4 1 2 (by norm_num)]

private def selfDistinctChunk15 (N S A B : ℝ) : ℝ :=
  -36*N^3*S^4*A^1*B^1
    + 3744*N^3*S^3*A^4*B^4
    - 1446*N^3*S^3*A^4*B^3
    - 2262*N^3*S^3*A^4*B^2
    - 36*N^3*S^3*A^4*B^1
    - 1446*N^3*S^3*A^3*B^4
    - 56586*N^3*S^3*A^3*B^3
    - 20472*N^3*S^3*A^3*B^2
    - 288*N^3*S^3*A^3*B^1
    - 2262*N^3*S^3*A^2*B^4
    - 20472*N^3*S^3*A^2*B^3
    + 21618*N^3*S^3*A^2*B^2
    + 1116*N^3*S^3*A^2*B^1
    - 36*N^3*S^3*A^1*B^4
    - 288*N^3*S^3*A^1*B^3
    + 1116*N^3*S^3*A^1*B^2
    - 792*N^3*S^3*A^1*B^1
    + 765*N^3*S^2*A^4*B^4

private theorem selfDistinctChunk15_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk15 N S A B ≤ 28359*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk15
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 4 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 4 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 4 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 4 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 3 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 3 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 2 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 2 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 1 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 3 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 3 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 4 4 (by norm_num)]

private def selfDistinctChunk16 (N S A B : ℝ) : ℝ :=
  -2262*N^3*S^2*A^4*B^3
    + 1431*N^3*S^2*A^4*B^2
    + 66*N^3*S^2*A^4*B^1
    - 2262*N^3*S^2*A^3*B^4
    - 20472*N^3*S^2*A^3*B^3
    + 21618*N^3*S^2*A^3*B^2
    + 1116*N^3*S^2*A^3*B^1
    + 1431*N^3*S^2*A^2*B^4
    + 21618*N^3*S^2*A^2*B^3
    + 47313*N^3*S^2*A^2*B^2
    + 2070*N^3*S^2*A^2*B^1
    + 66*N^3*S^2*A^1*B^4
    + 1116*N^3*S^2*A^1*B^3
    + 2070*N^3*S^2*A^1*B^2
    - 3252*N^3*S^2*A^1*B^1
    + 6*N^3*S^1*A^4*B^4
    - 36*N^3*S^1*A^4*B^3
    + 66*N^3*S^1*A^4*B^2

private theorem selfDistinctChunk16_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk16 N S A B ≤ 99987*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk16
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 4 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 4 1 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 3 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 3 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 2 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 2 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 2 1 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 1 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 1 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 2 1 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 2 1 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 4 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 4 2 (by norm_num)]

private def selfDistinctChunk17 (N S A B : ℝ) : ℝ :=
  -36*N^3*S^1*A^4*B^1
    - 36*N^3*S^1*A^3*B^4
    - 288*N^3*S^1*A^3*B^3
    + 1116*N^3*S^1*A^3*B^2
    - 792*N^3*S^1*A^3*B^1
    + 66*N^3*S^1*A^2*B^4
    + 1116*N^3*S^1*A^2*B^3
    + 2070*N^3*S^1*A^2*B^2
    - 3252*N^3*S^1*A^2*B^1
    - 36*N^3*S^1*A^1*B^4
    - 792*N^3*S^1*A^1*B^3
    - 3252*N^3*S^1*A^1*B^2
    - 960*N^3*S^1*A^1*B^1
    - 6612*N^2*S^4*A^4*B^4
    - 8364*N^2*S^4*A^4*B^3
    - 336*N^2*S^4*A^4*B^2
    - 8364*N^2*S^4*A^3*B^4
    + 7356*N^2*S^4*A^3*B^3

private theorem selfDistinctChunk17_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk17 N S A B ≤ 11724*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk17
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 4 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 3 1,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 2 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 2 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 3 1 2 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 2 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 1 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 1 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 1 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 3 1 1 1,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 4 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 4 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 4 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 3 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 3 3 (by norm_num)]

private def selfDistinctChunk18 (N S A B : ℝ) : ℝ :=
  1008*N^2*S^4*A^3*B^2
    - 336*N^2*S^4*A^2*B^4
    + 1008*N^2*S^4*A^2*B^3
    - 672*N^2*S^4*A^2*B^2
    - 8364*N^2*S^3*A^4*B^4
    + 7356*N^2*S^3*A^4*B^3
    + 1008*N^2*S^3*A^4*B^2
    + 7356*N^2*S^3*A^3*B^4
    + 63996*N^2*S^3*A^3*B^3
    + 7056*N^2*S^3*A^3*B^2
    + 1008*N^2*S^3*A^2*B^4
    + 7056*N^2*S^3*A^2*B^3
    - 8064*N^2*S^3*A^2*B^2
    - 336*N^2*S^2*A^4*B^4
    + 1008*N^2*S^2*A^4*B^3
    - 672*N^2*S^2*A^4*B^2
    + 1008*N^2*S^2*A^3*B^4
    + 7056*N^2*S^2*A^3*B^3

private theorem selfDistinctChunk18_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk18 N S A B ≤ 105924*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk18
  nlinarith only [
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 3 2 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 2 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 4 2 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 4 2 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 4 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 4 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 4 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 3 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 3 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 3 2 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 2 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 3 2 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 3 2 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 4 4,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 4 3 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 4 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 3 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 2 2 3 3 (by norm_num)]

private def selfDistinctChunk19 (N S A B : ℝ) : ℝ :=
  -8064*N^2*S^2*A^3*B^2
    - 672*N^2*S^2*A^2*B^4
    - 8064*N^2*S^2*A^2*B^3
    - 11424*N^2*S^2*A^2*B^2
    + 19044*N^1*S^4*A^4*B^4
    + 5040*N^1*S^4*A^4*B^3
    + 5040*N^1*S^4*A^3*B^4
    - 5040*N^1*S^4*A^3*B^3
    + 5040*N^1*S^3*A^4*B^4
    - 5040*N^1*S^3*A^4*B^3
    - 5040*N^1*S^3*A^3*B^4
    - 25200*N^1*S^3*A^3*B^3
    - 15120*N^0*S^4*A^4*B^4

private theorem selfDistinctChunk19_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctChunk19 N S A B ≤ 34164*N^16 := by
  have hN0 : 0 ≤ N := by linarith
  unfold selfDistinctChunk19
  nlinarith only [
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 3 2,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 2 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 2 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 2 2 2 2,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 4 4 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 4 3 (by norm_num),
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 4 3 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 4 3 3,
    self_monomial_le_pow_sixteen N S A B hN1 hS0 hSN hA0 hAN hB0 hBN 1 3 4 4 (by norm_num),
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 3 4 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 3 3 4,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 1 3 3 3,
    self_monomial_nonneg N S A B hN0 hS0 hA0 hB0 0 4 4 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem selfDistinctNumerator_eq_chunks (N S A B : ℝ) :
    selfDistinctNumerator N S A B =
        selfDistinctChunk0 N S A B
      + selfDistinctChunk1 N S A B
      + selfDistinctChunk2 N S A B
      + selfDistinctChunk3 N S A B
      + selfDistinctChunk4 N S A B
      + selfDistinctChunk5 N S A B
      + selfDistinctChunk6 N S A B
      + selfDistinctChunk7 N S A B
      + selfDistinctChunk8 N S A B
      + selfDistinctChunk9 N S A B
      + selfDistinctChunk10 N S A B
      + selfDistinctChunk11 N S A B
      + selfDistinctChunk12 N S A B
      + selfDistinctChunk13 N S A B
      + selfDistinctChunk14 N S A B
      + selfDistinctChunk15 N S A B
      + selfDistinctChunk16 N S A B
      + selfDistinctChunk17 N S A B
      + selfDistinctChunk18 N S A B
      + selfDistinctChunk19 N S A B
    := by
  unfold selfDistinctNumerator selfMomentNumerator
  unfold selfDistinctChunk0
  unfold selfDistinctChunk1
  unfold selfDistinctChunk2
  unfold selfDistinctChunk3
  unfold selfDistinctChunk4
  unfold selfDistinctChunk5
  unfold selfDistinctChunk6
  unfold selfDistinctChunk7
  unfold selfDistinctChunk8
  unfold selfDistinctChunk9
  unfold selfDistinctChunk10
  unfold selfDistinctChunk11
  unfold selfDistinctChunk12
  unfold selfDistinctChunk13
  unfold selfDistinctChunk14
  unfold selfDistinctChunk15
  unfold selfDistinctChunk16
  unfold selfDistinctChunk17
  unfold selfDistinctChunk18
  unfold selfDistinctChunk19
  simp only [selfFall]
  ring

private theorem selfDistinctNumerator_le (N S A B : ℝ)
    (hN1 : 1 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctNumerator N S A B ≤ 734237*N^16 := by
  rw [selfDistinctNumerator_eq_chunks N S A B]
  have h0 := selfDistinctChunk0_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h1 := selfDistinctChunk1_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h2 := selfDistinctChunk2_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h3 := selfDistinctChunk3_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h4 := selfDistinctChunk4_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h5 := selfDistinctChunk5_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h6 := selfDistinctChunk6_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h7 := selfDistinctChunk7_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h8 := selfDistinctChunk8_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h9 := selfDistinctChunk9_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h10 := selfDistinctChunk10_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h11 := selfDistinctChunk11_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h12 := selfDistinctChunk12_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h13 := selfDistinctChunk13_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h14 := selfDistinctChunk14_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h15 := selfDistinctChunk15_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h16 := selfDistinctChunk16_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h17 := selfDistinctChunk17_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h18 := selfDistinctChunk18_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  have h19 := selfDistinctChunk19_le N S A B hN1 hS0 hSN hA0 hAN hB0 hBN
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

private theorem selfFall_pos_of_eight (N : ℝ) (hN : 8 ≤ N)
    (r : ℕ) (hr : r ≤ 8) : 0 < selfFall N r := by
  induction r with
  | zero => simp [selfFall]
  | succ r ih =>
      rw [selfFall]
      have hr7 : r ≤ 7 := by omega
      have hr7R : (r : ℝ) ≤ 7 := by exact_mod_cast hr7
      have hfactor : 0 < N - (r : ℝ) := by
        linarith
      exact mul_pos hfactor (ih (by omega))

private theorem selfFall_lower_of_eight (N : ℝ) (hN : 8 ≤ N)
    (r : ℕ) (hr : r ≤ 8) : (N/8)^r ≤ selfFall N r := by
  induction r with
  | zero => simp [selfFall]
  | succ r ih =>
      rw [selfFall]
      have hr7 : r ≤ 7 := by omega
      have hr7R : (r : ℝ) ≤ 7 := by exact_mod_cast hr7
      have hN0 : 0 ≤ N := by linarith
      have hfactor : N/8 ≤ N - (r : ℝ) := by linarith
      have hfactor0 : 0 ≤ N/8 := by positivity
      calc
        (N/8)^(r+1) = (N/8)*(N/8)^r := by ring
        _ ≤ (N-(r:ℝ))*selfFall N r :=
          mul_le_mul hfactor (ih (by omega)) (by positivity)
            (hfactor0.trans hfactor)

private theorem selfMomentDenominator_pos (N : ℝ) (hN : 8 ≤ N) :
    0 < selfMomentDenominator N := by
  unfold selfMomentDenominator
  exact mul_pos (selfFall_pos_of_eight N hN 8 (by omega))
    (pow_pos (selfFall_pos_of_eight N hN 2 (by omega)) 3)

private theorem selfMomentDenominator_lower (N : ℝ) (hN : 8 ≤ N) :
    N^14 / 8^14 ≤ selfMomentDenominator N := by
  have hN0 : 0 ≤ N := by linarith
  have h8 := selfFall_lower_of_eight N hN 8 (by omega)
  have h2 := selfFall_lower_of_eight N hN 2 (by omega)
  have h8nonneg : 0 ≤ selfFall N 8 :=
    (selfFall_pos_of_eight N hN 8 (by omega)).le
  unfold selfMomentDenominator
  calc
    N^14 / 8^14 = (N/8)^8 * ((N/8)^2)^3 := by ring
    _ ≤ selfFall N 8 * (selfFall N 2)^3 := by gcongr

set_option maxHeartbeats 1000000 in
private theorem selfSameMoment_eq_numerator_div (N S A : ℝ) (hN : 8 ≤ N) :
    selfSameMoment N S A =
      selfSameNumerator N S A / selfMomentDenominator N := by
  have h2 : selfFall N 2 ≠ 0 :=
    (selfFall_pos_of_eight N hN 2 (by omega)).ne'
  have h4 : selfFall N 4 ≠ 0 :=
    (selfFall_pos_of_eight N hN 4 (by omega)).ne'
  have h6 : selfFall N 6 ≠ 0 :=
    (selfFall_pos_of_eight N hN 6 (by omega)).ne'
  have h8 : selfFall N 8 ≠ 0 :=
    (selfFall_pos_of_eight N hN 8 (by omega)).ne'
  unfold selfSameMoment selfMomentFromFactorials selfSameNumerator
  unfold selfMomentNumerator selfMomentDenominator
  field_simp [h2, h4, h6, h8]
  simp only [selfFall]
  ring

set_option maxHeartbeats 1000000 in
private theorem selfDistinctMoment_eq_numerator_div
    (N S A B : ℝ) (hN : 8 ≤ N) :
    selfDistinctMoment N S A B =
      selfDistinctNumerator N S A B / selfMomentDenominator N := by
  have h2 : selfFall N 2 ≠ 0 :=
    (selfFall_pos_of_eight N hN 2 (by omega)).ne'
  have h4 : selfFall N 4 ≠ 0 :=
    (selfFall_pos_of_eight N hN 4 (by omega)).ne'
  have h6 : selfFall N 6 ≠ 0 :=
    (selfFall_pos_of_eight N hN 6 (by omega)).ne'
  have h8 : selfFall N 8 ≠ 0 :=
    (selfFall_pos_of_eight N hN 8 (by omega)).ne'
  unfold selfDistinctMoment selfMomentFromFactorials selfDistinctNumerator
  unfold selfMomentNumerator selfMomentDenominator
  field_simp [h2, h4, h6, h8]
  simp only [selfFall]
  ring

private def selfMomentConstant : ℝ := 2479446 * 8^14

private theorem self_numerator_div_le (N P : ℝ) (hN : 8 ≤ N)
    (hP : P ≤ 2479446*N^16) :
    P / selfMomentDenominator N ≤ selfMomentConstant*N^2 := by
  have hdenpos := selfMomentDenominator_pos N hN
  have hden := selfMomentDenominator_lower N hN
  have hC0 : 0 ≤ selfMomentConstant := by
    unfold selfMomentConstant
    positivity
  by_cases hP0 : 0 ≤ P
  · apply (div_le_iff₀ hdenpos).2
    calc
      P ≤ 2479446*N^16 := hP
      _ = selfMomentConstant*N^2*(N^14/8^14) := by
        unfold selfMomentConstant
        ring
      _ ≤ selfMomentConstant*N^2*selfMomentDenominator N := by
        gcongr
  · have hP' : P ≤ 0 := le_of_not_ge hP0
    exact (div_nonpos_of_nonpos_of_nonneg hP' hdenpos.le).trans
      (mul_nonneg hC0 (sq_nonneg N))

private theorem selfSameMoment_le (N S A : ℝ) (hN : 8 ≤ N)
    (hS0 : 0 ≤ S) (hSN : S ≤ N) (hA0 : 0 ≤ A) (hAN : A ≤ N) :
    selfSameMoment N S A ≤ selfMomentConstant*N^2 := by
  rw [selfSameMoment_eq_numerator_div N S A hN]
  apply self_numerator_div_le N _ hN
  exact selfSameNumerator_le N S A A (by linarith) hS0 hSN
    hA0 hAN hA0 hAN

private theorem selfDistinctMoment_le (N S A B : ℝ) (hN : 8 ≤ N)
    (hS0 : 0 ≤ S) (hSN : S ≤ N) (hA0 : 0 ≤ A) (hAN : A ≤ N)
    (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    selfDistinctMoment N S A B ≤ selfMomentConstant*N^2 := by
  rw [selfDistinctMoment_eq_numerator_div N S A B hN]
  apply self_numerator_div_le N _ hN
  calc
    selfDistinctNumerator N S A B ≤ 734237*N^16 :=
      selfDistinctNumerator_le N S A B (by linarith) hS0 hSN
        hA0 hAN hB0 hBN
    _ ≤ 2479446*N^16 := by gcongr <;> norm_num


private theorem self_words_card_positive {α : Type*} [Fintype α]
    [DecidableEq α] {n : ℕ} (hn : 0 < n) (k : α → ℕ)
    (hk : ∑ a, k a = n) : 0 < Fintype.card (Words n k) := by
  have hb := type_class_bounds n k hk
  have hleft :
      0 < Real.exp ((n : ℝ) * entropyNats (fun a => (k a : ℝ) / n)) /
        ((n : ℝ) + 1) ^ Fintype.card α := by
    positivity
  have hcard : 0 < (Fintype.card (Words n k) : ℝ) := hleft.trans_le hb.1
  exact_mod_cast hcard

private theorem self_count_le {α : Type*} [DecidableEq α] {n : ℕ}
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n)) (a b : α)
    (x : Fin n → α) : selfPairCount S e a b x ≤ n := by
  unfold selfPairCount
  exact (Finset.card_filter_le S _).trans (by simpa using S.card_le_univ)

private theorem self_hist_le {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (k : α → ℕ) (hcard : 0 < Fintype.card (Words n k)) (a : α) :
    k a ≤ n := by
  let ⟨x⟩ := Fintype.card_pos_iff.mp hcard
  rw [← x.property a]
  unfold typeCnt
  simpa using Finset.card_filter_le Finset.univ (fun i : Fin n => x.val i = a)

private theorem self_avg_le_const {D : Type*} [Fintype D]
    (hD : 0 < Fintype.card D) (f : D → ℝ) (c : ℝ)
    (h : ∀ x, f x ≤ c) : avg f ≤ c := by
  unfold avg
  have hcard : 0 < (Fintype.card D : ℝ) := by exact_mod_cast hD
  apply (div_le_iff₀ hcard).2
  calc
    ∑ x, f x ≤ ∑ _x : D, c := Finset.sum_le_sum fun x _ => h x
    _ = c * Fintype.card D := by simp [mul_comm]

/-- Uniform `O(n²)` fourth-moment bound for an oriented self-pair sample in
the symbolic range `n ≥ 8`. -/
theorem selfPairCount_fourth_moment_of_eight
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 8 ≤ n)
    (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
    (hS : ∀ i ∈ S, e i ∉ S) (k : α → ℕ) (hk : ∑ a, k a = n)
    (a b : α) :
    avg (fun x : Words n k =>
      ((selfPairCount S e a b x.val : ℝ) -
        (S.card : ℝ) * (k a : ℝ) *
          ((k b : ℝ) - if a = b then 1 else 0) /
            ((n : ℝ) * ((n : ℝ) - 1)))^4) ≤
      (2479446 * 8^14 : ℝ)*(n:ℝ)^2 := by
  have hnpos : 0 < n := by omega
  have hwords := self_words_card_positive hnpos k hk
  have hSN : S.card ≤ n := by simpa using S.card_le_univ
  have hkaN := self_hist_le k hwords a
  have hkbN := self_hist_le k hwords b
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have hSNR : (S.card : ℝ) ≤ n := by exact_mod_cast hSN
  have hka0 : (0 : ℝ) ≤ k a := by positivity
  have hkaNR : (k a : ℝ) ≤ n := by exact_mod_cast hkaN
  have hkb0 : (0 : ℝ) ≤ k b := by positivity
  have hkbNR : (k b : ℝ) ≤ n := by exact_mod_cast hkbN
  have hmean := avg_selfPairCount (n := n) (by omega) S e hS k hk a b
  have hA1 := avg_selfPairCount_descFactorial (n := n) (r := 1)
    hnpos (by omega) S e hS k hk a b
  have havgOne :
      avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) =
        avg (fun x : Words n k =>
          ((selfPairCount S e a b x.val).descFactorial 1 : ℕ)) := by
    apply congrArg avg
    funext x
    simp only [Nat.descFactorial_one]
  have hmu :
      (S.card : ℝ) * (k a : ℝ) *
          ((k b : ℝ) - if a = b then 1 else 0) /
            ((n : ℝ) * ((n : ℝ) - 1)) =
        ((S.card.descFactorial 1 *
          (if a = b then (k a).descFactorial (2*1)
            else (k a).descFactorial 1 * (k b).descFactorial 1) : ℕ) : ℝ) /
            n.descFactorial (2*1) := hmean.symm.trans (havgOne.trans hA1)
  rw [hmu]
  rw [avg_selfPairCount_center_four_formula hn S e hS k hk a b]
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    simp only [Nat.cast_mul, self_cast_descFactorial]
    change selfSameMoment (n : ℝ) S.card (k a) ≤
      (2479446 * 8^14 : ℝ)*(n:ℝ)^2
    simpa only [selfMomentConstant] using
      selfSameMoment_le n S.card (k a) hnR hS0 hSNR hka0 hkaNR
  · simp only [if_neg hab]
    simp only [Nat.cast_mul, self_cast_descFactorial]
    change selfDistinctMoment (n : ℝ) S.card (k a) (k b) ≤
      (2479446 * 8^14 : ℝ)*(n:ℝ)^2
    simpa only [selfMomentConstant] using
      selfDistinctMoment_le n S.card (k a) (k b) hnR hS0 hSNR
        hka0 hkaNR hkb0 hkbNR

/-- Uniform fourth-moment bound for a disjoint oriented within-cell pairing,
centered at its corrected hypergeometric mean. -/
theorem selfPairCount_fourth_moment
    {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hn : 0 < n)
      (S : Finset (Fin n)) (e : Equiv.Perm (Fin n))
      (hS : ∀ i ∈ S, e i ∉ S) (k : α → ℕ) (hk : ∑ a, k a = n)
      (a b : α),
      avg (fun x : Words n k =>
        ((selfPairCount S e a b x.val : ℝ) -
          (S.card : ℝ) * (k a : ℝ) *
            ((k b : ℝ) - if a = b then 1 else 0) /
              ((n : ℝ) * ((n : ℝ) - 1)))^4) ≤
        (2479446 * 8^14 : ℝ)*(n:ℝ)^2 := by
  refine ⟨2479446 * 8^14, by positivity, ?_⟩
  intro n hn S e hS k hk a b
  by_cases hn8 : 8 ≤ n
  · exact selfPairCount_fourth_moment_of_eight hn8 S e hS k hk a b
  · by_cases hn2 : 2 ≤ n
    · have hwords := self_words_card_positive hn k hk
      have hmean := avg_selfPairCount (n := n) hn2 S e hS k hk a b
      rw [← hmean]
      have hmean0 :
          0 ≤ avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) := by
        unfold avg
        positivity
      have hmeanN :
          avg (fun x : Words n k => (selfPairCount S e a b x.val : ℝ)) ≤ n := by
        apply self_avg_le_const hwords
        intro x
        exact_mod_cast self_count_le S e a b x.val
      have hpoint : ∀ x : Words n k,
          ((selfPairCount S e a b x.val : ℝ) -
            avg (fun y : Words n k => (selfPairCount S e a b y.val : ℝ)))^4 ≤
              (n : ℝ)^4 := by
        intro x
        have hcount0 : 0 ≤ (selfPairCount S e a b x.val : ℝ) := by positivity
        have hcountN : (selfPairCount S e a b x.val : ℝ) ≤ n := by
          exact_mod_cast self_count_le S e a b x.val
        have habs :
            |(selfPairCount S e a b x.val : ℝ) -
              avg (fun y : Words n k => (selfPairCount S e a b y.val : ℝ))| ≤ n := by
          rw [abs_le]
          constructor <;> linarith
        calc
          ((selfPairCount S e a b x.val : ℝ) -
              avg (fun y : Words n k => (selfPairCount S e a b y.val : ℝ)))^4 =
              |(selfPairCount S e a b x.val : ℝ) -
                avg (fun y : Words n k =>
                  (selfPairCount S e a b y.val : ℝ))|^4 := by
                rw [← abs_pow]
                exact (abs_of_nonneg (by positivity)).symm
          _ ≤ (n : ℝ)^4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
      calc
        avg (fun x : Words n k =>
            ((selfPairCount S e a b x.val : ℝ) -
              avg (fun y : Words n k =>
                (selfPairCount S e a b y.val : ℝ)))^4) ≤
            (n : ℝ)^4 := self_avg_le_const hwords _ _ hpoint
        _ ≤ (2479446 * 8^14 : ℝ)*(n:ℝ)^2 := by
          have hn7 : n ≤ 7 := by omega
          interval_cases n <;> norm_num
    · have hn1 : n = 1 := by omega
      subst n
      have hSempt : S = ∅ := by
        ext i
        simp only [Finset.notMem_empty, iff_false]
        intro hi
        have hei : e i = i := by
          apply Fin.ext
          omega
        apply hS i hi
        rw [hei]
        exact hi
      subst S
      simp [selfPairCount, avg]
      positivity

end OmegaBound.ADVXXZGeneral
end
