import OmegaBound.ASISum
import OmegaBound.BlockDiag
import OmegaBound.Rectangular
import OmegaBound.ADVXXZGeneralEndpointDefs
import OmegaBound.ADVXXZGeneralRates
import OmegaBound.ADVXXZGeneralTensorAux

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem blockDiag_combineF (F : Type u) [Field F]
    {X Y Z X₁ Y₁ Z₁ X₂ Y₂ Z₂ XP YP ZP : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [Fintype X₁] [Fintype Y₁] [Fintype Z₁] [DecidableEq X₁] [DecidableEq Y₁] [DecidableEq Z₁]
    [Fintype X₂] [Fintype Y₂] [Fintype Z₂] [DecidableEq X₂] [DecidableEq Y₂] [DecidableEq Z₂]
    [Fintype XP] [Fintype YP] [Fintype ZP] [DecidableEq XP] [DecidableEq YP] [DecidableEq ZP]
    (W : Tensor3 F X Y Z) (P : Tensor3 F XP YP ZP)
    (T₁ : Tensor3 F X₁ Y₁ Z₁) (T₂ : Tensor3 F X₂ Y₂ Z₂) (m₁ m₂ : ℕ)
    (h₁ : blockDiag (Fin m₁) W ≤ₜ tensorProd P T₁)
    (h₂ : blockDiag (Fin m₂) W ≤ₜ tensorProd P T₂) :
    blockDiag (Fin (m₁ + m₂)) W ≤ₜ tensorProd P (T₁ ⊕ₜ T₂) :=
  Tensor3.Restricts.trans (blockDiag_add_le W m₁ m₂)
    (Tensor3.Restricts.trans (OmegaBound.Restricts.directSum h₁ h₂)
      (tensorProd_directSum_le P T₁ T₂))

private theorem blockDiag_choose_le_tpow_genF (F : Type u) [Field F]
    {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (T : Tensor3 F X Y Z) (U : Tensor3 F X' Y' Z') :
    ∀ (N k : ℕ),
      blockDiag (Fin (N.choose k)) (tensorProd (tpow T k) (tpow U (N - k)))
        ≤ₜ tpow (T ⊕ₜ U) N := by
  intro N
  induction N with
  | zero =>
      intro k
      match k with
      | 0 =>
          rw [show Nat.choose 0 0 = 1 from rfl]
          refine Restricts.of_eq (precomp_restricts
            (fun _ => (PUnit.unit : TIdx (X ⊕ X') 0))
            (fun _ => (PUnit.unit : TIdx (Y ⊕ Y') 0))
            (fun _ => (PUnit.unit : TIdx (Z ⊕ Z') 0))
            (tpow (T ⊕ₜ U) 0)) ?_
          funext x y z
          obtain ⟨t, x₁, x₂⟩ := x; obtain ⟨t', y₁, y₂⟩ := y; obtain ⟨t'', z₁, z₂⟩ := z
          rw [blockDiag_apply, if_pos ⟨Subsingleton.elim t t', Subsingleton.elim t t''⟩]
          simp [tensorProd, tpow]
      | k + 1 =>
          rw [Nat.choose_zero_succ]
          exact blockDiag_empty_le _ _
  | succ N ih =>
      intro k
      match k with
      | 0 =>
          rw [show (N + 1).choose 0 = 0 + N.choose 0 by simp]
          refine blockDiag_combineF F _ _ _ _ 0 (N.choose 0) (blockDiag_empty_le _ _) ?_
          have hstep : tensorProd (tpow T 0) (tpow U (N + 1 - 0))
              ≤ₜ tensorProd (tensorProd (tpow T 0) (tpow U (N - 0))) U := by
            have h1 : N + 1 - 0 = N - 0 + 1 := by omega
            rw [h1]
            exact tensorProd_assoc_le (tpow T 0) (tpow U (N - 0)) U
          refine Tensor3.Restricts.trans (blockDiag_mono (R := F) (N.choose 0) hstep) ?_
          refine Tensor3.Restricts.trans (blockDiag_tensorProd_le _ _) ?_
          exact OmegaBound.Restricts.tensorProd_right (ih 0) _
      | k + 1 =>
          rw [Nat.choose_succ_succ N k]
          refine blockDiag_combineF F _ _ _ _ (N.choose k) (N.choose (k + 1)) ?_ ?_
          · have hsub : N + 1 - (k + 1) = N - k := by omega
            have hstep : tensorProd (tpow T (k + 1)) (tpow U (N + 1 - (k + 1)))
                ≤ₜ tensorProd (tensorProd (tpow T k) (tpow U (N - k))) T := by
              rw [hsub]
              exact tensorProd_swap23_le (tpow T k) (tpow U (N - k)) T
            refine Tensor3.Restricts.trans (blockDiag_mono (R := F) (N.choose k) hstep) ?_
            refine Tensor3.Restricts.trans (blockDiag_tensorProd_le _ _) ?_
            exact OmegaBound.Restricts.tensorProd_right (ih k) _
          · by_cases hkN : k + 1 ≤ N
            · have hstep : tensorProd (tpow T (k + 1)) (tpow U (N + 1 - (k + 1)))
                  ≤ₜ tensorProd (tensorProd (tpow T (k + 1)) (tpow U (N - (k + 1)))) U := by
                have he : N + 1 - (k + 1) = N - (k + 1) + 1 := by omega
                rw [he]
                exact tensorProd_assoc_le (tpow T (k + 1)) (tpow U (N - (k + 1))) U
              refine Tensor3.Restricts.trans
                (blockDiag_mono (R := F) (N.choose (k + 1)) hstep) ?_
              refine Tensor3.Restricts.trans (blockDiag_tensorProd_le _ _) ?_
              exact OmegaBound.Restricts.tensorProd_right (ih (k + 1)) _
            · rw [Nat.choose_eq_zero_of_lt (by omega)]
              exact blockDiag_empty_le _ _

private theorem blockDiag_le_tpow_mmDSumF (F : Type u) [Field F]
    (a b c : ℕ → ℕ) :
    ∀ (s : ℕ) (m : ℕ → ℕ),
      blockDiag (Fin (mmult m s))
        (Tensor3.matMul (R := F) (∏ i ∈ Finset.range s, a i ^ m i)
          (∏ i ∈ Finset.range s, b i ^ m i) (∏ i ∈ Finset.range s, c i ^ m i))
      ≤ₜ tpow (mmDSumF F a b c s) (∑ i ∈ Finset.range s, m i) := by
  intro s
  induction s with
  | zero =>
      intro m
      rw [show mmult m 0 = 1 from rfl]
      show blockDiag (Fin 1) (Tensor3.matMul (R := F) 1 1 1) ≤ₜ tpow (mmDSumF F a b c 0) 0
      refine Restricts.of_eq (precomp_restricts
        (fun _ => (PUnit.unit : TIdx (mmIdxSum a b 0) 0))
        (fun _ => (PUnit.unit : TIdx (mmIdxSum b c 0) 0))
        (fun _ => (PUnit.unit : TIdx (mmIdxSum c a 0) 0))
        (tpow (mmDSumF F a b c 0) 0)) ?_
      funext x y z
      obtain ⟨t, u⟩ := x; obtain ⟨t', v⟩ := y; obtain ⟨t'', w⟩ := z
      rw [blockDiag_apply, if_pos ⟨Subsingleton.elim t t', Subsingleton.elim t t''⟩]
      exact matMul_one_apply u v w
  | succ s ih =>
      intro m
      set k : ℕ := m s with hk
      set N : ℕ := ∑ i ∈ Finset.range (s + 1), m i with hN
      have hNk : N - k = ∑ i ∈ Finset.range s, m i := by
        rw [hN, Finset.sum_range_succ]; omega
      have hsplit := blockDiag_choose_le_tpow_genF F
        (Tensor3.matMul (R := F) (a s) (b s) (c s))
        (mmDSumF F a b c s) N k
      have hinner : blockDiag (Fin (mmult m s))
          (Tensor3.matMul (R := F) (∏ i ∈ Finset.range s, a i ^ m i)
            (∏ i ∈ Finset.range s, b i ^ m i) (∏ i ∈ Finset.range s, c i ^ m i))
          ≤ₜ tpow (mmDSumF F a b c s) (N - k) := by rw [hNk]; exact ih m
      have houter : blockDiag (Fin (mmult m s))
          (Tensor3.matMul (R := F) (∏ i ∈ Finset.range (s + 1), a i ^ m i)
            (∏ i ∈ Finset.range (s + 1), b i ^ m i)
            (∏ i ∈ Finset.range (s + 1), c i ^ m i))
          ≤ₜ tensorProd (tpow (Tensor3.matMul (R := F) (a s) (b s) (c s)) k)
              (tpow (mmDSumF F a b c s) (N - k)) := by
        have hfac : Tensor3.matMul (R := F) (∏ i ∈ Finset.range (s + 1), a i ^ m i)
            (∏ i ∈ Finset.range (s + 1), b i ^ m i)
            (∏ i ∈ Finset.range (s + 1), c i ^ m i)
            ≤ₜ tensorProd (Tensor3.matMul (R := F) (a s ^ k) (b s ^ k) (c s ^ k))
              (Tensor3.matMul (R := F) (∏ i ∈ Finset.range s, a i ^ m i)
                (∏ i ∈ Finset.range s, b i ^ m i)
                (∏ i ∈ Finset.range s, c i ^ m i)) :=
          matMul_congr_le (matMul_restricts_tensorProd _ _ _ _ _ _)
            (by rw [Finset.prod_range_succ]; ring)
            (by rw [Finset.prod_range_succ]; ring)
            (by rw [Finset.prod_range_succ]; ring)
        refine Tensor3.Restricts.trans (blockDiag_mono (R := F) (mmult m s) hfac) ?_
        have h1 : blockDiag (Fin (mmult m s))
            (tensorProd (Tensor3.matMul (R := F) (a s ^ k) (b s ^ k) (c s ^ k))
              (Tensor3.matMul (R := F) (∏ i ∈ Finset.range s, a i ^ m i)
                (∏ i ∈ Finset.range s, b i ^ m i)
                (∏ i ∈ Finset.range s, c i ^ m i)))
            ≤ₜ tensorProd (Tensor3.matMul (R := F) (a s ^ k) (b s ^ k) (c s ^ k))
              (blockDiag (Fin (mmult m s))
                (Tensor3.matMul (R := F) (∏ i ∈ Finset.range s, a i ^ m i)
                  (∏ i ∈ Finset.range s, b i ^ m i)
                  (∏ i ∈ Finset.range s, c i ^ m i))) :=
          blockDiag_tensorProd_le' _ _ _
        refine Tensor3.Restricts.trans h1 ?_
        refine Tensor3.Restricts.trans
          (OmegaBound.Restricts.tensorProd_right (matMul_le_tpow (R := F) (a s) (b s) (c s) k) _) ?_
        exact OmegaBound.Restricts.tensorProd_left hinner _
      have hmul : blockDiag (Fin (N.choose k * mmult m s))
          (Tensor3.matMul (R := F) (∏ i ∈ Finset.range (s + 1), a i ^ m i)
            (∏ i ∈ Finset.range (s + 1), b i ^ m i)
            (∏ i ∈ Finset.range (s + 1), c i ^ m i))
          ≤ₜ blockDiag (Fin (N.choose k))
              (tensorProd (tpow (Tensor3.matMul (R := F) (a s) (b s) (c s)) k)
                (tpow (mmDSumF F a b c s) (N - k))) :=
        Tensor3.Restricts.trans (blockDiag_mul_le _ _ _)
          (blockDiag_mono (R := F) (N.choose k) houter)
      exact Tensor3.Restricts.trans hmul hsplit

private theorem polyDegeneratesAt_tpow_identity (F : Type u) [Field F]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (D r : ℕ) (T : Tensor3 F X Y Z)
    (h : PolyDegeneratesAt F D (Tensor3.identity F r) T) :
    ∀ n : ℕ, PolyDegeneratesAt F (n*D) (Tensor3.identity F (r^n)) (tpow T n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_, ?_⟩
      · intro x y z k hk
        omega
      · intro x y z
        rcases x with ⟨⟩
        rcases y with ⟨⟩
        rcases z with ⟨⟩
        simp [Tensor3.identity, tpow]
        rw [show ({x ∈ ({0} : Finset (Fin 1)) | (0 : Fin 1) = x}).card = 1 by
          decide +kernel]
        norm_num
  | succ n ih =>
      have hp := polyDegeneratesAt_tensorProd ih h
      let e : Fin (r^n*r) ≃ Fin (r^n) × Fin r :=
        (finProdFinEquiv (m := r^n) (n := r)).symm
      have hs := polyDegeneratesAt_source_equiv hp e e e
      have he : Tensor3.identity F (r^n*r) = fun x y z =>
          tensorProd (Tensor3.identity F (r^n)) (Tensor3.identity F r)
            (e x) (e y) (e z) := by
        funext x y z
        rw [identity_tensorProd]
        change Tensor3.identity F (r^n*r) x y z =
          Tensor3.identity F (r^n*r) (e.symm (e x)) (e.symm (e y)) (e.symm (e z))
        rw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
      have hs' := polyDegeneratesAt_source_eq hs he
      simpa only [Nat.succ_mul, pow_succ, tpow_succ] using hs'

private theorem one_le_of_rankLE_matMulF (F : Type u) [Field F]
    {a b c r : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : RankLE (Tensor3.matMul (R := F) a b c) r) : 1 ≤ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exfalso
    have hz := eq_zero_of_rankLE_zero h
    have hone : Tensor3.matMul (R := F) a b c (⟨0, ha⟩, ⟨0, hb⟩) (⟨0, hb⟩, ⟨0, hc⟩)
        (⟨0, hc⟩, ⟨0, ha⟩) = 1 := by simp [Tensor3.matMul]
    rw [hz] at hone
    simp at hone
  · exact hr

private theorem rankLE_stepF (F : Type u) [Field F]
    {A B C M s r K : ℕ} (hr : r ≤ K*M)
    (hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) s) {j : ℕ}
    (h : RankLE (Tensor3.matMul (R := F) (A^j) (B^j) (C^j)) r) :
    RankLE (Tensor3.matMul (R := F) (A^(j+1)) (B^(j+1)) (C^(j+1))) (K*s) := by
  have h₁ : Tensor3.matMul (R := F) (A^(j+1)) (B^(j+1)) (C^(j+1))
      ≤ₜ tensorProd (Tensor3.matMul (R := F) (A^j) (B^j) (C^j))
        (Tensor3.matMul (R := F) A B C) :=
    matMul_congr_le (matMul_restricts_tensorProd (A^j) (B^j) (C^j) A B C)
      (by ring) (by ring) (by ring)
  have h₂ : tensorProd (Tensor3.matMul (R := F) (A^j) (B^j) (C^j))
      (Tensor3.matMul (R := F) A B C)
      ≤ₜ tensorProd (Tensor3.identity F r) (Tensor3.matMul (R := F) A B C) :=
    OmegaBound.Restricts.tensorProd_right h _
  have h₃ : blockDiag (Fin r) (Tensor3.matMul (R := F) A B C)
      ≤ₜ blockDiag (Fin (K*M)) (Tensor3.matMul (R := F) A B C) :=
    blockDiag_le_of_injective _ (Fin.castLE_injective hr)
  have h₄ := blockDiag_mul_le (Tensor3.matMul (R := F) A B C) K M
  have h₅ : RankLE (blockDiag (Fin K) (blockDiag (Fin M)
      (Tensor3.matMul (R := F) A B C))) (K*s) := hblk.blockDiag K
  refine OmegaBound.RankLE.mono (Tensor3.Restricts.trans h₁ (Tensor3.Restricts.trans h₂ ?_)) h₅
  rw [← blockDiag_eq_tensorProd]
  exact Tensor3.Restricts.trans h₃ h₄

private theorem exists_ceil_mulF (r M : ℕ) (hM : 1 ≤ M) :
    ∃ K : ℕ, r ≤ K*M ∧ (K:ℝ)*(M:ℝ) ≤ (r:ℝ)+(M:ℝ) := by
  refine ⟨(r+M-1)/M, ?_, ?_⟩
  · have h₁ : M*((r+M-1)/M) + (r+M-1)%M = r+M-1 := Nat.div_add_mod _ _
    have h₂ : (r+M-1)%M < M := Nat.mod_lt _ hM
    have h₃ : r ≤ M*((r+M-1)/M) := by
      generalize hp : M*((r+M-1)/M) = p at h₁
      omega
    rw [Nat.mul_comm]
    exact h₃
  · have h₁ : (r+M-1)/M*M ≤ r+M-1 := Nat.div_mul_le_self _ _
    have h₂ : (r+M-1)/M*M ≤ r+M := by omega
    exact_mod_cast h₂

private theorem rankLE_pow_of_blockDiagF (F : Type u) [Field F]
    {A B C M s : ℕ} (hM : 1 ≤ M)
    (hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) s) (j : ℕ) :
    ∃ r : ℕ, RankLE (Tensor3.matMul (R := F) (A^(j+1)) (B^(j+1)) (C^(j+1))) r ∧
      (r:ℝ) ≤ (M:ℝ)*(1+(s:ℝ)/(M:ℝ))^(j+1) := by
  have hM₀ : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hρ : (0:ℝ) ≤ (s:ℝ)/(M:ℝ) := by positivity
  induction j with
  | zero =>
      refine ⟨s, ?_, ?_⟩
      · have hs : Tensor3.matMul (R := F) A B C
            ≤ₜ blockDiag (Fin M) (Tensor3.matMul (R := F) A B C) :=
          restricts_blockDiag _ ⟨0, hM⟩
        exact (OmegaBound.RankLE.mono hs hblk).congr_matMul (by ring) (by ring) (by ring)
      · rw [pow_one, mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hM₀)]
        linarith [hM₀]
  | succ j ih =>
      obtain ⟨r, hr, hrb⟩ := ih
      obtain ⟨K, hK₁, hK₂⟩ := exists_ceil_mulF r M hM
      refine ⟨K*s, rankLE_stepF F hK₁ hblk hr, ?_⟩
      set P : ℝ := (1+(s:ℝ)/(M:ℝ))^(j+1) with hP
      have hP₁ : 1+(s:ℝ)/(M:ℝ) ≤ P := by
        rw [hP]
        exact le_self_pow₀ (by linarith) (by omega)
      have hMP : (s:ℝ) ≤ (M:ℝ)*P := by
        have ht : (M:ℝ)*(1+(s:ℝ)/(M:ℝ)) ≤ (M:ℝ)*P :=
          mul_le_mul_of_nonneg_left hP₁ (le_of_lt hM₀)
        rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hM₀)] at ht
        linarith
      have hKb : (K:ℝ) ≤ (r:ℝ)/(M:ℝ)+1 := by
        rw [div_add' _ _ _ (ne_of_gt hM₀), le_div_iff₀ hM₀]
        linarith [hK₂]
      have hrP : (r:ℝ)/(M:ℝ) ≤ P := by
        rw [div_le_iff₀ hM₀]
        calc (r:ℝ) ≤ (M:ℝ)*P := hrb
          _ = P*(M:ℝ) := by ring
      have hs₀ : (0:ℝ) ≤ (s:ℝ) := by positivity
      calc ((K*s:ℕ):ℝ) = (K:ℝ)*(s:ℝ) := by push_cast; ring
        _ ≤ ((r:ℝ)/(M:ℝ)+1)*(s:ℝ) := mul_le_mul_of_nonneg_right hKb hs₀
        _ ≤ (P+1)*(s:ℝ) := by nlinarith [hrP, hs₀]
        _ ≤ (M:ℝ)*(1+(s:ℝ)/(M:ℝ))^(j+1+1) := by
          rw [pow_succ, ← hP]
          have ht : (M:ℝ)*(P*(1+(s:ℝ)/(M:ℝ))) =
              (M:ℝ)*P + P*(s:ℝ) := by field_simp
          rw [ht]
          nlinarith [hMP, hs₀]

private theorem omegaMM_le_of_blockDiagF (F : Type u) [Field F]
    {A B C M s : ℕ} (hV : 2 ≤ A*B*C) (hM : 1 ≤ M)
    (hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) s) :
    omegaMM F ≤ 3*Real.log (1+(s:ℝ)/(M:ℝ)) /
      Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) := by
  have hA : 1 ≤ A := Nat.pos_of_ne_zero (fun h => by simp [h] at hV)
  have hB : 1 ≤ B := Nat.pos_of_ne_zero (fun h => by simp [h] at hV)
  have hC : 1 ≤ C := Nat.pos_of_ne_zero (fun h => by simp [h] at hV)
  have hVR : (2:ℝ) ≤ (A:ℝ)*(B:ℝ)*(C:ℝ) := by exact_mod_cast hV
  set W : ℝ := Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) with hWdef
  have hW : 0 < W := Real.log_pos (by linarith)
  have hM₀ : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  set L : ℝ := Real.log (1+(s:ℝ)/(M:ℝ)) with hLdef
  have key : ∀ j : ℕ, omegaMM F ≤ 3*L/W + 3*Real.log (M:ℝ)/(((j:ℝ)+1)*W) := by
    intro j
    obtain ⟨r, hr, hrb⟩ := rankLE_pow_of_blockDiagF F hM hblk j
    have hrpos : 1 ≤ r := one_le_of_rankLE_matMulF F (Nat.one_le_pow _ _ hA)
      (Nat.one_le_pow _ _ hB) (Nat.one_le_pow _ _ hC) hr
    have hcube : 2 ≤ A^(j+1)*B^(j+1)*C^(j+1) := by
      calc 2 ≤ (A*B*C)^(j+1) := le_trans hV (Nat.le_self_pow (by omega) _)
        _ = A^(j+1)*B^(j+1)*C^(j+1) := by ring
    have hmain := omegaMM_le_logb_rect (R := F) hcube hr
    have hbase : ((A^(j+1):ℕ):ℝ)*((B^(j+1):ℕ):ℝ)*((C^(j+1):ℕ):ℝ) =
        ((A:ℝ)*(B:ℝ)*(C:ℝ))^(j+1) := by push_cast; ring
    rw [Real.logb, hbase, Real.log_pow] at hmain
    have hjW : (0:ℝ) < ((j:ℝ)+1)*W := by positivity
    have hlogr : Real.log (r:ℝ) ≤ Real.log (M:ℝ)+((j:ℝ)+1)*L := by
      have ht : Real.log (r:ℝ) ≤ Real.log ((M:ℝ)*(1+(s:ℝ)/(M:ℝ))^(j+1)) :=
        Real.log_le_log (by exact_mod_cast hrpos) hrb
      rw [Real.log_mul (ne_of_gt hM₀) (by positivity), Real.log_pow] at ht
      push_cast at ht
      linarith
    have hdiv : ∀ x y : ℝ, x ≤ y → x/(((j:ℝ)+1)*W) ≤ y/(((j:ℝ)+1)*W) := by
      intro x y hxy
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.mpr hjW))
    have hmain' : omegaMM F ≤ 3*Real.log (r:ℝ)/(((j:ℝ)+1)*W) := by
      refine le_trans hmain (le_of_eq ?_)
      push_cast
      ring
    have hnum : 3*Real.log (r:ℝ) ≤ 3*(((j:ℝ)+1)*L)+3*Real.log (M:ℝ) := by
      linarith [hlogr]
    have heq : (3*(((j:ℝ)+1)*L)+3*Real.log (M:ℝ))/(((j:ℝ)+1)*W) =
        3*L/W + 3*Real.log (M:ℝ)/(((j:ℝ)+1)*W) := by field_simp
    calc omegaMM F ≤ 3*Real.log (r:ℝ)/(((j:ℝ)+1)*W) := hmain'
      _ ≤ (3*(((j:ℝ)+1)*L)+3*Real.log (M:ℝ))/(((j:ℝ)+1)*W) := hdiv _ _ hnum
      _ = _ := heq
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (3*Real.log (M:ℝ)/(ε*W))
  refine le_trans (key n) ?_
  have hnW : (0:ℝ) < ((n:ℝ)+1)*W := by positivity
  have hεW : (0:ℝ) < ε*W := by positivity
  rw [div_lt_iff₀ hεW] at hn
  have hfin : 3*Real.log (M:ℝ)/(((n:ℝ)+1)*W) ≤ ε := by
    rw [div_le_iff₀ hnW]
    nlinarith [hn, hW.le, hε.le]
  linarith [hfin]

set_option maxHeartbeats 4000000 in
theorem asymptotic_sum (F : Type u) [Field F]
    (a b c : ℕ → ℕ) (r s : ℕ) (τ : ℝ)
    (hs : 1 ≤ s) (hV : ∀ i, i < s → 2 ≤ a i*b i*c i) (hτ : 0 ≤ τ)
    (hdeg : Degenerates F (Tensor3.identity F r) (mmDSumF F a b c s))
    (hsum : (r:ℝ) ≤ ∑ i ∈ Finset.range s, (a i*b i*c i:ℝ)^(τ/3)) :
  omegaMM F ≤ τ := by
  classical
  obtain ⟨s', rfl⟩ : ∃ s', s = s'+1 := ⟨s-1, by omega⟩
  obtain ⟨D, hD⟩ := CW90Eight.exists_degeneratesAt hdeg
  have hpoly : PolyDegeneratesAt F D (Tensor3.identity F r) (mmDSumF F a b c (s'+1)) := by
    exact hD
  set q : ℕ → ℝ := fun i => (a i*b i*c i:ℝ)^(τ/3) with hqdef
  have hq : ∀ i, 0 ≤ q i := fun i => Real.rpow_nonneg (by positivity) _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hτ₃ : 0 ≤ τ/3 := by linarith
  set S : ℝ := ((s'+1:ℕ):ℝ) with hSdef
  have hS₁ : (1:ℝ) ≤ S := by
    rw [hSdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have main : ∀ N : ℕ, 1 ≤ N →
      omegaMM F ≤ τ + 3*(2*Real.log (((N*D+2:ℕ):ℝ)) +
        S*Real.log (((N+1:ℕ):ℝ))) / ((N:ℝ)*Real.log 2) := by
    intro N hN
    have hpowPoly := polyDegeneratesAt_tpow_identity F D r
      (mmDSumF F a b c (s'+1)) hpoly N
    have hpowAt : CW90Eight.DegeneratesAt F (N*D) (Tensor3.identity F (r^N))
        (tpow (mmDSumF F a b c (s'+1)) N) := by
      exact hpowPoly
    have hRankTpow : RankLE (tpow (mmDSumF F a b c (s'+1)) N)
        ((N*D+1)^2*r^N) := by
      have ht := rankLE_of_degeneratesAt_identity F (N*D) (r^N)
        (tpow (mmDSumF F a b c (s'+1)) N) hpowAt
      simpa [mul_comm] using ht
    obtain ⟨m, hmsum, hmdom⟩ := exists_dominant_type_gen q hq s' N
    set M : ℕ := mmult m (s'+1) with hMdef
    have hM : 1 ≤ M := one_le_mmult m (s'+1)
    set A : ℕ := ∏ i ∈ Finset.range (s'+1), a i^m i with hAdef
    set B : ℕ := ∏ i ∈ Finset.range (s'+1), b i^m i with hBdef
    set C : ℕ := ∏ i ∈ Finset.range (s'+1), c i^m i with hCdef
    set srk : ℕ := (N*D+1)^2*r^N with hsrkdef
    have hblk : RankLE (blockDiag (Fin M) (Tensor3.matMul (R := F) A B C)) srk := by
      refine OmegaBound.RankLE.mono ?_ hRankTpow
      have hd := blockDiag_le_tpow_mmDSumF F a b c (s'+1) m
      rwa [hmsum] at hd
    have hABC : A*B*C = ∏ i ∈ Finset.range (s'+1), (a i*b i*c i)^m i := by
      rw [hAdef, hBdef, hCdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [← mul_pow, ← mul_pow]
    have hpow2 : 2^N ≤ A*B*C := by
      rw [hABC, ← hmsum]
      calc 2^(∑ i ∈ Finset.range (s'+1), m i) =
            ∏ i ∈ Finset.range (s'+1), 2^m i :=
              (Finset.prod_pow_eq_pow_sum _ _ _).symm
        _ ≤ ∏ i ∈ Finset.range (s'+1), (a i*b i*c i)^m i :=
          Finset.prod_le_prod' fun i hi =>
            Nat.pow_le_pow_left (hV i (Finset.mem_range.mp hi)) _
    have hV₂ : 2 ≤ A*B*C :=
      le_trans (by simpa using Nat.pow_le_pow_right (by norm_num) hN) hpow2
    have hVR : (2:ℝ) ≤ (A:ℝ)*(B:ℝ)*(C:ℝ) := by exact_mod_cast hV₂
    have hlogV : 0 < Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) := Real.log_pos (by linarith)
    have homega := omegaMM_le_of_blockDiagF F hV₂ hM hblk
    have hVq : ((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) =
        ∏ i ∈ Finset.range (s'+1), q i^m i := by
      have h₁ : (A:ℝ)*(B:ℝ)*(C:ℝ) =
          ∏ i ∈ Finset.range (s'+1), ((a i*b i*c i:ℕ):ℝ)^m i := by
        have h₂ := congrArg (fun n : ℕ => (n:ℝ)) hABC
        push_cast at h₂ ⊢
        exact h₂
      rw [h₁, ← Real.finset_prod_rpow _ _ (fun i _ => by positivity) (τ/3)]
      rw [hqdef]
      refine Finset.prod_congr rfl fun i _ => ?_
      have ht := rpow_pow_comm (x := ((a i*b i*c i:ℕ):ℝ))
        (by positivity) (m i) (τ/3)
      push_cast at ht
      push_cast
      exact ht
    have hMq : (∑ i ∈ Finset.range (s'+1), q i)^N / (((N:ℝ)+1)^(s'+1)) ≤
        (M:ℝ)*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) := by
      rw [hVq]
      exact hmdom
    have hrq : (r:ℝ)^N ≤ (∑ i ∈ Finset.range (s'+1), q i)^N :=
      pow_le_pow_left₀ (by positivity) hsum N
    have hMr : (r:ℝ)^N / (((N:ℝ)+1)^(s'+1)) ≤
        (M:ℝ)*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) := by
      refine le_trans ?_ hMq
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hrq (by positivity)
    have hA₁ : 1 ≤ A := Nat.pos_of_ne_zero (fun h => by simp [h] at hV₂)
    have hB₁ : 1 ≤ B := Nat.pos_of_ne_zero (fun h => by simp [h] at hV₂)
    have hC₁ : 1 ≤ C := Nat.pos_of_ne_zero (fun h => by simp [h] at hV₂)
    have hs₁ : 1 ≤ srk := one_le_of_rankLE_matMulF F hA₁ hB₁ hC₁
      (OmegaBound.RankLE.mono (restricts_blockDiag _ (⟨0, hM⟩ : Fin M)) hblk)
    have hrN₁ : 1 ≤ r^N := by
      by_contra h
      push_neg at h
      have hz : r^N = 0 := by omega
      rw [hsrkdef, hz, Nat.mul_zero] at hs₁
      omega
    have hrNR : (1:ℝ) ≤ (r:ℝ)^N := by exact_mod_cast hrN₁
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hVpow : (1:ℝ) ≤ ((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) :=
      Real.one_le_rpow (by linarith) hτ₃
    have hNp : (1:ℝ) ≤ ((N:ℝ)+1)^(s'+1) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
    have hsM : (srk:ℝ)/(M:ℝ) ≤ (((N*D+1:ℕ):ℝ)^2)*
        ((((N:ℝ)+1)^(s'+1))*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3)) := by
      rw [div_le_iff₀ hMpos]
      have hMlb : (r:ℝ)^N ≤ (((N:ℝ)+1)^(s'+1))*
          ((M:ℝ)*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3)) := by
        rw [div_le_iff₀ (by positivity)] at hMr
        linarith [hMr]
      have hscast : (srk:ℝ) = (((N*D+1:ℕ):ℝ)^2)*(r:ℝ)^N := by
        rw [hsrkdef]
        push_cast
        ring
      rw [hscast]
      nlinarith [hMlb, hMpos, hVpow, hrNR, hNp,
        sq_nonneg (((N*D+1:ℕ):ℝ))]
    have hkey : 1+(srk:ℝ)/(M:ℝ) ≤
        ((((N*D+2:ℕ):ℝ)^2)*(((N:ℝ)+1)^(s'+1)))*
          ((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) := by
      have hbase : (1:ℝ) ≤ (((N:ℝ)+1)^(s'+1))*
          ((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) := by
        nlinarith [hVpow, hNp]
      have hK : (((N*D+1:ℕ):ℝ)^2)+1 ≤ (((N*D+2:ℕ):ℝ)^2) := by
        have hx : (0:ℝ) ≤ (N:ℝ)*(D:ℝ) := mul_nonneg (by positivity) (by positivity)
        push_cast
        nlinarith [hx]
      have hbase₀ : 0 ≤ (((N:ℝ)+1)^(s'+1))*
          ((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3) := by positivity
      calc
        1+(srk:ℝ)/(M:ℝ) ≤
            1+(((N*D+1:ℕ):ℝ)^2)*
              ((((N:ℝ)+1)^(s'+1))*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3)) :=
          by linarith [hsM]
        _ ≤ ((((N*D+1:ℕ):ℝ)^2)+1)*
              ((((N:ℝ)+1)^(s'+1))*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3)) := by
          nlinarith [hbase]
        _ ≤ (((N*D+2:ℕ):ℝ)^2)*
              ((((N:ℝ)+1)^(s'+1))*((A:ℝ)*(B:ℝ)*(C:ℝ))^(τ/3)) :=
          mul_le_mul_of_nonneg_right hK hbase₀
        _ = _ := by ring
    have hpos : (0:ℝ) < 1+(srk:ℝ)/(M:ℝ) := by positivity
    have hlogle : Real.log (1+(srk:ℝ)/(M:ℝ)) ≤
        2*Real.log (((N*D+2:ℕ):ℝ)) + S*Real.log (((N+1:ℕ):ℝ)) +
          (τ/3)*Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) := by
      refine le_trans (Real.log_le_log hpos hkey) (le_of_eq ?_)
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_rpow (by linarith)]
      have hcast : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by push_cast; ring
      rw [hcast, hSdef]
      norm_num
    have hE₀ : 0 ≤ 2*Real.log (((N*D+2:ℕ):ℝ)) +
        S*Real.log (((N+1:ℕ):ℝ)) := by
      have h₁ : 0 ≤ Real.log (((N*D+2:ℕ):ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N*D+2))
      have h₂ : 0 ≤ Real.log (((N+1:ℕ):ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N+1))
      nlinarith [h₁, h₂, hS₁]
    have hNlog : (N:ℝ)*Real.log 2 ≤ Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) := by
      have h₁ : ((2:ℝ)^N) ≤ (A:ℝ)*(B:ℝ)*(C:ℝ) := by
        have h₂ : ((2^N:ℕ):ℝ) ≤ ((A*B*C:ℕ):ℝ) := by exact_mod_cast hpow2
        push_cast at h₂
        linarith
      have h₃ := Real.log_le_log (by positivity) h₁
      rwa [Real.log_pow] at h₃
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    calc omegaMM F ≤ 3*Real.log (1+(srk:ℝ)/(M:ℝ)) /
          Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) := homega
      _ ≤ τ + 3*(2*Real.log (((N*D+2:ℕ):ℝ)) +
          S*Real.log (((N+1:ℕ):ℝ))) / ((N:ℝ)*Real.log 2) := by
        set LV : ℝ := Real.log ((A:ℝ)*(B:ℝ)*(C:ℝ)) with hLVdef
        set E : ℝ := 2*Real.log (((N*D+2:ℕ):ℝ)) +
          S*Real.log (((N+1:ℕ):ℝ)) with hEdef
        have hmono : ∀ x y d : ℝ, 0 < d → x ≤ y → x/d ≤ y/d := by
          intro x y d hd hxy
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.mpr hd))
        have step₁ : 3*Real.log (1+(srk:ℝ)/(M:ℝ))/LV ≤ (3*E+τ*LV)/LV :=
          hmono _ _ _ hlogV (by nlinarith [hlogle])
        have step₂ : (3*E+τ*LV)/LV = 3*E/LV+τ := by field_simp
        have step₃ : 3*E/LV ≤ 3*E/((N:ℝ)*Real.log 2) := by
          rw [div_le_div_iff₀ hlogV (by positivity)]
          nlinarith [hE₀, hNlog, hlog2, hNpos]
        rw [step₂] at step₁
        linarith [step₁, step₃]
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set cst : ℝ := 6*(2*Real.sqrt ((D:ℝ)+2)+S*Real.sqrt 2)/Real.log 2 with hcdef
  have hc₀ : 0 ≤ cst := by
    rw [hcdef]
    have ht : 0 ≤ 2*Real.sqrt ((D:ℝ)+2)+S*Real.sqrt 2 := by
      have h₁ := Real.sqrt_nonneg ((D:ℝ)+2)
      have h₂ := Real.sqrt_nonneg (2:ℝ)
      nlinarith [hS₁]
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((cst/ε)^2+1)
  have hn₁ : 1 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n
    nlinarith [sq_nonneg (cst/ε), hn]
  refine le_trans (main n hn₁) ?_
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn₁
  have hn₁R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn₁
  have hb₁ : Real.log (((n*D+2:ℕ):ℝ)) ≤ 2*Real.sqrt (((D:ℝ)+2)*(n:ℝ)) := by
    refine le_trans (log_le_two_sqrt (by push_cast; positivity)) ?_
    have hle : ((n*D+2:ℕ):ℝ) ≤ ((D:ℝ)+2)*(n:ℝ) := by
      push_cast
      nlinarith [hnR, hn₁R, Nat.cast_nonneg (α := ℝ) D]
    have ht := Real.sqrt_le_sqrt hle
    linarith
  have hb₂ : Real.log (((n+1:ℕ):ℝ)) ≤ 2*Real.sqrt (2*(n:ℝ)) := by
    refine le_trans (log_le_two_sqrt (by push_cast; positivity)) ?_
    have hle : ((n+1:ℕ):ℝ) ≤ 2*(n:ℝ) := by push_cast; linarith [hn₁R]
    have ht := Real.sqrt_le_sqrt hle
    linarith
  have hsq₁ : Real.sqrt (((D:ℝ)+2)*(n:ℝ)) =
      Real.sqrt ((D:ℝ)+2)*Real.sqrt (n:ℝ) := Real.sqrt_mul (by positivity) _
  have hsq₂ : Real.sqrt (2*(n:ℝ)) = Real.sqrt 2*Real.sqrt (n:ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hsn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have hfinal : 3*(2*Real.log (((n*D+2:ℕ):ℝ)) +
      S*Real.log (((n+1:ℕ):ℝ))) / ((n:ℝ)*Real.log 2) ≤
      cst/Real.sqrt (n:ℝ) := by
    have hnsq : Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt hnR.le
    have hnum : 2*Real.log (((n*D+2:ℕ):ℝ)) + S*Real.log (((n+1:ℕ):ℝ)) ≤
        2*((2*Real.sqrt ((D:ℝ)+2)+S*Real.sqrt 2)*Real.sqrt (n:ℝ)) := by
      rw [hsq₁] at hb₁
      rw [hsq₂] at hb₂
      nlinarith [hb₁, hb₂, hS₁, Real.sqrt_nonneg (n:ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hnum (le_of_lt hsn)
    have hrw : 2*((2*Real.sqrt ((D:ℝ)+2)+S*Real.sqrt 2)*Real.sqrt (n:ℝ))*
          Real.sqrt (n:ℝ) =
        2*(2*Real.sqrt ((D:ℝ)+2)+S*Real.sqrt 2)*
          (Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)) := by ring
    rw [hrw, hnsq] at hmul
    rw [div_le_div_iff₀ (by positivity) hsn, hcdef]
    field_simp
    linarith [hmul]
  have hcn : cst/Real.sqrt (n:ℝ) ≤ ε := by
    rcases eq_or_lt_of_le hc₀ with hc | hc
    · rw [← hc, zero_div]
      linarith
    · rw [div_le_iff₀ hsn]
      have h₁ : (cst/ε)^2 < (n:ℝ) := by linarith [hn]
      have h₂ : cst/ε < Real.sqrt (n:ℝ) := by
        have h₃ := Real.sqrt_lt_sqrt (by positivity) h₁
        rwa [Real.sqrt_sq (by positivity)] at h₃
      rw [div_lt_iff₀ hε] at h₂
      nlinarith [h₂, hε, hsn]
  linarith [hfinal, hcn]

theorem omegaRect_one (F : Type u) [Field F] : omegaRect F 1 = omegaMM F := by
  unfold omegaRect OmegaBound.omegaMM
  congr 1
  ext τ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n hn => ?_⟩
    convert hC n hn using 1
    funext r
    rw [Real.rpow_one, Nat.ceil_natCast]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n hn => ?_⟩
    convert hC n hn using 1
    funext r
    rw [Real.rpow_one, Nat.ceil_natCast]

end OmegaBound.ADVXXZGeneral
end
