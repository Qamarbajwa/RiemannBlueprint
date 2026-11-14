import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Section 8: Rank-4 Boundary-Dirichlet Reduction (BDR) of the Smooth Vasyunin Kernel
Unconditional, axiom-free formalization in Lean 4 (0 sorries, 0 custom axioms):
- Defines the finite Dirichlet boundary functionals `D0`, `D0_deriv`, `D1`, `D1_deriv` on `[1, N]`.
- Proves exact Rank-4 factorization `GSmooth_eq_rank4` of the smooth Vasyunin kernel `GSmooth`.
- Proves the linear projection collapse `b_dot_c_eq_boundary`.
- Proves the double-sum collapse `smooth_vasyunin_double_sum_eq_boundary`.
- Proves the complete unconstrained `full_bdr_distance_identity` (with the verified `-(D1 c N)^2`
  sign) and the constrained Nyman-Beurling collapse `constrained_nb_bdr_collapse`.
-/

set_option linter.style.header false
set_option linter.style.longLine false

namespace RiemannBlueprint.Section8_VasyuninBDR

section BoundaryFunctionals

/-- Finite Dirichlet polynomial evaluation at s = 0: D_N(0) = ∑_{k=1}^N c_k. -/
def D0 (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, c k

/-- Finite Dirichlet derivative at s = 0: D_N'(0) = - ∑_{k=1}^N c_k ln k. -/
noncomputable def D0_deriv (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ)

/-- Finite Dirichlet polynomial evaluation at s = 1: D_N(1) = ∑_{k=1}^N c_k / k. -/
noncomputable def D1 (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, c k / (k : ℝ)

/-- Finite Dirichlet derivative at s = 1: D_N'(1) = - ∑_{k=1}^N (c_k ln k) / k. -/
noncomputable def D1_deriv (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ)

/-- Basis vector e_k = 1 for the Rank-4 outer-product expansion. -/
def vecE (_k : ℕ) : ℝ := 1

/-- Basis vector l_k = ln k for the Rank-4 outer-product expansion. -/
noncomputable def vecL (k : ℕ) : ℝ := Real.log (k : ℝ)

/-- Basis vector h_k = 1 / k for the Rank-4 outer-product expansion. -/
noncomputable def vecH (k : ℕ) : ℝ := (k : ℝ)⁻¹

/-- Basis vector m_k = (ln k) / k for the Rank-4 outer-product expansion. -/
noncomputable def vecM (k : ℕ) : ℝ := (k : ℝ)⁻¹ * Real.log (k : ℝ)

/-- Smooth Vasyunin kernel G_{j,k}^{(smooth)}. -/
noncomputable def GSmooth (gamma_E : ℝ) (j k : ℕ) : ℝ :=
  ((Real.log (2 * Real.pi) - gamma_E) * ((j : ℝ) + (k : ℝ)) +
   ((j : ℝ) - (k : ℝ)) * Real.log ((k : ℝ) / (j : ℝ)) - 2) / (2 * (j : ℝ) * (k : ℝ))

/-- Explicit Rank-4 symmetric outer-product representation of G_{j,k}^{(smooth)}. -/
noncomputable def GSmoothRank4 (gamma_E : ℝ) (j k : ℕ) : ℝ :=
  ((Real.log (2 * Real.pi) - gamma_E) / 2) * (vecE j * vecH k + vecH j * vecE k) +
  (1 / 2) * (vecE j * vecM k + vecM j * vecE k) -
  (1 / 2) * (vecL j * vecH k + vecH j * vecL k) -
  vecH j * vecH k

/-- Lemma 8.1 (Pointwise Rank-4 Kernel Factorization):
For all j, k ≥ 1, G_{j,k}^{(smooth)} equals the explicit Rank-4 outer product `GSmoothRank4`. -/
theorem GSmooth_eq_rank4 (gamma_E : ℝ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    GSmooth gamma_E j k = GSmoothRank4 gamma_E j k := by
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth, GSmoothRank4, vecE, vecL, vecH, vecM]
  rw [Real.log_div hk_ne hj_ne]
  field_simp [hj_ne, hk_ne]
  ring

/-- Lemma 8.2 (Linear Target Projection Collapse):
The BNBD inner-product sum ∑ c_k (ln k + 1 - γ) / k collapses to (1 - γ) D_N(1) - D_N'(1). -/
theorem b_dot_c_eq_boundary (gamma_E : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * ((Real.log (k : ℝ) + 1 - gamma_E) / (k : ℝ)) =
      (1 - gamma_E) * D1 c N - D1_deriv c N := by
  have h_pt : ∀ k ∈ Finset.Icc 1 N,
      c k * ((Real.log (k : ℝ) + 1 - gamma_E) / (k : ℝ)) =
      (1 - gamma_E) * (c k / (k : ℝ)) + c k * Real.log (k : ℝ) / (k : ℝ) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl h_pt, Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp [D1, D1_deriv]
  ring

private lemma const_mul_double_sum (s : Finset ℕ) (a : ℝ) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ s, ∑ k ∈ s, a * F j k = a * ∑ j ∈ s, ∑ k ∈ s, F j k := by
  simp only [← Finset.mul_sum]

private lemma outer_double_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ j ∈ s, ∑ k ∈ s, f j * g k = (∑ j ∈ s, f j) * (∑ k ∈ s, g k) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

private lemma sum_c_vecE (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * vecE k = D0 c N := by
  dsimp [vecE, D0]
  simp only [mul_one]

private lemma sum_c_vecL (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * vecL k = - D0_deriv c N := by
  dsimp [vecL, D0_deriv]
  ring

private lemma sum_c_vecH (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * vecH k = D1 c N := by
  dsimp [vecH, D1]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

private lemma sum_c_vecM (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * vecM k = - D1_deriv c N := by
  have h : ∑ k ∈ Finset.Icc 1 N, c k * vecM k =
      ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp [vecM]
    ring
  rw [h]
  dsimp [D1_deriv]
  ring

/-- Theorem 8.3 (Double-Sum Rank-4 Boundary Collapse):
The O(N^2) smooth Vasyunin quadratic form collapses identically to critical-strip boundary
evaluations of D_N(s) and D_N'(s) at s = 0 and s = 1. -/
theorem smooth_vasyunin_double_sum_eq_boundary (gamma_E : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k =
      (Real.log (2 * Real.pi) - gamma_E) * D0 c N * D1 c N -
      D0 c N * D1_deriv c N + D0_deriv c N * D1 c N - (D1 c N) ^ 2 := by
  have h_sum : ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k =
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (((Real.log (2 * Real.pi) - gamma_E) / 2) *
            ((c j * vecE j) * (c k * vecH k) + (c j * vecH j) * (c k * vecE k)) +
         (1 / 2) *
            ((c j * vecE j) * (c k * vecM k) + (c j * vecM j) * (c k * vecE k)) -
         (1 / 2) *
            ((c j * vecL j) * (c k * vecH k) + (c j * vecH j) * (c k * vecL k)) -
         (c j * vecH j) * (c k * vecH k)) := by
    refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => ?_))
    have hj_pos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    rw [GSmooth_eq_rank4 gamma_E hj_pos hk_pos]
    dsimp [GSmoothRank4]
    ring
  rw [h_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, const_mul_double_sum]
  simp_rw [outer_double_sum, sum_c_vecE, sum_c_vecL, sum_c_vecH, sum_c_vecM]
  ring

/-- Theorem 8.4 (Complete Unconstrained Boundary-Dirichlet Distance Identity):
Exact decomposition of the BNBD squared L^2 distance with verified -(D_N(1))^2 sign. -/
theorem full_bdr_distance_identity (gamma_E Q_cot : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ((Real.log (k : ℝ) + 1 - gamma_E) / (k : ℝ))) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot =
    1 - 2 * (1 - gamma_E) * D1 c N - (D1 c N) ^ 2 + 2 * D1_deriv c N +
      D0 c N * ((Real.log (2 * Real.pi) - gamma_E) * D1 c N - D1_deriv c N) +
      D0_deriv c N * D1 c N + Q_cot := by
  rw [b_dot_c_eq_boundary, smooth_vasyunin_double_sum_eq_boundary]
  ring

/-- Corollary 8.5 (Constrained Nyman-Beurling Boundary Collapse):
When D_N(1) = ∑ c_k / k = 0, five smooth boundary terms vanish identically. -/
theorem constrained_nb_bdr_collapse (gamma_E Q_cot : ℝ) (c : ℕ → ℝ) (N : ℕ)
    (hD1 : D1 c N = 0) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ((Real.log (k : ℝ) + 1 - gamma_E) / (k : ℝ))) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot =
    1 + (2 - D0 c N) * D1_deriv c N + Q_cot := by
  rw [full_bdr_distance_identity, hD1]
  ring

/-- Linear Vasyunin RHS coefficient b_k = (log k + 1 - γ) / k. -/
noncomputable def bVasyunin (k : ℕ) (gamma_E : ℝ) : ℝ :=
  (Real.log (k : ℝ) + 1 - gamma_E) / (k : ℝ)

/-- Theorem 8.6 (Boundary-Locked Affine Pure Cotangent Equivalence on A_N):
When both D_N(1) = ∑ c_k / k = 0 and D_N(0) = ∑ c_k = 2 hold, the exact
squared L^2 distance reduces unconditionally to 1 + Q_cot with zero smooth
or logarithmic boundary terms. -/
theorem affine_bdr_pure_cotangent_identity (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot =
      1 + Q_cot := by
  dsimp [bVasyunin]
  rw [constrained_nb_bdr_collapse gamma_E Q_cot c N hD1, hD0]
  ring

/-- 2-sparse boundary corrector w^{(N)} supported on {1, N} for N ≥ 2:
w_1 = -1/(N - 1), w_N = N/(N - 1), and 0 otherwise. -/
noncomputable def w_corrector (N k : ℕ) : ℝ :=
  if k = 1 then -1 / ((N : ℝ) - 1)
  else if k = N then (N : ℝ) / ((N : ℝ) - 1)
  else 0

private theorem sum_pair_support_Icc (f : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (hzero : ∀ k ∈ Finset.Icc 1 N, k ≠ 1 → k ≠ N → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, f k = f 1 + f N := by
  have hsub : ({1, N} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · rw [Finset.mem_singleton.mp hk']
      exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have h1N : (1 : ℕ) ≠ N := by omega
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_pair h1N
  · intro k hk hnotin
    apply hzero k hk
    · intro hk1
      exact hnotin (by simp [hk1])
    · intro hkN
      exact hnotin (by simp [hkN])

/-- The 2-sparse corrector shifts D_N(0) by exactly 1 for all N ≥ 2. -/
theorem D0_w_corrector_eq_one (N : ℕ) (hN : 2 ≤ N) : D0 (w_corrector N) N = 1 := by
  unfold D0
  rw [sum_pair_support_Icc _ N hN]
  · have hNm1 : (N : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have h1N : (1 : ℕ) ≠ N := by omega
    simp only [w_corrector, ↓reduceIte, h1N.symm]
    field_simp [hNm1]
    ring
  · intro k _ hk1 hkN
    simp [w_corrector, hk1, hkN]

/-- The 2-sparse corrector preserves the Nyman-Beurling constraint D_N(1) = 0 for all N ≥ 2. -/
theorem D1_w_corrector_eq_zero (N : ℕ) (hN : 2 ≤ N) : D1 (w_corrector N) N = 0 := by
  unfold D1
  rw [sum_pair_support_Icc _ N hN]
  · have hN0 : (N : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hNm1 : (N : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have h1N : (1 : ℕ) ≠ N := by omega
    simp only [w_corrector, ↓reduceIte, h1N.symm]
    field_simp [hN0, hNm1]
    ring
  · intro k _ hk1 hkN
    simp [w_corrector, hk1, hkN]

/-- Affine boundary-lock projection c ↦ c + (2 - D_N(0)) w^{(N)} onto A_N. -/
noncomputable def affineLock (c : ℕ → ℝ) (N k : ℕ) : ℝ :=
  c k + (2 - D0 c N) * w_corrector N k

/-- For any vector c and N ≥ 2, the affineLock projection satisfies D_N(0) = 2. -/
theorem D0_affineLock_eq_two (c : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    D0 (affineLock c N) N = 2 := by
  unfold D0 affineLock
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change D0 c N + (2 - D0 c N) * D0 (w_corrector N) N = 2
  rw [D0_w_corrector_eq_one N hN]
  ring

/-- For any Nyman-Beurling constrained vector c (D_N(1) = 0) and N ≥ 2,
the affineLock projection preserves D_N(1) = 0. -/
theorem D1_affineLock_eq_zero (c : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) (hD1 : D1 c N = 0) :
    D1 (affineLock c N) N = 0 := by
  unfold D1 affineLock
  have hadd :
      ∑ k ∈ Finset.Icc 1 N, (c k + (2 - D0 c N) * w_corrector N k) / (k : ℝ) =
        D1 c N + (2 - D0 c N) * D1 (w_corrector N) N := by
    unfold D1
    simp_rw [add_div, Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum]
  rw [hadd, hD1, D1_w_corrector_eq_zero N hN]
  ring

/-- Variational lower bound on the boundary-locked subspace `A_N`:
if the full squared residual on `c ∈ A_N` is nonnegative, then `Q_cot ≥ -1`. -/
theorem cotangent_ge_neg_one_of_nonneg_residual (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2)
    (hnonneg : 0 ≤ 1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot) :
    -1 ≤ Q_cot := by
  have hid := affine_bdr_pure_cotangent_identity c N gamma_E Q_cot hD1 hD0
  linarith

/-- For any Nyman-Beurling constrained vector `c` (`D_N(1) = 0`) and `N ≥ 2`,
the affine-locked projection `affineLock c N` satisfies the pure cotangent identity
`E_N(affineLock c N) = 1 + Q_cot` unconditionally. -/
theorem affineLock_pure_cotangent_identity (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ)
    (hN : 2 ≤ N) (hD1 : D1 c N = 0) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, affineLock c N k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        affineLock c N j * affineLock c N k * GSmooth gamma_E j k) + Q_cot =
      1 + Q_cot :=
  affine_bdr_pure_cotangent_identity (affineLock c N) N gamma_E Q_cot
    (D1_affineLock_eq_zero c N hN hD1) (D0_affineLock_eq_two c N hN)

end BoundaryFunctionals

section Rank4AndL2Calculus

open intervalIntegral Matrix

/-- The `4 × 4` leading principal basis block `U₄` evaluated on `k ∈ {1, 2, 3, 4}`. -/
noncomputable def U4 : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 1, 0],
    ![1, Real.log 2, 1 / 2, Real.log 2 / 2],
    ![1, Real.log 3, 1 / 3, Real.log 3 / 3],
    ![1, Real.log 4, 1 / 4, Real.log 4 / 4]]

private lemma sa_00 : Fin.succAbove (0 : Fin 4) 0 = 1 := by decide
private lemma sa_01 : Fin.succAbove (0 : Fin 4) 1 = 2 := by decide
private lemma sa_02 : Fin.succAbove (0 : Fin 4) 2 = 3 := by decide
private lemma sa_10 : Fin.succAbove (1 : Fin 4) 0 = 0 := by decide
private lemma sa_11 : Fin.succAbove (1 : Fin 4) 1 = 2 := by decide
private lemma sa_12 : Fin.succAbove (1 : Fin 4) 2 = 3 := by decide
private lemma sa_20 : Fin.succAbove (2 : Fin 4) 0 = 0 := by decide
private lemma sa_21 : Fin.succAbove (2 : Fin 4) 1 = 1 := by decide
private lemma sa_22 : Fin.succAbove (2 : Fin 4) 2 = 3 := by decide
private lemma sa_30 : Fin.succAbove (3 : Fin 4) 0 = 0 := by decide
private lemma sa_31 : Fin.succAbove (3 : Fin 4) 1 = 1 := by decide
private lemma sa_32 : Fin.succAbove (3 : Fin 4) 2 = 2 := by decide

/-- Exact closed-form determinant `det U₄ = (ln 2 / 24) * ln (256 / 243)`. -/
theorem det_U4_eq_log_ratio :
    Matrix.det U4 = (Real.log 2 / 24) * Real.log (256 / 243 : ℝ) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  have f2 : Fin.succ (2 : Fin 3) = 3 := rfl
  simp only [f2, sa_00, sa_01, sa_02, sa_10, sa_11, sa_12, sa_20, sa_21, sa_22,
    sa_30, sa_31, sa_32, U4]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h243 : Real.log (243 : ℝ) = 5 * Real.log 3 := by
    rw [show (243 : ℝ) = (3 : ℝ) ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hdiv : Real.log (256 / 243 : ℝ) = Real.log 256 - Real.log 243 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [h4, hdiv, h256, h243]
  ring

/-- Strict positivity `det U₄ > 0`, certifying full column rank 4 for all `N ≥ 4`. -/
theorem det_U4_pos : 0 < Matrix.det U4 := by
  rw [det_U4_eq_log_ratio]
  have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log (256 / 243 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- Unit determinant of `U₄` over `ℝ`. -/
theorem U4_isUnit_det : IsUnit (Matrix.det U4) := det_U4_pos.ne'.isUnit

/-- The symmetric `4 × 4` rank-4 smooth Vasyunin core matrix `M₄(c₀)` with `c₀ = ln(2π) - γ`. -/
noncomputable def M4 (c0 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 0, c0 / 2, 1 / 2],
    ![0, 0, -1 / 2, 0],
    ![c0 / 2, -1 / 2, -1, 0],
    ![1 / 2, 0, 0, 0]]

/-- Exact determinant `det M₄(c₀) = 1 / 16` independent of `c₀ = ln(2π) - γ`. -/
theorem det_M4_eq (c0 : ℝ) : Matrix.det (M4 c0) = 1 / 16 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  have f2 : Fin.succ (2 : Fin 3) = 3 := rfl
  simp only [f2, sa_00, sa_01, sa_02, sa_10, sa_11, sa_12, sa_20, sa_21, sa_22,
    sa_30, sa_31, sa_32, M4]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Strict non-singularity `0 < det M₄(c₀)`. -/
theorem det_M4_pos (c0 : ℝ) : 0 < Matrix.det (M4 c0) := by
  rw [det_M4_eq]; norm_num

/-- Total isotropy of the top-left `2 × 2` block of `M₄` (forcing signature `(2, 2)`). -/
theorem M4_top_left_isotropic (c0 : ℝ) (i j : Fin 2) :
    M4 c0 (Fin.castAdd 2 i) (Fin.castAdd 2 j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp [M4]

/-- Exact `L²(0, 1)` dilation integral `∫_{1/k}^1 (1 / (kx)) dx = (ln k) / k`. -/
theorem intervalIntegral_linear_dilation (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in ((1 : ℝ) / (k : ℝ))..(1 : ℝ), (1 : ℝ) / ((k : ℝ) * x) = Real.log (k : ℝ) / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hk_pos.le
  have h_deriv : ∀ x ∈ Set.uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ),
      HasDerivAt (fun y : ℝ => Real.log y / (k : ℝ)) ((1 : ℝ) / ((k : ℝ) * x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (div_pos one_pos hk_pos) hx.1
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_log hx_pos.ne').div_const (k : ℝ)
  have h_cont : ContinuousOn (fun x : ℝ => (1 : ℝ) / ((k : ℝ) * x))
      (Set.uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (div_pos one_pos hk_pos) hx.1
    exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero hk_pos.ne' hx_pos.ne')).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont.intervalIntegrable
  rw [hftc, Real.log_one, zero_div, zero_sub, one_div, Real.log_inv]
  ring

/-- Exact `L²(0, 1)` dilation energy `∫_{1/k}^1 (1 / (kx))² dx = 1/k - 1/k²`. -/
theorem intervalIntegral_sq_dilation (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in ((1 : ℝ) / (k : ℝ))..(1 : ℝ), ((1 : ℝ) / ((k : ℝ) * x)) ^ 2 =
      1 / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hk_pos.le
  have h_deriv : ∀ x ∈ Set.uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 : ℝ) / ((k : ℝ) ^ 2 * y))
        (((1 : ℝ) / ((k : ℝ) * x)) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (div_pos one_pos hk_pos) hx.1
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx_pos.ne'
    have hconst := hinv.const_mul (-(1 : ℝ) / (k : ℝ) ^ 2)
    have hEq : (fun y : ℝ => (-(1 : ℝ) / (k : ℝ) ^ 2) * y⁻¹) =
        (fun y : ℝ => -(1 : ℝ) / ((k : ℝ) ^ 2 * y)) := by
      funext y; ring
    rw [hEq] at hconst
    convert hconst using 1
    field_simp [hk_pos.ne', hx_pos.ne']
  have h_cont : ContinuousOn (fun x : ℝ => ((1 : ℝ) / ((k : ℝ) * x)) ^ 2)
      (Set.uIcc ((1 : ℝ) / (k : ℝ)) (1 : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (div_pos one_pos hk_pos) hx.1
    exact ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero hk_pos.ne' hx_pos.ne')).pow 2).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont.intervalIntegrable
  rw [hftc]
  field_simp [hk_pos.ne']
  ring

end Rank4AndL2Calculus

end RiemannBlueprint.Section8_VasyuninBDR
