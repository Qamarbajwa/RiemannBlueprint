import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

end BoundaryFunctionals

end RiemannBlueprint.Section8_VasyuninBDR
