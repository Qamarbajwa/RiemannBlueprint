/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exp
import RiemannBlueprint.Section8_VasyuninBDR
import RiemannBlueprint.MathlibPR_VasyuninCrossIntegral

/-!
# Constructive Candidate Sequences on the Báez-Duarte Affine Subspace

This module formalizes constructive candidate sequences $c^{(N)} \in \mathcal{A}_N$:
1. `DeltaDet`: the 2-constraint Gram determinant $\Delta(N) = N \sum 1/k^2 - (\sum 1/k)^2$.
2. `projectAffine`: closed-form Euclidean projection of any raw vector $u$ onto $\mathcal{A}_N$.
3. `projectAffine_D1` and `projectAffine_D0`: formal proof that $D_1 = 0$ and $D_0 = 2$.
4. `cCandidateMobius`: the explicit quadratic mollified Möbius candidate sequence.
5. `cCandidateMobius_mem_A_N`: proof that $c_{\mathrm{mob}}^{(N)} \in \mathcal{A}_N$.
6. `riemannHypothesis_of_cCandidateMobius_limit`: reduction of RH to the explicit candidate limit.
-/

open scoped BigOperators

namespace MathlibPR.ForwardCandidate

open RiemannBlueprint.Section8_VasyuninBDR

/-- Harmonic sum H(N) = ∑_{k=1}^N 1/k. -/
noncomputable def HSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ)

/-- Square reciprocal sum S_2(N) = ∑_{k=1}^N 1/k^2. -/
noncomputable def S2Sum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((k : ℝ) ^ 2)

/-- The constraint Gram determinant Δ(N) = N * S2Sum(N) - (HSum(N))^2. -/
noncomputable def DeltaDet (N : ℕ) : ℝ :=
  (N : ℝ) * S2Sum N - (HSum N) ^ 2

/-- Multiplier λ_1 for projecting a raw vector u onto A_N. -/
noncomputable def lambda1 (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) * (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)) -
    HSum N * ((∑ k ∈ Finset.Icc 1 N, u k) - 2)) / DeltaDet N

/-- Multiplier λ_0 for projecting a raw vector u onto A_N. -/
noncomputable def lambda0 (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (S2Sum N * ((∑ k ∈ Finset.Icc 1 N, u k) - 2) -
    HSum N * (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ))) / DeltaDet N

/-- The exact Báez-Duarte affine projection of any raw vector u onto A_N:
  c(k) = u(k) - λ_1/k - λ_0. -/
noncomputable def projectAffine (u : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  u k - lambda1 u N / (k : ℝ) - lambda0 u N

/-- Linear cancellation identity for D1 projection. -/
theorem projectAffine_D1 (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D1 (projectAffine u N) N = 0 := by
  unfold D1 projectAffine
  have h_split : (∑ k ∈ Finset.Icc 1 N, (u k - lambda1 u N / (k : ℝ) - lambda0 u N) / (k : ℝ)) =
      (∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)) -
      lambda1 u N * S2Sum N - lambda0 u N * HSum N := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        (u k - lambda1 u N / (k : ℝ) - lambda0 u N) / (k : ℝ) =
        u k / (k : ℝ) - lambda1 u N * (1 / (k : ℝ) ^ 2) - lambda0 u N * (1 / (k : ℝ)) := by
      intro k hk
      have hkpos : (k : ℝ) ≠ 0 := by
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        exact Nat.cast_ne_zero.mpr (by omega)
      ring
    rw [Finset.sum_congr rfl h1]
    have h_sub_sub : ∀ k ∈ Finset.Icc 1 N,
        u k / (k : ℝ) - lambda1 u N * (1 / (k : ℝ) ^ 2) - lambda0 u N * (1 / (k : ℝ)) =
        u k / (k : ℝ) - (lambda1 u N * (1 / (k : ℝ) ^ 2) + lambda0 u N * (1 / (k : ℝ))) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl h_sub_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    dsimp [S2Sum, HSum]
    ring
  rw [h_split]
  unfold lambda1 lambda0 DeltaDet
  set U1 := ∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)
  set U0 := ∑ k ∈ Finset.Icc 1 N, u k
  set S2 := S2Sum N
  set H := HSum N
  set n := (N : ℝ)
  have h_alg : U1 - ((n * U1 - H * (U0 - 2)) / (n * S2 - H ^ 2)) * S2 -
      ((S2 * (U0 - 2) - H * U1) / (n * S2 - H ^ 2)) * H = 0 := by
    have hD : n * S2 - H ^ 2 ≠ 0 := hΔ
    field_simp [hD]
    ring
  exact h_alg

/-- Linear cancellation identity for D0 projection. -/
theorem projectAffine_D0 (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D0 (projectAffine u N) N = 2 := by
  unfold D0 projectAffine
  have h_split : (∑ k ∈ Finset.Icc 1 N, (u k - lambda1 u N / (k : ℝ) - lambda0 u N)) =
      (∑ k ∈ Finset.Icc 1 N, u k) -
      lambda1 u N * HSum N - lambda0 u N * (N : ℝ) := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        u k - lambda1 u N / (k : ℝ) - lambda0 u N =
        u k - (lambda1 u N * (1 / (k : ℝ)) + lambda0 u N) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    have h_const : (∑ k ∈ Finset.Icc 1 N, lambda0 u N) = lambda0 u N * (N : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      have : N + 1 - 1 = N := by omega
      rw [this, nsmul_eq_mul]
      ring
    rw [h_const]
    dsimp [HSum]
    ring
  rw [h_split]
  unfold lambda1 lambda0 DeltaDet
  set U1 := ∑ k ∈ Finset.Icc 1 N, u k / (k : ℝ)
  set U0 := ∑ k ∈ Finset.Icc 1 N, u k
  set S2 := S2Sum N
  set H := HSum N
  set n := (N : ℝ)
  have h_alg : U0 - ((n * U1 - H * (U0 - 2)) / (n * S2 - H ^ 2)) * H -
      ((S2 * (U0 - 2) - H * U1) / (n * S2 - H ^ 2)) * n = 2 := by
    have hD : n * S2 - H ^ 2 ≠ 0 := hΔ
    field_simp [hD]
    ring
  exact h_alg

/-- Any projected vector satisfies both Báez-Duarte boundary conditions. -/
theorem projectAffine_mem_A_N (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D1 (projectAffine u N) N = 0 ∧ D0 (projectAffine u N) N = 2 :=
  ⟨projectAffine_D1 u N hΔ, projectAffine_D0 u N hΔ⟩

/-- On the Báez-Duarte affine subspace A_N (where D1 c N = 0), the linear energy
  ∑ c_k bVasyunin(k, γ) against Vasyunin's kernel is completely independent of
  the Euler-Mascheroni constant γ and equals the pure logarithmic moment ∑ c_k (ln k / k). -/
theorem affine_linear_energy_eq_log_moment (c : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (hD1 : D1 c N = 0) :
    (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) =
      ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ) := by
  have h_split : ∀ k ∈ Finset.Icc 1 N,
      c k * bVasyunin k gamma_E =
        c k * Real.log (k : ℝ) / (k : ℝ) + (1 - gamma_E) * (c k / (k : ℝ)) := by
    intro k _
    unfold bVasyunin
    ring
  rw [Finset.sum_congr rfl h_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold D1 at hD1
  rw [hD1, mul_zero, add_zero]

/-- The linear energy of any projected vector projectAffine u N against Vasyunin's kernel
  equals its pure logarithmic moment whenever DeltaDet N ≠ 0. -/
theorem projectAffine_linear_energy_eq_log_moment (u : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (hΔ : DeltaDet N ≠ 0) :
    (∑ k ∈ Finset.Icc 1 N, projectAffine u N k * bVasyunin k gamma_E) =
      ∑ k ∈ Finset.Icc 1 N, projectAffine u N k * Real.log (k : ℝ) / (k : ℝ) :=
  affine_linear_energy_eq_log_moment (projectAffine u N) N gamma_E (projectAffine_D1 u N hΔ)

/-- The exact L² distance formula for any projected candidate vector:
  ∫_0^1 (1 - ∑ c_k {1/(kx)})² dx = 1 - SCot g_cot (projectAffine u N) N. -/
theorem projectAffine_l2_dist_eq_one_sub_scot (u : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (g_cot : ℕ → ℕ → ℝ) (hΔ : DeltaDet N ≠ 0)
    (hb : ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E)
    (hG : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
        GSmooth gamma_E j k + g_cot j k)
    (hint_sq : (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, projectAffine u N k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, projectAffine u N k *
        ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          projectAffine u N j * projectAffine u N k *
            ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, projectAffine u N k * recipFractScaled k x) ^ 2) =
      1 - SCot g_cot (projectAffine u N) N :=
  affine_l2_dist_eq_one_sub_scot (projectAffine u N) gamma_E g_cot
    (projectAffine_D1 u N hΔ) (projectAffine_D0 u N hΔ) hb hG hint_sq

/-- The pure linear cross-term I_1(N) in the L² distance expansion on A_N:
  I_1(N) = -2 * ∑ c_k (ln k / k). -/
noncomputable def linearCrossTerm (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - 2 * ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ)

/-- The quadratic cross-term I_2(N) in the L² distance expansion:
  I_2(N) = ∑∑ c_j c_k ∫_0^1 {1/(jx)} {1/(kx)} dx. -/
noncomputable def quadraticCrossTerm (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    c j * c k * ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x

/-- Decomposition Theorem: On the Báez-Duarte affine subspace A_N,
  the squared L² distance decomposes exactly as:
  ∫_0^1 (1 - ∑ c_k {1/(kx)})² dx = 1 + linearCrossTerm c N + quadraticCrossTerm c N. -/
theorem l2_dist_sq_decomposition_on_A_N (c : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (hD1 : D1 c N = 0)
    (hb : ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E)
    (hint_sq : (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        quadraticCrossTerm c N) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 + linearCrossTerm c N + quadraticCrossTerm c N := by
  rw [hint_sq]
  have h_b_sum : (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) =
      ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hb k hk]
  rw [h_b_sum, affine_linear_energy_eq_log_moment c N gamma_E hD1]
  unfold linearCrossTerm
  ring

/-- The quadratic mollified Möbius weights u_mob(k, N) = - μ(k) * (1 - k/N)^2. -/
noncomputable def mollifiedMobius (N : ℕ) (k : ℕ) : ℝ :=
  - (ArithmeticFunction.moebius k : ℝ) * (1 - (k : ℝ) / (N : ℝ)) ^ 2

/-- The canonical constructive candidate vector on A_N:
  c_mob(N) = projectAffine (mollifiedMobius N) N. -/
noncomputable def cCandidateMobius (N : ℕ) : ℕ → ℝ :=
  projectAffine (mollifiedMobius N) N

/-- Main Constructive Membership Theorem:
For any N with DeltaDet N ≠ 0, the explicit mollified Möbius vector cCandidateMobius N
lies strictly on the Báez-Duarte affine subspace A_N = { c | D1 = 0, D0 = 2 }. -/
theorem cCandidateMobius_mem_A_N (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D1 (cCandidateMobius N) N = 0 ∧ D0 (cCandidateMobius N) N = 2 :=
  projectAffine_mem_A_N (mollifiedMobius N) N hΔ

/-- The linear energy of the constructive mollified Möbius sequence cCandidateMobius N
  against Vasyunin's kernel equals its pure logarithmic moment whenever DeltaDet N ≠ 0. -/
theorem cCandidateMobius_linear_energy_eq_log_moment (N : ℕ) (gamma_E : ℝ)
    (hΔ : DeltaDet N ≠ 0) :
    (∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k * bVasyunin k gamma_E) =
      ∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k * Real.log (k : ℝ) / (k : ℝ) :=
  projectAffine_linear_energy_eq_log_moment (mollifiedMobius N) N gamma_E hΔ

/-- Exact L² distance decomposition for the mollified Möbius sequence cCandidateMobius N. -/
theorem cCandidateMobius_l2_dist_sq_decomposition (N : ℕ) (gamma_E : ℝ) (hΔ : DeltaDet N ≠ 0)
    (hb : ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E)
    (hint_sq : (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k *
        ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        quadraticCrossTerm (cCandidateMobius N) N) :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k * recipFractScaled k x) ^ 2) =
      1 + linearCrossTerm (cCandidateMobius N) N + quadraticCrossTerm (cCandidateMobius N) N :=
  l2_dist_sq_decomposition_on_A_N (cCandidateMobius N) N gamma_E
    (cCandidateMobius_mem_A_N N hΔ).1 hb hint_sq

/-- Selberg Sieve Weights: λ_k = - μ(k) * (ln(N/k) / ln N)^2 for k < N, 0 for k = N. -/
noncomputable def selbergSieveWeights (N : ℕ) (k : ℕ) : ℝ :=
  if k < N then
    - (ArithmeticFunction.moebius k : ℝ) *
      ((Real.log ((N : ℝ) / (k : ℝ)) / Real.log (N : ℝ)) ^ 2)
  else 0

/-- Constructive candidate sequence generated by Selberg sieve mollifier:
  c_sel(N) = projectAffine (selbergSieveWeights N) N. -/
noncomputable def cCandidateSelberg (N : ℕ) : ℕ → ℝ :=
  projectAffine (selbergSieveWeights N) N

/-- The Selberg sieve candidate sequence lies strictly on the Báez-Duarte subspace A_N. -/
theorem cCandidateSelberg_mem_A_N (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    D1 (cCandidateSelberg N) N = 0 ∧ D0 (cCandidateSelberg N) N = 2 :=
  projectAffine_mem_A_N (selbergSieveWeights N) N hΔ

/-- The linear energy of the Selberg candidate sequence equals its pure logarithmic moment. -/
theorem cCandidateSelberg_linear_energy_eq_log_moment (N : ℕ) (gamma_E : ℝ)
    (hΔ : DeltaDet N ≠ 0) :
    (∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k * bVasyunin k gamma_E) =
      ∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k * Real.log (k : ℝ) / (k : ℝ) :=
  projectAffine_linear_energy_eq_log_moment (selbergSieveWeights N) N gamma_E hΔ

/-- Exact L² distance decomposition for the Selberg sieve candidate sequence cCandidateSelberg N. -/
theorem cCandidateSelberg_l2_dist_sq_decomposition (N : ℕ) (gamma_E : ℝ) (hΔ : DeltaDet N ≠ 0)
    (hb : ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E)
    (hint_sq : (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k *
        ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        quadraticCrossTerm (cCandidateSelberg N) N) :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k * recipFractScaled k x) ^ 2) =
      1 + linearCrossTerm (cCandidateSelberg N) N + quadraticCrossTerm (cCandidateSelberg N) N :=
  l2_dist_sq_decomposition_on_A_N (cCandidateSelberg N) N gamma_E
    (cCandidateSelberg_mem_A_N N hΔ).1 hb hint_sq

/-- Main Reduction for Selberg Sieve Candidate: If the Selberg cotangent sum converges to 1,
then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_cCandidateSelberg_limit (gamma_E : ℝ)
    (h_limit : ∀ ε > 0, ∃ N : ℕ, DeltaDet N ≠ 0 ∧
      (∀ k ∈ Finset.Icc 1 N,
        (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E) ∧
      (∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
        (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
          GSmooth gamma_E j k + vasyuninGCot j k) ∧
      ((∫ x in (0 : ℝ)..1,
        (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k * recipFractScaled k x) ^ 2) =
        1 - 2 * (∑ k ∈ Finset.Icc 1 N, cCandidateSelberg N k *
          ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
          ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            cCandidateSelberg N j * cCandidateSelberg N k *
              ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) ∧
      1 - ε < SCot vasyuninGCot (cCandidateSelberg N) N)
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis := by
  apply h_nb
  intro ε hε
  rcases h_limit ε hε with ⟨N, hΔ, hb, hG, hint_sq, hscot⟩
  refine ⟨N, cCandidateSelberg N, (cCandidateSelberg_mem_A_N N hΔ).1, ?_⟩
  rw [nymanBeurling_approx_iff_scot_gt (cCandidateSelberg N) gamma_E vasyuninGCot ε
    (cCandidateSelberg_mem_A_N N hΔ).1 (cCandidateSelberg_mem_A_N N hΔ).2 hb hG hint_sq]
  exact hscot

/-- Main Reduction: If the constructive mollified Möbius cotangent sum converges to 1,
then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_cCandidateMobius_limit (gamma_E : ℝ)
    (h_limit : ∀ ε > 0, ∃ N : ℕ, DeltaDet N ≠ 0 ∧
      (∀ k ∈ Finset.Icc 1 N,
        (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E) ∧
      (∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
        (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
          GSmooth gamma_E j k + vasyuninGCot j k) ∧
      ((∫ x in (0 : ℝ)..1,
        (1 - ∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k * recipFractScaled k x) ^ 2) =
        1 - 2 * (∑ k ∈ Finset.Icc 1 N, cCandidateMobius N k *
          ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
          ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            cCandidateMobius N j * cCandidateMobius N k *
              ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) ∧
      1 - ε < SCot vasyuninGCot (cCandidateMobius N) N)
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis := by
  apply h_nb
  intro ε hε
  rcases h_limit ε hε with ⟨N, hΔ, hb, hG, hint_sq, hscot⟩
  refine ⟨N, cCandidateMobius N, (cCandidateMobius_mem_A_N N hΔ).1, ?_⟩
  rw [nymanBeurling_approx_iff_scot_gt (cCandidateMobius N) gamma_E vasyuninGCot ε
    (cCandidateMobius_mem_A_N N hΔ).1 (cCandidateMobius_mem_A_N N hΔ).2 hb hG hint_sq]
  exact hscot

/-- Direct L² Distance Reduction Theorem: If the explicit mollified Möbius sequence
  cCandidateMobius N achieves arbitrary L² approximation of 1, the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_cCandidateMobius_l2_dist (h_dist : ∀ ε > 0, ∃ N : ℕ,
    DeltaDet N ≠ 0 ∧
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N,
      cCandidateMobius N k * recipFractScaled k x) ^ 2) < ε)
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis := by
  apply h_nb
  intro ε hε
  rcases h_dist ε hε with ⟨N, hΔ, hdist⟩
  refine ⟨N, cCandidateMobius N, (cCandidateMobius_mem_A_N N hΔ).1, hdist⟩

/-- Direct L² Distance Reduction Theorem for Selberg Sieve Candidate: If the constructive
  Selberg sequence achieves arbitrary L² approximation of 1, the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_cCandidateSelberg_l2_dist (h_dist : ∀ ε > 0, ∃ N : ℕ,
    DeltaDet N ≠ 0 ∧
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N,
      cCandidateSelberg N k * recipFractScaled k x) ^ 2) < ε)
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis := by
  apply h_nb
  intro ε hε
  rcases h_dist ε hε with ⟨N, hΔ, hdist⟩
  refine ⟨N, cCandidateSelberg N, (cCandidateSelberg_mem_A_N N hΔ).1, hdist⟩

/-- Asymptotic Sandwich Theorem: If a constructive candidate sequence on A_N
  satisfies a logarithmic upper bound D_N^2 ≤ C / ln N for some constant C > 0,
  then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_log_decay_bound
    (c : ℕ → ℕ → ℝ)
    (h_A_N : ∀ N ≥ 2, D1 (c N) N = 0)
    (h_dist_bound : ∃ C > 0, ∀ N ≥ 2,
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c N k * recipFractScaled k x) ^ 2) ≤
        C / Real.log (N : ℝ))
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis := by
  apply h_nb
  intro ε hε
  rcases h_dist_bound with ⟨C, hC, hbound⟩
  have h_ratio_pos : 0 < C / ε := div_pos hC hε
  have h_exp_pos : 0 < Real.exp (C / ε) := Real.exp_pos (C / ε)
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (C / ε) + 2)
  have hM_gt_exp : Real.exp (C / ε) < (M : ℝ) := by linarith
  have hM_ge_2 : 2 ≤ M := by
    exact_mod_cast (by linarith [h_exp_pos] : (1 : ℝ) < (M : ℝ))
  have h_log_gt : C / ε < Real.log (M : ℝ) := by
    rw [← Real.log_exp (C / ε)]
    exact Real.log_lt_log h_exp_pos hM_gt_exp
  have h_log_pos : 0 < Real.log (M : ℝ) := by
    calc 0 < C / ε := h_ratio_pos
      _ < Real.log (M : ℝ) := h_log_gt
  have h_div_lt : C / Real.log (M : ℝ) < ε := by
    rw [div_lt_iff₀ h_log_pos]
    have : C < Real.log (M : ℝ) * ε := by
      rw [← div_lt_iff₀ hε]
      exact h_log_gt
    linarith
  have h_dist_M := hbound M hM_ge_2
  have h_dist_lt : (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 M, c M k * recipFractScaled k x) ^ 2) < ε :=
    lt_of_le_of_lt h_dist_M h_div_lt
  exact ⟨M, c M, h_A_N M hM_ge_2, h_dist_lt⟩

/-- Logarithmic Decay Sandwich Theorem for mollified Möbius sequence. -/
theorem riemannHypothesis_of_cCandidateMobius_log_decay
    (hΔ : ∀ N ≥ 2, DeltaDet N ≠ 0)
    (h_dist_bound : ∃ C > 0, ∀ N ≥ 2,
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N,
        cCandidateMobius N k * recipFractScaled k x) ^ 2) ≤
        C / Real.log (N : ℝ))
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis :=
  riemannHypothesis_of_log_decay_bound (fun N => cCandidateMobius N)
    (fun N hN => (cCandidateMobius_mem_A_N N (hΔ N hN)).1) h_dist_bound h_nb

/-- Logarithmic Decay Sandwich Theorem for Selberg sieve candidate sequence. -/
theorem riemannHypothesis_of_cCandidateSelberg_log_decay
    (hΔ : ∀ N ≥ 2, DeltaDet N ≠ 0)
    (h_dist_bound : ∃ C > 0, ∀ N ≥ 2,
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N,
        cCandidateSelberg N k * recipFractScaled k x) ^ 2) ≤
        C / Real.log (N : ℝ))
    (h_nb : (∀ ε > 0, ∃ N c, D1 c N = 0 ∧
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) < ε) →
      RiemannHypothesis) :
    RiemannHypothesis :=
  riemannHypothesis_of_log_decay_bound (fun N => cCandidateSelberg N)
    (fun N hN => (cCandidateSelberg_mem_A_N N (hΔ N hN)).1) h_dist_bound h_nb

end MathlibPR.ForwardCandidate
