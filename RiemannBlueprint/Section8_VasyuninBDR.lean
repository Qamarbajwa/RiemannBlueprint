import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import RiemannBlueprint.Section5_MobiusMertens

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

/-- Total BDR squared residual functional `E_N(c)` with smooth Gram + cotangent term `Q_cot`. -/
noncomputable def E_BDR (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ) : ℝ :=
  1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
    (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot

/-- Asymptotic cotangent-limit bridge on `A_N`: for any sequence `c_seq N ∈ A_N` (`N ≥ 2`),
`E_BDR (c_seq N) N gamma_E (Q_cot_seq N) → 0` if and only if `Q_cot_seq N → -1`. -/
theorem tendsto_E_BDR_zero_iff_tendsto_Q_cot_neg_one
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD1 : ∀ N, 2 ≤ N → D1 (c_seq N) N = 0)
    (hD0 : ∀ N, 2 ≤ N → D0 (c_seq N) N = 2) :
    Filter.Tendsto (fun N => E_BDR (c_seq N) N gamma_E (Q_cot_seq N)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1)) := by
  have hev : ∀ᶠ N in Filter.atTop,
      E_BDR (c_seq N) N gamma_E (Q_cot_seq N) = 1 + Q_cot_seq N := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun N hN => ?_⟩
    exact affine_bdr_pure_cotangent_identity (c_seq N) N gamma_E (Q_cot_seq N)
      (hD1 N hN) (hD0 N hN)
  rw [Filter.tendsto_congr' hev]
  constructor
  · intro h
    have hsub := h.sub_const (1 : ℝ)
    have heq : (fun N => (1 + Q_cot_seq N) - 1) = Q_cot_seq := by
      ext N; ring
    rw [heq] at hsub
    simpa using hsub
  · intro h
    have hadd := h.const_add (1 : ℝ)
    simpa using hadd

/-- Asymptotic cotangent-limit bridge for `affineLock`: given only `D1 (c_seq N) N = 0` for
`N ≥ 2`, `E_BDR (affineLock (c_seq N) N) N gamma_E (Q_cot_seq N) → 0` iff `Q_cot_seq N → -1`. -/
theorem tendsto_E_BDR_affineLock_zero_iff_tendsto_Q_cot_neg_one
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD1 : ∀ N, 2 ≤ N → D1 (c_seq N) N = 0) :
    Filter.Tendsto (fun N => E_BDR (affineLock (c_seq N) N) N gamma_E (Q_cot_seq N))
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1)) :=
  tendsto_E_BDR_zero_iff_tendsto_Q_cot_neg_one
    (fun N => affineLock (c_seq N) N) Q_cot_seq gamma_E
    (fun N hN => D1_affineLock_eq_zero (c_seq N) N hN (hD1 N hN))
    (fun N hN => D0_affineLock_eq_two (c_seq N) N hN)

/-- Orthogonality on the Nyman-Beurling subspace: for any `c` with `D_N(1) = 0` and any
complex factor `α`, the zero-mode inner product `∑ c_k (α / k)` vanishes. -/
theorem nb_inner_zero_mode_eq_zero (c : ℕ → ℝ) (N : ℕ) (α : ℂ) (hD1 : D1 c N = 0) :
    ∑ k ∈ Finset.Icc 1 N, (c k : ℂ) * (α / (k : ℂ)) = 0 := by
  have hsum : ∑ k ∈ Finset.Icc 1 N, (c k : ℂ) * (α / (k : ℂ)) = α * (D1 c N : ℂ) := by
    unfold D1
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum, hD1, Complex.ofReal_zero, mul_zero]

/-- For `N ≥ 2` and `D_N(1) = 0`, `affineLock c N` preserves zero-mode orthogonality. -/
theorem affineLock_inner_zero_mode_eq_zero (c : ℕ → ℝ) (N : ℕ) (α : ℂ)
    (hN : 2 ≤ N) (hD1 : D1 c N = 0) :
    ∑ k ∈ Finset.Icc 1 N, (affineLock c N k : ℂ) * (α / (k : ℂ)) = 0 :=
  nb_inner_zero_mode_eq_zero (affineLock c N) N α (D1_affineLock_eq_zero c N hN hD1)

/-- Positive residual floor prevents `Q_cot_seq` from converging to `-1` on `A_N`. -/
theorem pos_floor_prevents_Q_cot_tendsto_neg_one
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E δ : ℝ)
    (hδ : 0 < δ)
    (hD1 : ∀ N, 2 ≤ N → D1 (c_seq N) N = 0)
    (hD0 : ∀ N, 2 ≤ N → D0 (c_seq N) N = 2)
    (hfloor : ∀ N, 2 ≤ N → δ ≤ E_BDR (c_seq N) N gamma_E (Q_cot_seq N)) :
    ¬ Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1)) := by
  intro htend
  have hE : Filter.Tendsto (fun N => E_BDR (c_seq N) N gamma_E (Q_cot_seq N))
      Filter.atTop (nhds 0) :=
    (tendsto_E_BDR_zero_iff_tendsto_Q_cot_neg_one c_seq Q_cot_seq gamma_E hD1 hD0).mpr htend
  have hev := Metric.tendsto_atTop.mp hE δ hδ
  rcases hev with ⟨N0, hN0⟩
  have h1 := hN0 (max N0 2) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero, abs_lt] at h1
  have h2 := hfloor (max N0 2) (le_max_right _ _)
  linarith

/-- Conditional Cauchy-Schwarz Cotangent-to-RH Bridge: given the Mellin floor
`∀ ρ, 1/2 < ρ.re → ζ(ρ) = 0 → (2*ρ.re - 1)/‖ρ‖² ≤ E_BDR(affineLock (c_seq N) N)`,
convergence `Q_cot_seq → -1` implies `_root_.RiemannHypothesis`. -/
theorem cotangent_limit_neg_one_implies_rh
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD1 : ∀ N, 2 ≤ N → D1 (c_seq N) N = 0)
    (hcs : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ = 0 →
      ∀ N, 2 ≤ N →
        (2 * ρ.re - 1) / Complex.normSq ρ ≤
          E_BDR (affineLock (c_seq N) N) N gamma_E (Q_cot_seq N))
    (htend : Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis := by
  have h_nofail : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0 := by
    intro ρ hρ_re hρ_zero
    have h_norm_pos : 0 < Complex.normSq ρ := by
      rw [Complex.normSq_pos]
      intro h0
      rw [h0, Complex.zero_re] at hρ_re
      linarith
    have hδ : 0 < (2 * ρ.re - 1) / Complex.normSq ρ :=
      div_pos (by linarith) h_norm_pos
    exact pos_floor_prevents_Q_cot_tendsto_neg_one
      (fun N => affineLock (c_seq N) N) Q_cot_seq gamma_E
      ((2 * ρ.re - 1) / Complex.normSq ρ) hδ
      (fun N hN => D1_affineLock_eq_zero (c_seq N) N hN (hD1 N hN))
      (fun N hN => D0_affineLock_eq_two (c_seq N) N hN)
      (hcs ρ hρ_re hρ_zero) htend
  intro s hs_zero hs_not_triv hs_not_one
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hs_lt | hs_gt
  · have ⟨h_refl_zero, h_refl_gt⟩ :=
      RiemannBlueprint.Section5_MobiusMertens.zeta_zero_reflection
        hs_zero hs_not_triv hs_not_one hs_lt
    exact h_nofail (1 - s) h_refl_gt h_refl_zero
  · exact h_nofail s hs_gt hs_zero

/-- The four exact Clay/BDR boundary conditions at `s ∈ {0, 1}` corresponding to `-1 / ζ(s)`:
`D_N(0) = 2`, `D_N'(0) = -2 ln(2π)`, `D_N(1) = 0`, and `D_N'(1) = -1`. -/
def SatisfiesClayBoundaryConditions (c : ℕ → ℝ) (N : ℕ) : Prop :=
  D0 c N = 2 ∧
  D0_deriv c N = -2 * Real.log (2 * Real.pi) ∧
  D1 c N = 0 ∧
  D1_deriv c N = -1

/-- Under `D_N(1) = 0` and `D_N'(1) = -1`, the linear Vasyunin term `-2 b_N^T c` equals `-2`. -/
theorem linear_term_eq_neg_two_of_clay_boundary (c : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (hD1 : D1 c N = 0) (hD1' : D1_deriv c N = -1) :
    -2 * ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E = -2 := by
  dsimp [bVasyunin]
  rw [b_dot_c_eq_boundary, hD1, hD1']
  ring

/-- Under `D_N(0) = 2`, `D_N(1) = 0`, and `D_N'(1) = -1`, the smooth Vasyunin double sum
equals `+2`. -/
theorem smooth_double_sum_eq_two_of_clay_boundary (c : ℕ → ℝ) (N : ℕ) (gamma_E : ℝ)
    (hD0 : D0 c N = 2) (hD1 : D1 c N = 0) (hD1' : D1_deriv c N = -1) :
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k = 2 := by
  rw [smooth_vasyunin_double_sum_eq_boundary, hD0, hD1, hD1']
  ring

/-- Complete `(1, -2, +2, -1)` Equilibrium Identity (Monograph Corollary 8.4):
whenever `c` satisfies all four Clay/BDR boundary conditions at `N`, each part of
`‖1‖² - 2 b_N^T c + S_N^(smooth)(c) = 1 - 2 + 2 = 1` and `E_BDR = 1 + Q_cot` holds identically. -/
theorem clay_four_part_equilibrium_identity (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ)
    (hc : SatisfiesClayBoundaryConditions c N) :
    (-2 * ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E = -2) ∧
    (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k = 2) ∧
    (1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) = 1) ∧
    (E_BDR c N gamma_E Q_cot = 1 + Q_cot) := by
  rcases hc with ⟨hD0, _, hD1, hD1'⟩
  have hlin := linear_term_eq_neg_two_of_clay_boundary c N gamma_E hD1 hD1'
  have hsm := smooth_double_sum_eq_two_of_clay_boundary c N gamma_E hD0 hD1 hD1'
  refine ⟨hlin, hsm, ?_, ?_⟩
  · linear_combination hlin + hsm
  · unfold E_BDR
    linear_combination hlin + hsm

private theorem sum_four_support_Icc (f : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N)
    (hzero : ∀ k ∈ Finset.Icc 1 N, k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, f k = f 1 + f 2 + f 3 + f 4 := by
  have hsub : ({1, 2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.sum_subset hsub]
  · simp [Finset.sum_insert, add_assoc]
  · intro k hk hnotin
    apply hzero k hk
    · intro hk1; exact hnotin (by simp [hk1])
    · intro hk2; exact hnotin (by simp [hk2])
    · intro hk3; exact hnotin (by simp [hk3])
    · intro hk4; exact hnotin (by simp [hk4])

/-- Non-vanishing of the reduced `4 × 4` boundary determinant numerator `8 ln 2 - 5 ln 3 = ln(256/243)`. -/
theorem delta_log256_243_ne_zero : 8 * Real.log 2 - 5 * Real.log 3 ≠ 0 := by
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h243 : Real.log (243 : ℝ) = 5 * Real.log 3 := by
    rw [show (243 : ℝ) = (3 : ℝ) ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hdiv : Real.log (256 / 243 : ℝ) = Real.log 256 - Real.log 243 :=
    Real.log_div (by norm_num) (by norm_num)
  have hpos : 0 < Real.log (256 / 243 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- Closed-form 4-sparse Rank-4 boundary corrector supported on `{1, 2, 3, 4}`, inverting `U₄ᵀ`
to realize any prescribed boundary tuple `(t0, t0', t1, t1')` at `s ∈ {0, 1}`. -/
noncomputable def w_rank4_corrector (t0 t0' t1 t1' : ℝ) (k : ℕ) : ℝ :=
  let L2 := Real.log 2
  let L3 := Real.log 3
  let Delta := 8 * L2 - 5 * L3
  let w3 := (12 * L2 * (t0 - t1) + 3 * (t0' + 2 * t1')) / Delta
  let w2 := (t0' - 4 * t1' - (L3 / 3) * w3) / L2
  let w4 := (2 * t1' - t0' - (L3 / 3) * w3) / L2
  let w1 := t0 - (w2 + w3 + w4)
  if k = 1 then w1
  else if k = 2 then w2
  else if k = 3 then w3
  else if k = 4 then w4
  else 0

private lemma w_rank4_eval (t0 t0' t1 t1' : ℝ) :
    let L2 := Real.log 2
    let L3 := Real.log 3
    let Delta := 8 * L2 - 5 * L3
    let w3 := (12 * L2 * (t0 - t1) + 3 * (t0' + 2 * t1')) / Delta
    let w2 := (t0' - 4 * t1' - (L3 / 3) * w3) / L2
    let w4 := (2 * t1' - t0' - (L3 / 3) * w3) / L2
    let w1 := t0 - (w2 + w3 + w4)
    w_rank4_corrector t0 t0' t1 t1' 1 = w1 ∧
    w_rank4_corrector t0 t0' t1 t1' 2 = w2 ∧
    w_rank4_corrector t0 t0' t1 t1' 3 = w3 ∧
    w_rank4_corrector t0 t0' t1 t1' 4 = w4 := by
  simp [w_rank4_corrector]

private lemma w_rank4_zero_outside (t0 t0' t1 t1' : ℝ) {k : ℕ}
    (hk1 : k ≠ 1) (hk2 : k ≠ 2) (hk3 : k ≠ 3) (hk4 : k ≠ 4) :
    w_rank4_corrector t0 t0' t1 t1' k = 0 := by
  simp [w_rank4_corrector, hk1, hk2, hk3, hk4]

/-- Exact `D_N(0)` value of `w_rank4_corrector t0 t0' t1 t1'` for all `N ≥ 4`. -/
theorem D0_w_rank4_corrector (t0 t0' t1 t1' : ℝ) (N : ℕ) (hN : 4 ≤ N) :
    D0 (w_rank4_corrector t0 t0' t1 t1') N = t0 := by
  unfold D0
  rw [sum_four_support_Icc _ N hN (fun k _ hk1 hk2 hk3 hk4 =>
    w_rank4_zero_outside t0 t0' t1 t1' hk1 hk2 hk3 hk4)]
  rcases w_rank4_eval t0 t0' t1 t1' with ⟨h1, h2, h3, h4⟩
  rw [h1, h2, h3, h4]
  ring

/-- Exact `D_N'(0)` value of `w_rank4_corrector t0 t0' t1 t1'` for all `N ≥ 4`. -/
theorem D0_deriv_w_rank4_corrector (t0 t0' t1 t1' : ℝ) (N : ℕ) (hN : 4 ≤ N) :
    D0_deriv (w_rank4_corrector t0 t0' t1 t1') N = t0' := by
  unfold D0_deriv
  rw [sum_four_support_Icc _ N hN (fun k _ hk1 hk2 hk3 hk4 => by
    simp [w_rank4_zero_outside t0 t0' t1 t1' hk1 hk2 hk3 hk4])]
  rcases w_rank4_eval t0 t0' t1 t1' with ⟨_, h2, h3, h4⟩
  have hL2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h1 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
  have h4log : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h2log : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  have h3log : Real.log ((3 : ℕ) : ℝ) = Real.log 3 := by norm_num
  rw [h1, h2log, h3log, h4log, mul_zero, zero_add, h2, h3, h4]
  field_simp [hL2_ne]
  ring

/-- Exact `D_N(1)` value of `w_rank4_corrector t0 t0' t1 t1'` for all `N ≥ 4`. -/
theorem D1_w_rank4_corrector (t0 t0' t1 t1' : ℝ) (N : ℕ) (hN : 4 ≤ N) :
    D1 (w_rank4_corrector t0 t0' t1 t1') N = t1 := by
  unfold D1
  rw [sum_four_support_Icc _ N hN (fun k _ hk1 hk2 hk3 hk4 => by
    simp [w_rank4_zero_outside t0 t0' t1 t1' hk1 hk2 hk3 hk4])]
  rcases w_rank4_eval t0 t0' t1 t1' with ⟨h1, h2, h3, h4⟩
  have hL2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hDelta_ne : 8 * Real.log 2 - 5 * Real.log 3 ≠ 0 := delta_log256_243_ne_zero
  set L2 := Real.log 2
  set L3 := Real.log 3
  set w3 := (12 * L2 * (t0 - t1) + 3 * (t0' + 2 * t1')) / (8 * L2 - 5 * L3)
  set w2 := (t0' - 4 * t1' - (L3 / 3) * w3) / L2
  set w4 := (2 * t1' - t0' - (L3 / 3) * w3) / L2
  set w1 := t0 - (w2 + w3 + w4)
  have hw3_mul : w3 * (8 * L2 - 5 * L3) = 12 * L2 * (t0 - t1) + 3 * (t0' + 2 * t1') :=
    div_mul_cancel₀ _ hDelta_ne
  have hw2_mul : w2 * L2 = t0' - 4 * t1' - (L3 / 3) * w3 := div_mul_cancel₀ _ hL2_ne
  have hw4_mul : w4 * L2 = 2 * t1' - t0' - (L3 / 3) * w3 := div_mul_cancel₀ _ hL2_ne
  have h1' : w_rank4_corrector t0 t0' t1 t1' 1 = w1 := h1
  have h2' : w_rank4_corrector t0 t0' t1 t1' 2 = w2 := h2
  have h3' : w_rank4_corrector t0 t0' t1 t1' 3 = w3 := h3
  have h4' : w_rank4_corrector t0 t0' t1 t1' 4 = w4 := h4
  norm_num only
  rw [h1', h2', h3', h4']
  have h12 : 12 * L2 * (w1 + w2 / 2 + w3 / 3 + w4 / 4 - t1) = 0 := by
    have hw1_def : w1 = t0 - (w2 + w3 + w4) := rfl
    rw [hw1_def]
    linear_combination 6 * (-hw2_mul) + 9 * (-hw4_mul) + (-hw3_mul)
  have h12_ne : 12 * L2 ≠ 0 := mul_ne_zero (by norm_num) hL2_ne
  have hsub := (mul_eq_zero.mp h12).resolve_left h12_ne
  linarith

/-- Exact `D_N'(1)` value of `w_rank4_corrector t0 t0' t1 t1'` for all `N ≥ 4`. -/
theorem D1_deriv_w_rank4_corrector (t0 t0' t1 t1' : ℝ) (N : ℕ) (hN : 4 ≤ N) :
    D1_deriv (w_rank4_corrector t0 t0' t1 t1') N = t1' := by
  unfold D1_deriv
  rw [sum_four_support_Icc _ N hN (fun k _ hk1 hk2 hk3 hk4 => by
    simp [w_rank4_zero_outside t0 t0' t1 t1' hk1 hk2 hk3 hk4])]
  rcases w_rank4_eval t0 t0' t1 t1' with ⟨_, h2, h3, h4⟩
  have hL2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h4log : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  norm_num only [Real.log_one]
  rw [h4log, h2, h3, h4]
  field_simp [hL2_ne]
  ring

/-- Explicit Rank-4 boundary-lock projection sending any vector `c` onto the affine Clay/BDR
subspace `SatisfiesClayBoundaryConditions · N` for all `N ≥ 4`. -/
noncomputable def clayRank4Lock (c : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  c k + w_rank4_corrector
    (2 - D0 c N)
    (-2 * Real.log (2 * Real.pi) - D0_deriv c N)
    (-D1 c N)
    (-1 - D1_deriv c N) k

/-- For any vector `c` and `N ≥ 4`, `clayRank4Lock c N` satisfies all four Clay/BDR boundary
conditions `(2, -2 ln(2π), 0, -1)` unconditionally. -/
theorem satisfiesClayBoundaryConditions_clayRank4Lock (c : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N) :
    SatisfiesClayBoundaryConditions (clayRank4Lock c N) N := by
  let corr := w_rank4_corrector
    (2 - D0 c N) (-2 * Real.log (2 * Real.pi) - D0_deriv c N) (-D1 c N) (-1 - D1_deriv c N)
  have hD0_add : D0 (clayRank4Lock c N) N = D0 c N + D0 corr N := by
    unfold D0 clayRank4Lock
    exact Finset.sum_add_distrib
  have hD0'_add : D0_deriv (clayRank4Lock c N) N = D0_deriv c N + D0_deriv corr N := by
    unfold D0_deriv clayRank4Lock
    have hpt : ∀ k ∈ Finset.Icc 1 N, (c k + corr k) * Real.log (k : ℝ) =
        c k * Real.log (k : ℝ) + corr k * Real.log (k : ℝ) := fun k _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    ring
  have hD1_add : D1 (clayRank4Lock c N) N = D1 c N + D1 corr N := by
    unfold D1 clayRank4Lock
    have hpt : ∀ k ∈ Finset.Icc 1 N, (c k + corr k) / (k : ℝ) =
        c k / (k : ℝ) + corr k / (k : ℝ) := fun k _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have hD1'_add : D1_deriv (clayRank4Lock c N) N = D1_deriv c N + D1_deriv corr N := by
    unfold D1_deriv clayRank4Lock
    have hpt : ∀ k ∈ Finset.Icc 1 N, (c k + corr k) * Real.log (k : ℝ) / (k : ℝ) =
        c k * Real.log (k : ℝ) / (k : ℝ) + corr k * Real.log (k : ℝ) / (k : ℝ) := fun k _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD0_add, D0_w_rank4_corrector _ _ _ _ N hN]; ring
  · rw [hD0'_add, D0_deriv_w_rank4_corrector _ _ _ _ N hN]; ring
  · rw [hD1_add, D1_w_rank4_corrector _ _ _ _ N hN]; ring
  · rw [hD1'_add, D1_deriv_w_rank4_corrector _ _ _ _ N hN]; ring

/-- For any vector `c` and `N ≥ 4`, `clayRank4Lock c N` satisfies the exact `(1, -2, +2, -1)`
equilibrium and pure cotangent identity `E_BDR (clayRank4Lock c N) N = 1 + Q_cot`. -/
theorem clayRank4Lock_four_part_equilibrium (c : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N) (gamma_E Q_cot : ℝ) :
    (-2 * ∑ k ∈ Finset.Icc 1 N, clayRank4Lock c N k * bVasyunin k gamma_E = -2) ∧
    (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      clayRank4Lock c N j * clayRank4Lock c N k * GSmooth gamma_E j k = 2) ∧
    (1 - 2 * (∑ k ∈ Finset.Icc 1 N, clayRank4Lock c N k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        clayRank4Lock c N j * clayRank4Lock c N k * GSmooth gamma_E j k) = 1) ∧
    (E_BDR (clayRank4Lock c N) N gamma_E Q_cot = 1 + Q_cot) :=
  clay_four_part_equilibrium_identity (clayRank4Lock c N) N gamma_E Q_cot
    (satisfiesClayBoundaryConditions_clayRank4Lock c N hN)

/-- Asymptotic `(1, -2, +2, -1)` Equilibrium (Monograph Corollary 8.4):
if any unconstrained sequence `c_seq` converges to the four Clay/BDR boundary limits
`(2, -2 ln(2π), 0, -1)` at `s ∈ {0, 1}`, then the linear term tends to `-2`, the smooth Vasyunin
double sum tends to `+2`, and their sum with `‖1‖² = 1` tends to `+1`. -/
theorem tendsto_four_part_equilibrium_of_clay_boundary_limits
    (c_seq : ℕ → (ℕ → ℝ)) (gamma_E : ℝ)
    (hD0 : Filter.Tendsto (fun N => D0 (c_seq N) N) Filter.atTop (nhds 2))
    (hD0' : Filter.Tendsto (fun N => D0_deriv (c_seq N) N) Filter.atTop
      (nhds (-2 * Real.log (2 * Real.pi))))
    (hD1 : Filter.Tendsto (fun N => D1 (c_seq N) N) Filter.atTop (nhds 0))
    (hD1' : Filter.Tendsto (fun N => D1_deriv (c_seq N) N) Filter.atTop (nhds (-1))) :
    Filter.Tendsto (fun N => -2 * ∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E)
        Filter.atTop (nhds (-2)) ∧
    Filter.Tendsto (fun N => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c_seq N j * c_seq N k * GSmooth gamma_E j k) Filter.atTop (nhds 2) ∧
    Filter.Tendsto (fun N => 1 - 2 * (∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c_seq N j * c_seq N k * GSmooth gamma_E j k) Filter.atTop (nhds 1) := by
  have hlin_eq : (fun N => -2 * ∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E) =
      fun N => -2 * ((1 - gamma_E) * D1 (c_seq N) N - D1_deriv (c_seq N) N) := by
    ext N; dsimp [bVasyunin]; rw [b_dot_c_eq_boundary]
  have hlin_tend : Filter.Tendsto
      (fun N => -2 * ∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E)
      Filter.atTop (nhds (-2)) := by
    rw [hlin_eq]
    have h := (hD1.const_mul (1 - gamma_E)).sub hD1' |>.const_mul (-2)
    simpa using h
  have hsm_eq : (fun N => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c_seq N j * c_seq N k * GSmooth gamma_E j k) =
      fun N => (Real.log (2 * Real.pi) - gamma_E) * D0 (c_seq N) N * D1 (c_seq N) N -
        D0 (c_seq N) N * D1_deriv (c_seq N) N + D0_deriv (c_seq N) N * D1 (c_seq N) N -
        (D1 (c_seq N) N) ^ 2 := by
    ext N; exact smooth_vasyunin_double_sum_eq_boundary gamma_E (c_seq N) N
  have hsm_tend : Filter.Tendsto
      (fun N => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c_seq N j * c_seq N k * GSmooth gamma_E j k)
      Filter.atTop (nhds 2) := by
    rw [hsm_eq]
    have h1 := ((hD0.const_mul (Real.log (2 * Real.pi) - gamma_E)).mul hD1)
    have h2 := hD0.mul hD1'
    have h3 := hD0'.mul hD1
    have h4 := hD1.pow 2
    have h := ((h1.sub h2).add h3).sub h4
    simpa using h
  have hcomb_eq : (fun N => 1 - 2 * (∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c_seq N j * c_seq N k * GSmooth gamma_E j k) =
      fun N => 1 + (-2 * ∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E) +
        (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c_seq N j * c_seq N k * GSmooth gamma_E j k) := by
    ext N; ring
  refine ⟨hlin_tend, hsm_tend, ?_⟩
  rw [hcomb_eq]
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hlin_tend).add hsm_tend
  simpa using h

/-- Asymptotic BDR-to-Cotangent Equivalence under the four Clay boundary limits (without
assuming `D1 = 0` or `D0 = 2` at finite `N`): `E_BDR → 0` iff `Q_cot_seq → -1`. -/
theorem tendsto_E_BDR_zero_iff_tendsto_Q_cot_neg_one_of_clay_boundary_limits
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD0 : Filter.Tendsto (fun N => D0 (c_seq N) N) Filter.atTop (nhds 2))
    (hD0' : Filter.Tendsto (fun N => D0_deriv (c_seq N) N) Filter.atTop
      (nhds (-2 * Real.log (2 * Real.pi))))
    (hD1 : Filter.Tendsto (fun N => D1 (c_seq N) N) Filter.atTop (nhds 0))
    (hD1' : Filter.Tendsto (fun N => D1_deriv (c_seq N) N) Filter.atTop (nhds (-1))) :
    Filter.Tendsto (fun N => E_BDR (c_seq N) N gamma_E (Q_cot_seq N)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1)) := by
  have h_smooth := (tendsto_four_part_equilibrium_of_clay_boundary_limits
    c_seq gamma_E hD0 hD0' hD1 hD1').2.2
  let S := fun N => 1 - 2 * (∑ k ∈ Finset.Icc 1 N, c_seq N k * bVasyunin k gamma_E) +
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c_seq N j * c_seq N k * GSmooth gamma_E j k
  have hE_eq : (fun N => E_BDR (c_seq N) N gamma_E (Q_cot_seq N)) = fun N => S N + Q_cot_seq N := by
    ext N; rfl
  constructor
  · intro hE
    rw [hE_eq] at hE
    have hQ : (fun N => (S N + Q_cot_seq N) - S N) = Q_cot_seq := by ext N; ring
    have ht := hE.sub h_smooth
    rw [hQ] at ht
    simpa using ht
  · intro hQ
    rw [hE_eq]
    have ht := h_smooth.add hQ
    simpa using ht

/-- Explicit bilinear cotangent quadratic form `Q_cot(c) = ∑_{j,k=1}^N c_j c_k G_{j,k}^{(cot)}`. -/
def Q_cot_quad (G_cot : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * G_cot j k

/-- Additive Vasyunin Gram matrix decomposition `G_{j,k} = G_{j,k}^{(smooth)} + G_{j,k}^{(cot)}`. -/
noncomputable def GVasyuninDecomp (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ) (j k : ℕ) : ℝ :=
  GSmooth gamma_E j k + G_cot j k

/-- Additive splitting of the full Vasyunin quadratic energy with `GVasyuninDecomp` into
`E_BDR c N gamma_E (Q_cot_quad G_cot c N)`. -/
theorem vasyunin_energy_eq_E_BDR_of_decomp (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ)
    (c : ℕ → ℝ) (N : ℕ) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GVasyuninDecomp gamma_E G_cot j k) =
      E_BDR c N gamma_E (Q_cot_quad G_cot c N) := by
  unfold E_BDR Q_cot_quad GVasyuninDecomp
  have h_split :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (GSmooth gamma_E j k + G_cot j k)) =
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * G_cot j k) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [h_split]
  ring

/-- For any vector `c` and `N ≥ 4`, the full decomposed Vasyunin energy evaluated on
`clayRank4Lock c N` reduces identically to `1 + Q_cot_quad G_cot (clayRank4Lock c N) N`. -/
theorem clayRank4Lock_vasyunin_energy_eq_one_add_Q_cot_quad
    (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, clayRank4Lock c N k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        clayRank4Lock c N j * clayRank4Lock c N k * GVasyuninDecomp gamma_E G_cot j k) =
      1 + Q_cot_quad G_cot (clayRank4Lock c N) N := by
  rw [vasyunin_energy_eq_E_BDR_of_decomp]
  exact (clayRank4Lock_four_part_equilibrium c N hN gamma_E
    (Q_cot_quad G_cot (clayRank4Lock c N) N)).2.2.2

/-- At zero boundary defect `(0, 0, 0, 0)`, `w_rank4_corrector` vanishes identically. -/
theorem w_rank4_corrector_zero (k : ℕ) : w_rank4_corrector 0 0 0 0 k = 0 := by
  unfold w_rank4_corrector
  dsimp only
  split_ifs <;> ring

/-- If the four boundary defect sequences `t0_seq, t0'_seq, t1_seq, t1'_seq` tend to `0`, then
`w_rank4_corrector (t0_seq N) (t0'_seq N) (t1_seq N) (t1'_seq N) k → 0` for every `k : ℕ`. -/
theorem tendsto_w_rank4_corrector_zero (t0_seq t0'_seq t1_seq t1'_seq : ℕ → ℝ)
    (h0 : Filter.Tendsto t0_seq Filter.atTop (nhds 0))
    (h0' : Filter.Tendsto t0'_seq Filter.atTop (nhds 0))
    (h1 : Filter.Tendsto t1_seq Filter.atTop (nhds 0))
    (h1' : Filter.Tendsto t1'_seq Filter.atTop (nhds 0)) (k : ℕ) :
    Filter.Tendsto
      (fun N => w_rank4_corrector (t0_seq N) (t0'_seq N) (t1_seq N) (t1'_seq N) k)
      Filter.atTop (nhds 0) := by
  let L2 := Real.log 2
  let L3 := Real.log 3
  let Delta := 8 * L2 - 5 * L3
  let w3_seq := fun N => (12 * L2 * (t0_seq N - t1_seq N) + 3 * (t0'_seq N + 2 * t1'_seq N)) / Delta
  let w2_seq := fun N => (t0'_seq N - 4 * t1'_seq N - (L3 / 3) * w3_seq N) / L2
  let w4_seq := fun N => (2 * t1'_seq N - t0'_seq N - (L3 / 3) * w3_seq N) / L2
  let w1_seq := fun N => t0_seq N - (w2_seq N + w3_seq N + w4_seq N)
  have hw3 : Filter.Tendsto w3_seq Filter.atTop (nhds 0) := by
    have h := (((h0.sub h1).const_mul (12 * L2)).add
      ((h0'.add (h1'.const_mul 2)).const_mul 3)).div_const Delta
    simpa [w3_seq] using h
  have hw2 : Filter.Tendsto w2_seq Filter.atTop (nhds 0) := by
    have h := ((h0'.sub (h1'.const_mul 4)).sub (hw3.const_mul (L3 / 3))).div_const L2
    simpa [w2_seq] using h
  have hw4 : Filter.Tendsto w4_seq Filter.atTop (nhds 0) := by
    have h := (((h1'.const_mul 2).sub h0').sub (hw3.const_mul (L3 / 3))).div_const L2
    simpa [w4_seq] using h
  have hw1 : Filter.Tendsto w1_seq Filter.atTop (nhds 0) := by
    have h := h0.sub ((hw2.add hw3).add hw4)
    simpa [w1_seq] using h
  unfold w_rank4_corrector
  dsimp only
  split_ifs
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact tendsto_const_nhds

/-- If `c_seq` satisfies the four asymptotic Clay boundary limits `(2, -2 ln(2π), 0, -1)`, then
the Rank-4 projection modification `clayRank4Lock (c_seq N) N k - c_seq N k` tends to `0`
pointwise for every `k : ℕ`. -/
theorem tendsto_clayRank4Lock_sub_self_zero
    (c_seq : ℕ → (ℕ → ℝ))
    (hD0 : Filter.Tendsto (fun N => D0 (c_seq N) N) Filter.atTop (nhds 2))
    (hD0' : Filter.Tendsto (fun N => D0_deriv (c_seq N) N) Filter.atTop
      (nhds (-2 * Real.log (2 * Real.pi))))
    (hD1 : Filter.Tendsto (fun N => D1 (c_seq N) N) Filter.atTop (nhds 0))
    (hD1' : Filter.Tendsto (fun N => D1_deriv (c_seq N) N) Filter.atTop (nhds (-1)))
    (k : ℕ) :
    Filter.Tendsto (fun N => clayRank4Lock (c_seq N) N k - c_seq N k)
      Filter.atTop (nhds 0) := by
  have h_eq : (fun N => clayRank4Lock (c_seq N) N k - c_seq N k) =
      fun N => w_rank4_corrector
        (2 - D0 (c_seq N) N)
        (-2 * Real.log (2 * Real.pi) - D0_deriv (c_seq N) N)
        (-D1 (c_seq N) N)
        (-1 - D1_deriv (c_seq N) N) k := by
    ext N; unfold clayRank4Lock; ring
  rw [h_eq]
  refine tendsto_w_rank4_corrector_zero _ _ _ _ ?_ ?_ ?_ ?_ k
  · simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub hD0
  · simpa using (tendsto_const_nhds (x := -2 * Real.log (2 * Real.pi))).sub hD0'
  · simpa using hD1.neg
  · simpa using (tendsto_const_nhds (x := (-1 : ℝ))).sub hD1'

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
