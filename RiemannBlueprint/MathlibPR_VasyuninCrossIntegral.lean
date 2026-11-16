/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RiemannBlueprint.MathlibPR_NymanBeurling
import RiemannBlueprint.MathlibPR_VasyuninIntegral
import RiemannBlueprint.Section8_VasyuninBDR

/-!
# Vasyunin Cross-Integrals, Off-Diagonal Cotangent Sums, and L² BDR Bridge

This file formalizes the analytic cross-integrals and the exact bridge between the continuous
Lebesgue $L^2(0, 1)$ Hilbert space distance and the discrete Rank-4 Boundary-Dirichlet
Reduction (BDR) matrix algebra:
1. Product integrability: `intervalIntegrable_recipFractScaled_mul` proves that
   `recipFractScaled j x * recipFractScaled k x` is interval integrable on any compact interval.
2. Upper sub-interval evaluation: on `(max(1/j, 1/k), 1)`, both `{1/(jx)}` and `{1/(kx)}` have
   zero integer part, yielding `1 / (j * k * max(1/j, 1/k)) - 1 / (j * k)`.
3. Vasyunin cotangent sums: `vasyuninCotSum` and `vasyuninGCot`, proving diagonal vanishing
   `vasyuninGCot k k = 0` and symmetry `vasyuninGCot j k = vasyuninGCot k j`.
4. Smooth kernel properties: `GSmooth_comm` and diagonal reduction `GSmooth_diag`.
5. Full quadratic expansion: `intervalIntegral_sq_sub_sum` expands the Lebesgue $L^2$ norm
   of `1 - ∑ c_k {1/(kx)}` into linear target projections and cross-Gram inner products.
6. Affine $L^2$ pure cotangent bridge: `affine_l2_pure_cotangent_bridge` proves that for any
   $c \in \mathcal{A}_N$ (satisfying $D_1(c, N) = 0$ and $D_0(c, N) = 2$), all smooth and
   logarithmic terms cancel identically, leaving exact pure cotangent residual `1 + Q_cot(c, N)`.
-/

open MeasureTheory Set Filter Finset
open RiemannBlueprint.Section8_VasyuninBDR

/-- Product of two dilated fractional parts is interval integrable on any compact interval. -/
theorem intervalIntegrable_recipFractScaled_mul (j k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => recipFractScaled j x * recipFractScaled k x) volume a b := by
  have hmeas : Measurable (fun x => recipFractScaled j x * recipFractScaled k x) := by
    have hmj : Measurable (recipFractScaled j) :=
      measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
    have hmk : Measurable (recipFractScaled k) :=
      measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
    exact hmj.mul hmk
  have hbd : ∀ x, ‖recipFractScaled j x * recipFractScaled k x‖ ≤ (1 : ℝ) := by
    intro x
    unfold recipFractScaled
    have hj_nonneg : 0 ≤ Int.fract (1 / ((j : ℝ) * x)) := Int.fract_nonneg _
    have hk_nonneg : 0 ≤ Int.fract (1 / ((k : ℝ) * x)) := Int.fract_nonneg _
    have hj_lt : Int.fract (1 / ((j : ℝ) * x)) < 1 := Int.fract_lt_one _
    have hk_lt : Int.fract (1 / ((k : ℝ) * x)) < 1 := Int.fract_lt_one _
    rw [Real.norm_of_nonneg (mul_nonneg hj_nonneg hk_nonneg)]
    nlinarith
  exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hmeas.aestronglyMeasurable
    (ae_of_all _ fun x => hbd x)

/-- On the upper sub-interval `uIoc (max(1/j, 1/k)) 1`, both fractional parts reduce to hyperbolas:
`recipFractScaled j x * recipFractScaled k x = 1 / (j * k * x^2)`. -/
theorem recipFractScaled_mul_eq_on_uIoc {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∈ uIoc (max (1 / (j : ℝ)) (1 / (k : ℝ))) 1) :
    recipFractScaled j x * recipFractScaled k x = 1 / ((j : ℝ) * (k : ℝ) * x ^ 2) := by
  let M := max (1 / (j : ℝ)) (1 / (k : ℝ))
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hj_le_one : 1 / (j : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hj) hj_pos.le
  have hk_le_one : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hk_pos.le
  have hM_le : M ≤ 1 := max_le hj_le_one hk_le_one
  rw [uIoc_of_le hM_le] at hx
  have hx_j : x ∈ uIoc (1 / (j : ℝ)) 1 := by
    rw [uIoc_of_le hj_le_one]
    exact ⟨(le_max_left (1 / (j : ℝ)) (1 / (k : ℝ))).trans_lt hx.1, hx.2⟩
  have hx_k : x ∈ uIoc (1 / (k : ℝ)) 1 := by
    rw [uIoc_of_le hk_le_one]
    exact ⟨(le_max_right (1 / (j : ℝ)) (1 / (k : ℝ))).trans_lt hx.1, hx.2⟩
  rw [recipFractScaled_eq_one_div_of_mem_uIoc hj hx_j,
      recipFractScaled_eq_one_div_of_mem_uIoc hk hx_k]
  ring

/-- Exact integral of `1 / (j * k * x^2)` on `M..1`. -/
theorem intervalIntegral_inv_prod_x_sq {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) {M : ℝ}
    (hM_pos : 0 < M) (hM_le : M ≤ 1) :
    ∫ x in M..1, (1 : ℝ) / ((j : ℝ) * (k : ℝ) * x ^ 2) =
      1 / ((j : ℝ) * (k : ℝ) * M) - 1 / ((j : ℝ) * (k : ℝ)) := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hjk_pos : (0 : ℝ) < (j : ℝ) * (k : ℝ) := mul_pos hj_pos hk_pos
  have h_deriv : ∀ x ∈ Set.uIcc M 1,
      HasDerivAt (fun y : ℝ => -(1 : ℝ) / ((j : ℝ) * (k : ℝ) * y))
        ((1 : ℝ) / ((j : ℝ) * (k : ℝ) * x ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hM_le] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le hM_pos hx.1
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx_pos.ne'
    have hconst := hinv.const_mul (-(1 : ℝ) / ((j : ℝ) * (k : ℝ)))
    have hEq : (fun y : ℝ => (-(1 : ℝ) / ((j : ℝ) * (k : ℝ))) * y⁻¹) =
        (fun y : ℝ => -(1 : ℝ) / ((j : ℝ) * (k : ℝ) * y)) := by
      funext y; ring
    rw [hEq] at hconst
    convert hconst using 1
    field_simp [hj_pos.ne', hk_pos.ne', hx_pos.ne']
  have h_cont : ContinuousOn (fun x : ℝ => (1 : ℝ) / ((j : ℝ) * (k : ℝ) * x ^ 2))
      (Set.uIcc M 1) := by
    intro x hx
    rw [Set.uIcc_of_le hM_le] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le hM_pos hx.1
    have hdenom : (j : ℝ) * (k : ℝ) * x ^ 2 ≠ 0 :=
      mul_ne_zero hjk_pos.ne' (pow_ne_zero 2 hx_pos.ne')
    exact ((continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.pow 2)) hdenom)).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont.intervalIntegrable
  rw [hftc]
  ring

/-- Upper sub-interval contribution to the cross inner product on `(max(1/j, 1/k), 1)`. -/
theorem intervalIntegral_recipFractScaled_mul_upper {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    let M := max (1 / (j : ℝ)) (1 / (k : ℝ))
    ∫ x in M..1, recipFractScaled j x * recipFractScaled k x =
      1 / ((j : ℝ) * (k : ℝ) * M) - 1 / ((j : ℝ) * (k : ℝ)) := by
  intro M
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hM_pos : 0 < M := lt_max_of_lt_left (div_pos one_pos hj_pos)
  have hj_le_one : 1 / (j : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hj) hj_pos.le
  have hk_le_one : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hk_pos.le
  have hM_le : M ≤ 1 := max_le hj_le_one hk_le_one
  have h_eq : (∫ x in M..1, recipFractScaled j x * recipFractScaled k x) =
      ∫ x in M..1, (1 : ℝ) / ((j : ℝ) * (k : ℝ) * x ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    exact ae_of_all _ (fun x hx => recipFractScaled_mul_eq_on_uIoc hj hk hx)
  rw [h_eq]
  exact intervalIntegral_inv_prod_x_sq hj hk hM_pos hM_le

/-- Vasyunin's cotangent sum V(a, b) for coprime pairs or general positive integers:
  V(a, b) = ∑_{m=1}^{a-1} {m * b / a} * cot(π * m / a). -/
noncomputable def vasyuninCotSum (a b : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 a,
    Int.fract ((m : ℝ) * (b : ℝ) / (a : ℝ)) *
      (Real.cos (Real.pi * (m : ℝ) / (a : ℝ)) / Real.sin (Real.pi * (m : ℝ) / (a : ℝ)))

/-- Cotangent component of Vasyunin's cross Gram matrix entry:
  g_{j,k}^{(cot)} = - (π / (2 * j * k)) * (V(j, k) + V(k, j)). -/
noncomputable def vasyuninGCot (j k : ℕ) : ℝ :=
  - (Real.pi / (2 * (j : ℝ) * (k : ℝ))) * (vasyuninCotSum j k + vasyuninCotSum k j)

/-- vasyuninCotSum vanishes on the diagonal: V(k, k) = 0 for any k. -/
theorem vasyuninCotSum_diag (k : ℕ) : vasyuninCotSum k k = 0 := by
  unfold vasyuninCotSum
  by_cases hk : k = 0
  · subst hk
    rfl
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  refine Finset.sum_eq_zero ?_
  intro m _hm
  have hmk : (m : ℝ) * (k : ℝ) / (k : ℝ) = (m : ℝ) := mul_div_cancel_right₀ (m : ℝ) hk_pos.ne'
  rw [hmk, Int.fract_natCast, zero_mul]

/-- The cotangent Gram component vanishes on the diagonal. -/
theorem vasyuninGCot_diag (k : ℕ) : vasyuninGCot k k = 0 := by
  unfold vasyuninGCot
  rw [vasyuninCotSum_diag k, add_zero, mul_zero]

/-- Symmetry of the cotangent Gram component: g_{j,k}^{(cot)} = g_{k,j}^{(cot)}. -/
theorem vasyuninGCot_comm (j k : ℕ) : vasyuninGCot j k = vasyuninGCot k j := by
  dsimp [vasyuninGCot]
  have hdenom : 2 * (j : ℝ) * (k : ℝ) = 2 * (k : ℝ) * (j : ℝ) := by ring
  rw [hdenom, add_comm (vasyuninCotSum j k)]

/-- GSmooth is symmetric in j and k. -/
theorem GSmooth_comm (gamma_E : ℝ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    GSmooth gamma_E j k = GSmooth gamma_E k j := by
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth]
  have hlog_inv : Real.log ((j : ℝ) / (k : ℝ)) = - Real.log ((k : ℝ) / (j : ℝ)) := by
    rw [Real.log_div hj_ne hk_ne, Real.log_div hk_ne hj_ne]
    ring
  rw [hlog_inv]
  ring

/-- On the diagonal, GSmooth evaluates to the smooth Vasyunin diagonal value. -/
theorem GSmooth_diag (gamma_E : ℝ) {k : ℕ} (hk : 0 < k) :
    GSmooth gamma_E k k = (Real.log (2 * Real.pi) - gamma_E) / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth]
  rw [div_self hk_ne, Real.log_one, mul_zero, add_zero]
  field_simp [hk_ne]
  ring

/-- The total Vasyunin Gram entry GSmooth + vasyuninGCot evaluates to the exact diagonal energy. -/
theorem vasyuninGram_diag (gamma_E : ℝ) {k : ℕ} (hk : 0 < k) :
    GSmooth gamma_E k k + vasyuninGCot k k =
      (Real.log (2 * Real.pi) - gamma_E) / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
  rw [vasyuninGCot_diag k, add_zero]
  exact GSmooth_diag gamma_E hk

/-- Full quadratic expansion of the Lebesgue L² distance:
  ∫_0^1 (1 - ∑ c_k {1/(kx)})² dx = 1 - 2 ∑ c_k b_k + ∑∑ c_j c_k g_{j,k}. -/
theorem intervalIntegral_sq_sub_sum {N : ℕ} (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k *
          ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x := by
  have h_exp : ∀ x, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x) := by
    intro x
    have hsq : (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 =
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x) := by
      rw [sq, sum_mul_sum]
      refine sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => ?_))
      ring
    have hlin : (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 =
        1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) +
          (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 := by ring
    rw [hlin, hsq]
  have h_eq : (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      ∫ x in (0 : ℝ)..1, (1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x)) := by
    refine intervalIntegral.integral_congr (fun x _ => h_exp x)
  rw [h_eq]
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  have hint2_term : ∀ k ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => c k * recipFractScaled k x) volume 0 1 := by
    intro k _
    exact (intervalIntegrable_recipFractScaled k 0 1).const_mul (c k)
  have hint2_sum : IntervalIntegrable
      (fun x => ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) volume 0 1 := by
    have heq : (fun x => ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) =
        (∑ k ∈ Finset.Icc 1 N, fun x => c k * recipFractScaled k x) := by
      funext x; rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) hint2_term
  have hint2 : IntervalIntegrable
      (fun x => 2 * ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) volume 0 1 :=
    hint2_sum.const_mul 2
  have hint3_term : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => c j * c k *
        (recipFractScaled j x * recipFractScaled k x)) volume 0 1 := by
    intro j _ k _
    exact (intervalIntegrable_recipFractScaled_mul j k 0 1).const_mul (c j * c k)
  have hint3_inner : ∀ j ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x)) volume 0 1 := by
    intro j hj
    have heq : (fun x => ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x)) =
        (∑ k ∈ Finset.Icc 1 N, fun x => c j * c k *
          (recipFractScaled j x * recipFractScaled k x)) := by
      funext x; rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (hint3_term j hj)
  have hint3 : IntervalIntegrable (fun x => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j * c k * (recipFractScaled j x * recipFractScaled k x)) volume 0 1 := by
    have heq : (fun x => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x)) =
        (∑ j ∈ Finset.Icc 1 N, fun x => ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x)) := by
      funext x; rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) hint3_inner
  rw [intervalIntegral.integral_add (hint1.sub hint2) hint3]
  rw [intervalIntegral.integral_sub hint1 hint2]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum hint2_term]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum hint3_inner]
  refine congr_arg₂ _ rfl ?_
  refine sum_congr rfl ?_
  intro j hj
  rw [intervalIntegral.integral_finsetSum (hint3_term j hj)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- Quadratic form of the cotangent Gram matrix on `Finset.Icc 1 N`. -/
noncomputable def QCot (g_cot : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * g_cot j k

/-- Theorem: Affine L² Pure Cotangent Bridge.
For any coefficient sequence `c` on the affine subspace `A_N` (satisfying `D1(c, N) = 0` and
`D0(c, N) = 2`), when the linear target projections equal `bVasyunin` and the cross inner products
equal `GSmooth + g_cot`, the true continuous Lebesgue L² distance collapses unconditionally
to `1 + QCot g_cot c N` with zero smooth or logarithmic residual. -/
theorem affine_l2_pure_cotangent_bridge {N : ℕ} (c : ℕ → ℝ) (gamma_E : ℝ)
    (g_cot : ℕ → ℕ → ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2)
    (hb : ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled k x) = bVasyunin k gamma_E)
    (hG : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
        GSmooth gamma_E j k + g_cot j k)
    (hint_sq : (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k *
          ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 + QCot g_cot c N := by
  rw [hint_sq]
  have hb_sum : (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) =
      ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E := by
    refine sum_congr rfl (fun k hk => ?_)
    rw [hb k hk]
  rw [hb_sum]
  have hG_sum : (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k *
      ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) +
        QCot g_cot c N := by
    unfold QCot
    have hterm : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
        c j * c k * ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x =
        c j * c k * GSmooth gamma_E j k + c j * c k * g_cot j k := by
      intro j hj k hk
      rw [hG j hj k hk, mul_add]
    have hinner : ∀ j ∈ Finset.Icc 1 N,
        (∑ k ∈ Finset.Icc 1 N, c j * c k *
          ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
        (∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) +
          ∑ k ∈ Finset.Icc 1 N, c j * c k * g_cot j k := by
      intro j hj
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun k hk => hterm j hj k hk)
    rw [sum_congr rfl (fun j hj => hinner j hj), sum_add_distrib]
  rw [hG_sum, ← add_assoc]
  exact affine_bdr_pure_cotangent_identity c N gamma_E (QCot g_cot c N) hD1 hD0
