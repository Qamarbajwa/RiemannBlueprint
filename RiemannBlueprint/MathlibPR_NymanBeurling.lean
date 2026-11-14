/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import RiemannBlueprint.MellinFracPart
import RiemannBlueprint.Section8_VasyuninBDR
import RiemannBlueprint.CMIAuditBridge

/-!
# Nyman–Beurling (1950) and Báez-Duarte (2003) Forward Theorems for the Riemann Hypothesis

This standalone upstream-PR module packages the unconditional forward implications from `L²(0, 1)`
completeness of fractional-part dilations `{1 / (k x)}` (`recipFractScaled k x`) to Mathlib's
`_root_.RiemannHypothesis`, together with the Rank-4 Vasyunin Boundary-Dirichlet Reduction (BDR)
cotangent criterion.

## Mathematical background

* **Titchmarsh (1986), Eq. (2.1.5):** For `0 < s.re` and `s ≠ 1`,
  `∫ x in Ioc 0 1, {1 / x} * x ^ (s - 1) = 1 / (s - 1) - riemannZeta s / s`.
* **Nyman (1950) / Beurling (1955) (Constrained):** If `1` lies in the `L²(0, 1)` closure of finite
  linear combinations `∑ k ∈ Icc 1 N, c k * {1 / (k x)}` obeying `∑ k ∈ Icc 1 N, c k / k = 0`,
  then any critical-strip zero `s₀` with `1 / 2 < s₀.re` yields a strictly positive Cauchy–Schwarz
  floor `(2 * s₀.re - 1) / ‖s₀‖ ^ 2 ≤ ∫ x in Ioo 0 1, ‖R x‖ ^ 2` via the spatial test function
  `g_{s₀}(x) = x ^ (conj s₀ - 1)`.
* **Báez-Duarte (2003) (Unconstrained):** Removing the pole-cancellation constraint `∑ c k / k = 0`
  is handled via the paired annihilator `h_{s₀}(x) = (conj s₀ - 1) x ^ (conj s₀ - 1) - (s₀ - 1) x ^ (s₀ - 1)`
  after proving `s₀.im ≠ 0` for critical-strip zeros (`0 < s₀.re < 1`).
* **Vasyunin (1995) Rank-4 BDR Cotangent Criterion:** Under `D₁(c) = 0`, if the Rank-4 boundary
  smooth part converges to `1` and the cotangent Rayleigh quotient `Q_cot → -1`, then
  `_root_.RiemannHypothesis` holds.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]` with `0` `sorry`s.
-/

namespace MathlibPR.NymanBeurling

/-- **1. Critical-Strip Zeta Continuation:** For `0 < s.re` and `s ≠ 1`, `riemannZeta s` equals
`s / (s - 1) - s * ∑' n : ℕ, harmonicUnitSummand s (n + 1)`. -/
theorem riemannZeta_eq_tsum_harmonicUnitSummand (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) -
        s * ∑' n : ℕ, NumberTheory.MellinFracPart.harmonicUnitSummand s (n + 1) := by
  rw [NumberTheory.MellinFracPart.riemannZeta_eq_tsum_harmonicUnitSummand s hs_pos hs_ne_one]
  ring

/-- **2. Titchmarsh Eq. (2.1.5):** For `0 < s.re` and `s ≠ 1`,
`∫ x in Ioc 0 1, ({1/x} : ℂ) * x ^ (s - 1) = 1 / (s - 1) - riemannZeta s / s`. -/
theorem mellin_recipFract_unit_interval (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      (NumberTheory.MellinFracPart.recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s :=
  NumberTheory.MellinFracPart.mellin_recipFract_unit_interval_of_pos_re s hs_pos hs_ne_one

/-- **3a. Schwarz Conjugation Symmetry:** For `0 < s.re` and `s ≠ 1`,
`riemannZeta (conj s) = conj (riemannZeta s)`. -/
theorem riemannZeta_conj_of_pos_re (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) :=
  CMIAudit.riemannZeta_conj_of_pos_re s hs_pos hs_ne_one

/-- **3b. Non-Real Critical-Strip Zeros:** Any zero `s₀` of `riemannZeta` in the critical strip
`0 < s₀.re < 1` has `s₀.im ≠ 0`. -/
theorem im_ne_zero_of_inCriticalStrip_zeta_zero (s₀ : ℂ)
    (hs : CMIAudit.InCriticalStrip s₀) (hz : riemannZeta s₀ = 0) :
    s₀.im ≠ 0 :=
  CMIAudit.im_ne_zero_of_inCriticalStrip_zeta_zero s₀ hs hz

/-- **4. Constrained Nyman–Beurling Spatial Cauchy–Schwarz Floor:**
If `0 < s₀.re`, `1/2 < s₀.re`, `riemannZeta s₀ = 0`, and `∑ k ∈ Icc 1 N, c k / k = 0`, then
`(2 * s₀.re - 1) / ‖s₀‖ ^ 2 ≤ ∫ x in Ioo 0 1, ‖1 - ∑ k ∈ Icc 1 N, c k * ρ_k(x)‖ ^ 2`. -/
theorem nymanBeurling_spatial_cauchy_floor (s₀ : ℂ)
    (hs : CMIAudit.InCriticalStrip s₀) (hre : 1 / 2 < s₀.re)
    (hz : riemannZeta s₀ = 0) (N : ℕ) (c : ℕ → ℂ)
    (hc : ∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ) = 0) :
    (2 * s₀.re - 1) / ‖s₀‖ ^ 2 ≤
      ∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2 := by
  have h := CMIAudit.nymanBeurling_spatial_cauchy_floor N c hc s₀ hs hre hz
  rwa [Complex.normSq_eq_norm_sq] at h

/-- **5. Unconstrained Báez–Duarte Spatial Cauchy–Schwarz Floor:**
For any critical-strip zero `s₀` with `1 / 2 < s₀.re`, there exists `δ > 0` such that
`δ ≤ ∫ x in Ioo 0 1, ‖1 - ∑ k ∈ Icc 1 N, c k * ρ_k(x)‖ ^ 2` for all `N` and unconstrained `c`. -/
theorem baezDuarte_unconstrained_spatial_floor (s₀ : ℂ)
    (hs : CMIAudit.InCriticalStrip s₀) (hre : 1 / 2 < s₀.re)
    (hz : riemannZeta s₀ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (c : ℕ → ℂ),
      δ ≤ ∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2 :=
  CMIAudit.baezDuarte_unconstrained_spatial_floor s₀ hs hre hz

/-- **6. Constrained Nyman–Beurling Forward Theorem (`NB → RH`):**
If `1` lies in the `L²(0, 1)` closure of constrained dilations `∑ k ∈ Icc 1 N, c k * ρ_k(x)`
(`∑ c k / k = 0`), then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_nymanBeurling_approx
    (h_nb : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℂ),
      (∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ) = 0) ∧
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) < ε) :
    _root_.RiemannHypothesis :=
  CMIAudit.nymanBeurling_implies_rh h_nb

/-- **7. Unconstrained Báez–Duarte Forward Theorem (`BD → RH`):**
If `1` lies in the `L²(0, 1)` closure of unconstrained dilations `∑ k ∈ Icc 1 N, c k * ρ_k(x)`,
then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_baezDuarte_approx
    (h_bd : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℂ),
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) < ε) :
    _root_.RiemannHypothesis :=
  CMIAudit.baezDuarte_implies_rh h_bd

/-- **8. Vasyunin Rank-4 BDR Cotangent Forward Theorem (`Q_cot → -1 ⇒ RH`):**
If real sequences `c_seq N` obey `D₁(c_seq N) = 0`, the `L²(0, 1)` residual is bounded by `E_BDR`,
the Rank-4 boundary smooth part tends to `1`, and `Q_cot_seq → -1`, then `_root_.RiemannHypothesis`
holds. -/
theorem RiemannHypothesis.of_vasyunin_bdr_cotangent_limit
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD1 : ∀ N, 2 ≤ N → RiemannBlueprint.Section8_VasyuninBDR.D1 (c_seq N) N = 0)
    (h_bdr_le : ∀ N, 2 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          (c_seq N k : ℂ) * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        RiemannBlueprint.Section8_VasyuninBDR.E_BDR (c_seq N) N gamma_E (Q_cot_seq N))
    (h_smooth_lim : Filter.Tendsto
      (fun N => 1 + (2 - RiemannBlueprint.Section8_VasyuninBDR.D0 (c_seq N) N) *
        RiemannBlueprint.Section8_VasyuninBDR.D1_deriv (c_seq N) N)
      Filter.atTop (nhds 1))
    (h_cot_lim : Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.bdr_cotangent_implies_rh c_seq Q_cot_seq gamma_E hD1 h_bdr_le h_smooth_lim h_cot_lim

#print axioms riemannZeta_eq_tsum_harmonicUnitSummand
#print axioms mellin_recipFract_unit_interval
#print axioms riemannZeta_conj_of_pos_re
#print axioms im_ne_zero_of_inCriticalStrip_zeta_zero
#print axioms nymanBeurling_spatial_cauchy_floor
#print axioms baezDuarte_unconstrained_spatial_floor
#print axioms RiemannHypothesis.of_nymanBeurling_approx
#print axioms RiemannHypothesis.of_baezDuarte_approx
#print axioms RiemannHypothesis.of_vasyunin_bdr_cotangent_limit

end MathlibPR.NymanBeurling
