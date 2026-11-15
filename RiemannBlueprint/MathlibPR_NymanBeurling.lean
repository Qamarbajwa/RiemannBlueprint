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

/-- **9. Unconstrained Four-Boundary Clay Cotangent Forward Theorem (`(2, -2 ln 2π, 0, -1)` & `Q_cot → -1 ⇒ RH`):**
For any unconstrained real sequence `c_seq` converging to all four Clay/BDR boundary limits at
`s ∈ {0, 1}`, `L² ≤ E_BDR` and `Q_cot_seq → -1` imply `_root_.RiemannHypothesis`. -/
theorem RiemannHypothesis.of_clay_four_boundary_cotangent_limit
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (hD0 : Filter.Tendsto (fun N => RiemannBlueprint.Section8_VasyuninBDR.D0 (c_seq N) N)
      Filter.atTop (nhds 2))
    (hD0' : Filter.Tendsto (fun N => RiemannBlueprint.Section8_VasyuninBDR.D0_deriv (c_seq N) N)
      Filter.atTop (nhds (-2 * Real.log (2 * Real.pi))))
    (hD1 : Filter.Tendsto (fun N => RiemannBlueprint.Section8_VasyuninBDR.D1 (c_seq N) N)
      Filter.atTop (nhds 0))
    (hD1' : Filter.Tendsto (fun N => RiemannBlueprint.Section8_VasyuninBDR.D1_deriv (c_seq N) N)
      Filter.atTop (nhds (-1)))
    (h_bdr_le : ∀ N, 1 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          (c_seq N k : ℂ) * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        RiemannBlueprint.Section8_VasyuninBDR.E_BDR (c_seq N) N gamma_E (Q_cot_seq N))
    (h_cot_lim : Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clay_four_boundary_limits_implies_rh
    c_seq Q_cot_seq gamma_E hD0 hD0' hD1 hD1' h_bdr_le h_cot_lim

/-- **10. Explicit Rank-4 Boundary-Lock (`clayRank4Lock`) Cotangent Forward Theorem:**
Projecting any unconstrained sequence `c_seq` onto `SatisfiesClayBoundaryConditions · N` via
`clayRank4Lock`, if `L²(clayRank4Lock (c_seq N) N) ≤ E_BDR` for `N ≥ 4` and `Q_cot_seq → -1`,
then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Lock_cotangent_limit
    (c_seq : ℕ → (ℕ → ℝ)) (Q_cot_seq : ℕ → ℝ) (gamma_E : ℝ)
    (h_bdr_le : ∀ N, 4 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Lock (c_seq N) N k : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        RiemannBlueprint.Section8_VasyuninBDR.E_BDR
          (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Lock (c_seq N) N)
          N gamma_E (Q_cot_seq N))
    (h_cot_lim : Filter.Tendsto Q_cot_seq Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Lock_cotangent_implies_rh c_seq Q_cot_seq gamma_E h_bdr_le h_cot_lim

/-- **11. Bilinear `Q_cot_quad` Rank-4 Boundary-Lock Cotangent Forward Theorem:**
For any `G_cot : ℕ → ℕ → ℝ` and unconstrained `c_seq`, if
`L²(clayRank4Lock (c_seq N) N) ≤ 1 + Q_cot_quad G_cot (clayRank4Lock (c_seq N) N) N` for `N ≥ 4`
and `Q_cot_quad G_cot (clayRank4Lock (c_seq N) N) N → -1`, then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Lock_Q_cot_quad_limit
    (G_cot : ℕ → ℕ → ℝ) (c_seq : ℕ → (ℕ → ℝ))
    (h_bd_le : ∀ N, 4 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Lock (c_seq N) N k : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Lock (c_seq N) N) N)
    (h_cot_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Lock (c_seq N) N) N)
      Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Lock_Q_cot_quad_implies_rh G_cot c_seq h_bd_le h_cot_lim

/-- **12. Affine Base-Plus-Nullspace (`clayRank4Base + α • clayRank4Hom`) Forward Theorem:**
For any `G_cot : ℕ → ℕ → ℝ`, directions `u_seq`, and scalars `α_seq`, if
`L²(clayRank4Base + α_seq N • clayRank4Hom (u_seq N) N) ≤ 1 + Q_cot_quad` for `N ≥ 4` and
`Q_cot_quad → -1`, then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Base_add_hom_Q_cot_quad_limit
    (G_cot : ℕ → ℕ → ℝ) (u_seq : ℕ → (ℕ → ℝ)) (α_seq : ℕ → ℝ)
    (h_bd_le : ∀ N, 4 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          ((RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k +
            α_seq N * RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N k : ℝ) : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k +
            α_seq N * RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N k) N)
    (h_cot_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k +
          α_seq N * RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N k) N)
      Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Base_add_hom_Q_cot_quad_implies_rh G_cot u_seq α_seq h_bd_le h_cot_lim

/-- **13. Optimal 1D Homogeneous Nullspace Step Forward Theorem:**
For symmetric `G_cot` and directions `u_seq`, if `v_N = clayRank4Hom (u_seq N) N` has
`A_N = Q_cot_quad G_cot v_N N ≠ 0`, `L²(clayRank4Base + (-B_N / A_N) • v_N) ≤ 1 + Q_cot_quad`
for `N ≥ 4`, and `Q_cot_quad clayRank4Base - B_N^2 / A_N → -1`, then `_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Base_opt_step_limit
    (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_bd_le : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N
      let B := RiemannBlueprint.Section8_VasyuninBDR.B_cot_bilinear G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base v N
      let A := RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot v N
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          ((RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + (-B / A) * v k : ℝ) : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + (-B / A) * v k) N)
    (h_opt_lim : Filter.Tendsto
      (fun N =>
        let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N
        let B := RiemannBlueprint.Section8_VasyuninBDR.B_cot_bilinear G_cot
          RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base v N
        let A := RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot v N
        RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base N - B ^ 2 / A)
      Filter.atTop (nhds (-1))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Base_opt_step_implies_rh G_cot hG_symm u_seq hA h_bd_le h_opt_lim

/-- **14. Universal `N = 4` Constant Galerkin Nullspace Forward Theorem:**
For symmetric `G_cot` and homogeneous, Galerkin-orthogonal vectors `v_seq`, if
`L²(clayRank4Base + v_seq N) ≤ 1 + Q_cot_quad` for `N ≥ 4` and
`Q_cot_quad G_cot (v_seq N) N → 1 + Q_cot_quad G_cot clayRank4Base 4`, then
`_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Base_galerkin_hom_limit
    (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (v_seq : ℕ → (ℕ → ℝ))
    (h_hom : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.SatisfiesHomogeneousClayConditions (v_seq N) N)
    (h_gal : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.SatisfiesCotGalerkin G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base (v_seq N) N)
    (h_bd_le : ∀ N, 4 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          ((RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v_seq N k : ℝ) : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v_seq N k) N)
    (h_hom_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot (v_seq N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Base_galerkin_hom_limit_implies_rh
    G_cot hG_symm v_seq h_hom h_gal h_bd_le h_hom_lim

/-- **15. 1D Base-Potential Pairing Forward Theorem:**
For symmetric `G_cot` and homogeneous, Galerkin-orthogonal vectors `v_seq`, if
`L²(clayRank4Base + v_seq N) ≤ 1 + Q_cot_quad` for `N ≥ 4` and the 1D linear pairing
`∑_{k=1}^N v_seq N k * phiCotBase G_cot k → -(1 + Q_cot_quad G_cot clayRank4Base 4)`, then
`_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4Base_phiCotBase_pairing_limit
    (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (v_seq : ℕ → (ℕ → ℝ))
    (h_hom : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.SatisfiesHomogeneousClayConditions (v_seq N) N)
    (h_gal : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.SatisfiesCotGalerkin G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base (v_seq N) N)
    (h_bd_le : ∀ N, 4 ≤ N →
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          ((RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v_seq N k : ℝ) : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v_seq N k) N)
    (h_phi_lim : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.Icc 1 N,
        v_seq N k * RiemannBlueprint.Section8_VasyuninBDR.phiCotBase G_cot k)
      Filter.atTop
      (nhds (-(1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4)))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4Base_phiCotBase_pairing_limit_implies_rh
    G_cot hG_symm v_seq h_hom h_gal h_bd_le h_phi_lim

/-- **16. Unconstrained 1D Rayleigh–Potential Saturation Forward Theorem:**
For symmetric `G_cot` and any unconstrained sequence `u_seq` with nonzero cotangent norm on
`h_N = clayRank4Hom (u_seq N) N`, `clayRank4GalerkinRay` automatically satisfies all four
homogeneous boundary conditions and cotangent Galerkin orthogonality. If
`L²(clayRank4Base + clayRank4GalerkinRay G_cot (u_seq N) N) ≤ 1 + Q_cot_quad` for `N ≥ 4` and
`phiCotRayQuotient G_cot h_N N → 1 + Q_cot_quad G_cot clayRank4Base 4`, then
`_root_.RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_clayRank4GalerkinRay_rayQuotient_limit
    (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_bd_le : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4GalerkinRay G_cot (u_seq N) N
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N,
          ((RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k : ℝ) : ℂ) *
            (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)‖ ^ 2) ≤
        1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k) N)
    (h_ray_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.phiCotRayQuotient G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4GalerkinRay_rayQuotient_limit_implies_rh
    G_cot hG_symm u_seq hA h_bd_le h_ray_lim

/-- **17. Unconditional Critical-Strip Zero Reflection Symmetry:**
Directly from Mathlib's `riemannZeta_one_sub`, any critical-strip zero `0 < s.re ∧ s.re < 1`
reflects to `0 < (1 - s).re ∧ (1 - s).re < 1` with `riemannZeta (1 - s) = 0`. -/
theorem zetaZeroReflectionSymmetry :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s = 0 →
      (0 < (1 - s).re ∧ (1 - s).re < 1) ∧ riemannZeta (1 - s) = 0 :=
  CMIAudit.zetaZeroReflectionSymmetry_unconditional

/-- **18. Reflection-Free Hardy–Szegő & 1D Rayleigh Quotient Forward Theorem:**
Combines `SzegoReproducingInequality D`, `vasyunin_energy_clayRank4GalerkinRay_eq_sub_rayQuotient`,
and `phiCotRayQuotient G_cot (clayRank4Hom (u_seq N) N) N → 1 + Q_cot_quad G_cot clayRank4Base 4`
to deduce `_root_.RiemannHypothesis` without taking any reflection hypothesis. -/
theorem RiemannHypothesis.of_szego_and_clayRank4GalerkinRay_rayQuotient_limit
    (D : ℕ → ℝ) (gamma_E : ℝ)
    (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (h_szego : CMIAudit.SzegoReproducingInequality D)
    (h_nonneg : ∀ N : ℕ, 0 ≤ CMIAudit.baezDuarteDistSq D N)
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_ub : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4GalerkinRay G_cot (u_seq N) N
      CMIAudit.baezDuarteDistSq D N ≤
        CMIAudit.vasyuninQuadraticEnergy
          (RiemannBlueprint.Section8_VasyuninBDR.GVasyuninDecomp gamma_E G_cot)
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.bVasyunin k gamma_E) N
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k))
    (h_ray_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.phiCotRayQuotient G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4GalerkinRay_rayQuotient_limit_implies_rh_of_szego
    D gamma_E G_cot hG_symm u_seq h_szego h_nonneg hA h_ub h_ray_lim

/-- **19. First-Stage Prime Totient Defect:** For any prime `p`, `p - φ(p) = 1`. -/
theorem totientDefect1_prime (p : ℕ) (hp : Nat.Prime p) :
    RiemannBlueprint.Section8_VasyuninBDR.totientDefect1 p = 1 :=
  RiemannBlueprint.Section8_VasyuninBDR.totientDefect1_prime p hp

/-- **20. Prime-Power Collapse Excess Energy:** For any prime `p` and `k ≥ 1`,
`primePowerExtraEnergy (p ^ k) = p ^ (k - 1) - 1`. -/
theorem primePowerExtraEnergy_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) :
    RiemannBlueprint.Section8_VasyuninBDR.primePowerExtraEnergy (p ^ k) = p ^ (k - 1) - 1 :=
  RiemannBlueprint.Section8_VasyuninBDR.primePowerExtraEnergy_prime_pow p k hp hk

/-- **21. Vanishing of Collapse Weight at Exponent 1:** For any prime `p`,
`collapseWeightPurePower p 1 = 0`. -/
theorem collapseWeightPurePower_k_eq_one (p : ℕ) :
    RiemannBlueprint.Section8_VasyuninBDR.collapseWeightPurePower p 1 = 0 :=
  RiemannBlueprint.Section8_VasyuninBDR.collapseWeightPurePower_k_eq_one p

/-- **22. Decomposed Hardy–Cauchy–Schwarz & 1D Rayleigh Quotient Forward Theorem:**
Combines `SatisfiesHardyCauchySchwarz D pairing szegoNormSq`,
`vasyunin_energy_clayRank4GalerkinRay_eq_sub_rayQuotient`, and
`phiCotRayQuotient G_cot (clayRank4Hom (u_seq N) N) N → 1 + Q_cot_quad G_cot clayRank4Base 4`
to deduce `_root_.RiemannHypothesis` without taking any reflection hypothesis. -/
theorem RiemannHypothesis.of_hardyCauchySchwarz_and_clayRank4GalerkinRay_rayQuotient_limit
    (D : ℕ → ℝ) (pairing : ℂ → ℕ → ℝ) (szegoNormSq : ℂ → ℝ)
    (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (h_hcs : CMIAudit.SatisfiesHardyCauchySchwarz D pairing szegoNormSq)
    (h_nonneg : ∀ N : ℕ, 0 ≤ CMIAudit.baezDuarteDistSq D N)
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_ub : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4GalerkinRay G_cot (u_seq N) N
      CMIAudit.baezDuarteDistSq D N ≤
        CMIAudit.vasyuninQuadraticEnergy
          (RiemannBlueprint.Section8_VasyuninBDR.GVasyuninDecomp gamma_E G_cot)
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.bVasyunin k gamma_E) N
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k))
    (h_ray_lim : Filter.Tendsto
      (fun N => RiemannBlueprint.Section8_VasyuninBDR.phiCotRayQuotient G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4GalerkinRay_rayQuotient_limit_implies_rh_of_hardyCauchySchwarz
    D pairing szegoNormSq gamma_E G_cot hG_symm u_seq h_hcs h_nonneg hA h_ub h_ray_lim

/-- 24. Exact antiderivative evaluation at `± π / 2` for the critical-line Szegő Poisson kernel,
yielding the Hardy–Szegő Cauchy floor reciprocal `Complex.normSq s₀ / (2 * s₀.re - 1)`. -/
theorem szegoKernelAntideriv_upper_sub_lower (s₀ : ℂ) (h_re : 1 / 2 < s₀.re) :
    (Complex.normSq s₀ / (2 * Real.pi * (s₀.re - 1 / 2))) * (Real.pi / 2) -
      (Complex.normSq s₀ / (2 * Real.pi * (s₀.re - 1 / 2))) * (-(Real.pi / 2)) =
      Complex.normSq s₀ / (2 * s₀.re - 1) :=
  CMIAudit.szegoKernelAntideriv_upper_sub_lower s₀ h_re

/-- 25. Exact real derivative identity
`HasDerivAt (szegoKernelAntideriv s₀) (szegoKernelIntegrand s₀ t) t` for `1 / 2 < s₀.re`. -/
theorem hasDerivAt_szegoKernelAntideriv (s₀ : ℂ) (h_re : 1 / 2 < s₀.re) (t : ℝ) :
    HasDerivAt (CMIAudit.szegoKernelAntideriv s₀) (CMIAudit.szegoKernelIntegrand s₀ t) t :=
  CMIAudit.hasDerivAt_szegoKernelAntideriv s₀ h_re t

/-- 26. Unconstrained Raw-Vector Clay–Galerkin 1D Limit Implies RH under Hardy Cauchy–Schwarz:
any unconstrained raw sequence `u_seq : ℕ → ℕ → ℝ` (requiring zero boundary conditions) with
`phiCotUnconstrainedRayQuotient G_cot (u_seq N) N → 1 + Q_cot_quad G_cot clayRank4Base 4`
implies `_root_.RiemannHypothesis`. -/
theorem RiemannHypothesis.of_hardyCauchySchwarz_and_unconstrainedRayQuotient_limit
    (D : ℕ → ℝ) (pairing : ℂ → ℕ → ℝ) (szegoNormSq : ℂ → ℝ)
    (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (h_hcs : CMIAudit.SatisfiesHardyCauchySchwarz D pairing szegoNormSq)
    (h_nonneg : ∀ N : ℕ, 0 ≤ CMIAudit.baezDuarteDistSq D N)
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_ub : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4UnconstrainedRay G_cot (u_seq N) N
      CMIAudit.baezDuarteDistSq D N ≤
        CMIAudit.vasyuninQuadraticEnergy
          (RiemannBlueprint.Section8_VasyuninBDR.GVasyuninDecomp gamma_E G_cot)
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.bVasyunin k gamma_E) N
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k))
    (h_ray_lim : Filter.Tendsto
      (fun N =>
        RiemannBlueprint.Section8_VasyuninBDR.phiCotUnconstrainedRayQuotient G_cot (u_seq N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4UnconstrainedRay_limit_implies_rh_of_hardyCauchySchwarz
    D pairing szegoNormSq gamma_E G_cot hG_symm u_seq h_hcs h_nonneg hA h_ub h_ray_lim

/-- 27. Tail Coordinate Invariance for `4 < k`:
for every tail index `4 < k`, `clayRank4Hom u N` preserves `u k` identically. -/
theorem clayRank4Hom_eq_self_of_lt_four (u : ℕ → ℝ) (N k : ℕ) (hk : 4 < k) :
    RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom u N k = u k :=
  RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom_eq_self_of_lt_four u N k hk

/-- 28. Fundamental Theorem of Calculus Evaluation for `szegoKernelIntegrand`:
`(∫ t in a..b, szegoKernelIntegrand s₀ t) = szegoKernelAntideriv s₀ b - szegoKernelAntideriv s₀ a`
for `1 / 2 < s₀.re`. -/
theorem integral_szegoKernelIntegrand_eq_sub (s₀ : ℂ) (h_re : 1 / 2 < s₀.re) (a b : ℝ) :
    (∫ t in a..b, CMIAudit.szegoKernelIntegrand s₀ t) =
      CMIAudit.szegoKernelAntideriv s₀ b - CMIAudit.szegoKernelAntideriv s₀ a :=
  CMIAudit.integral_szegoKernelIntegrand_eq_sub s₀ h_re a b

/-- 29. Unconditional Critical-Line Improper Integral Limit of `szegoKernelIntegrand`:
symmetric definite integrals `∫ t in (-T)..T, szegoKernelIntegrand s₀ t` converge as `T → ∞` to
`Complex.normSq s₀ / (2 * s₀.re - 1)` for `1 / 2 < s₀.re`. -/
theorem tendsto_integral_szegoKernelIntegrand_atTop (s₀ : ℂ) (h_re : 1 / 2 < s₀.re) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (-T)..T, CMIAudit.szegoKernelIntegrand s₀ t)
      Filter.atTop (nhds (Complex.normSq s₀ / (2 * s₀.re - 1))) :=
  CMIAudit.tendsto_integral_szegoKernelIntegrand_atTop s₀ h_re

/-- 30. Integral-Grounded Hardy–Cauchy–Schwarz & Unconstrained Ray 1D Limit Implies RH:
requires only the improper integral characterization `SatisfiesIntegralHardyCauchySchwarz` and
unconstrained raw vectors `u_seq`. -/
theorem RiemannHypothesis.of_integralHardyCauchySchwarz_and_unconstrainedRayQuotient_limit
    (D : ℕ → ℝ) (pairing : ℂ → ℕ → ℝ) (szegoNormSq : ℂ → ℝ)
    (gamma_E : ℝ) (G_cot : ℕ → ℕ → ℝ) (hG_symm : ∀ j k, G_cot j k = G_cot k j)
    (u_seq : ℕ → (ℕ → ℝ))
    (h_ihcs : CMIAudit.SatisfiesIntegralHardyCauchySchwarz D pairing szegoNormSq)
    (h_nonneg : ∀ N : ℕ, 0 ≤ CMIAudit.baezDuarteDistSq D N)
    (hA : ∀ N, 4 ≤ N →
      RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        (RiemannBlueprint.Section8_VasyuninBDR.clayRank4Hom (u_seq N) N) N ≠ 0)
    (h_ub : ∀ N, 4 ≤ N →
      let v := RiemannBlueprint.Section8_VasyuninBDR.clayRank4UnconstrainedRay G_cot (u_seq N) N
      CMIAudit.baezDuarteDistSq D N ≤
        CMIAudit.vasyuninQuadraticEnergy
          (RiemannBlueprint.Section8_VasyuninBDR.GVasyuninDecomp gamma_E G_cot)
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.bVasyunin k gamma_E) N
          (fun k => RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base k + v k))
    (h_ray_lim : Filter.Tendsto
      (fun N =>
        RiemannBlueprint.Section8_VasyuninBDR.phiCotUnconstrainedRayQuotient G_cot (u_seq N) N)
      Filter.atTop
      (nhds (1 + RiemannBlueprint.Section8_VasyuninBDR.Q_cot_quad G_cot
        RiemannBlueprint.Section8_VasyuninBDR.clayRank4Base 4))) :
    _root_.RiemannHypothesis :=
  CMIAudit.clayRank4UnconstrainedRay_limit_implies_rh_of_integralHardyCauchySchwarz
    D pairing szegoNormSq gamma_E G_cot hG_symm u_seq h_ihcs h_nonneg hA h_ub h_ray_lim

#print axioms riemannZeta_eq_tsum_harmonicUnitSummand
#print axioms mellin_recipFract_unit_interval
#print axioms riemannZeta_conj_of_pos_re
#print axioms im_ne_zero_of_inCriticalStrip_zeta_zero
#print axioms nymanBeurling_spatial_cauchy_floor
#print axioms baezDuarte_unconstrained_spatial_floor
#print axioms RiemannHypothesis.of_nymanBeurling_approx
#print axioms RiemannHypothesis.of_baezDuarte_approx
#print axioms RiemannHypothesis.of_vasyunin_bdr_cotangent_limit
#print axioms RiemannHypothesis.of_clay_four_boundary_cotangent_limit
#print axioms RiemannHypothesis.of_clayRank4Lock_cotangent_limit
#print axioms RiemannHypothesis.of_clayRank4Lock_Q_cot_quad_limit
#print axioms RiemannHypothesis.of_clayRank4Base_add_hom_Q_cot_quad_limit
#print axioms RiemannHypothesis.of_clayRank4Base_opt_step_limit
#print axioms RiemannHypothesis.of_clayRank4Base_galerkin_hom_limit
#print axioms RiemannHypothesis.of_clayRank4Base_phiCotBase_pairing_limit
#print axioms RiemannHypothesis.of_clayRank4GalerkinRay_rayQuotient_limit
#print axioms zetaZeroReflectionSymmetry
#print axioms RiemannHypothesis.of_szego_and_clayRank4GalerkinRay_rayQuotient_limit
#print axioms totientDefect1_prime
#print axioms primePowerExtraEnergy_prime_pow
#print axioms collapseWeightPurePower_k_eq_one
#print axioms RiemannHypothesis.of_hardyCauchySchwarz_and_clayRank4GalerkinRay_rayQuotient_limit
#print axioms szegoKernelAntideriv_upper_sub_lower
#print axioms hasDerivAt_szegoKernelAntideriv
#print axioms RiemannHypothesis.of_hardyCauchySchwarz_and_unconstrainedRayQuotient_limit
#print axioms clayRank4Hom_eq_self_of_lt_four
#print axioms integral_szegoKernelIntegrand_eq_sub
#print axioms tendsto_integral_szegoKernelIntegrand_atTop
#print axioms RiemannHypothesis.of_integralHardyCauchySchwarz_and_unconstrainedRayQuotient_limit

end MathlibPR.NymanBeurling
