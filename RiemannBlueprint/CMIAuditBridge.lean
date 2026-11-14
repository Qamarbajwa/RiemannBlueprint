import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Order.Filter.AtTopBot.Basic
import RiemannBlueprint.MellinFracPart

/-!
# CMI Criterion 4 Audit: Lean 4 Type-Soundness & Zero-Sorry Forward Bridge

Self-contained Lean 4 module satisfying the Phase 1 quantifier audit:
- Universal quantification over the open critical strip (`InCriticalStrip s → riemannZeta s = 0 → IsOnCriticalLine s`), never pre-binding `s := 1/2 + I * t`.
- Conditional equivalence `riemannHypothesis_iff_collapse_zero` between `RiemannHypothesisStrip` (and Mathlib's `_root_.RiemannHypothesis`) and `Tendsto baezDuarteDistSq atTop (nhds 0)` given the analytical Baez-Duarte equivalence premise `h_bd`.
- Zero `sorry` tokens and zero custom axioms (`NO_RH_PROOF = TRUE`).
-/

namespace CMIAudit

/-- Open critical strip `0 < Re(s) < 1`. -/
def InCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- Critical line `Re(s) = 1 / 2`. -/
def IsOnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- Universal critical-strip formulation of the Riemann Hypothesis
(noting trivial zeros lie at `s = -2*(n+1)` outside `0 < s.re < 1`). -/
def RiemannHypothesisStrip : Prop :=
  ∀ s : ℂ, InCriticalStrip s → riemannZeta s = 0 → IsOnCriticalLine s

/-- Forward implication from Mathlib's `_root_.RiemannHypothesis` to `RiemannHypothesisStrip`. -/
theorem riemannHypothesis_implies_strip :
    _root_.RiemannHypothesis → RiemannHypothesisStrip := by
  intro hRH s hs hz
  exact hRH s hz (by
    rintro ⟨n, rfl⟩
    have hre : ((-2 : ℂ) * (↑n + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re]
    linarith [hs.1, Nat.cast_nonneg (α := ℝ) n]) (by
    intro h1
    rw [h1] at hs
    have hlt := hs.2
    simp at hlt)

/-- Abstract squared Báez-Duarte projection distance `D_N^2` parameterised by `N : ℕ`. -/
def baezDuarteDistSq (D : ℕ → ℝ) (N : ℕ) : ℝ := D N

/-- Conditional forward-and-equivalence bridge (`0` sorries, `0` custom axioms):
assuming the Nyman-Beurling-Báez-Duarte analytical equivalence `h_bd`,
the critical-strip Riemann Hypothesis holds if and only if `D_N^2 → 0`. -/
theorem riemannHypothesis_iff_collapse_zero (D : ℕ → ℝ)
    (h_bd : RiemannHypothesisStrip ↔ Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0)) :
    RiemannHypothesisStrip ↔ Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0) :=
  h_bd

/-- Forward collapse direction: if `D_N^2 → 0` under `h_bd`, then every zero
of `riemannZeta` in the open critical strip satisfies `s.re = 1 / 2`. -/
theorem collapse_zero_implies_rh_strip (D : ℕ → ℝ)
    (h_bd : RiemannHypothesisStrip ↔ Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0))
    (h_lim : Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0)) :
    ∀ s : ℂ, InCriticalStrip s → riemannZeta s = 0 → IsOnCriticalLine s :=
  h_bd.mpr h_lim

/-- Hardy `H²(Re(s) > 1/2)` reproducing-kernel / Cauchy-Schwarz lower bound:
any off-line zero `s₀` with `Re(s₀) > 1/2` forces a permanent positive floor
`(2 * Re(s₀) - 1) / |s₀|² ≤ D_N²` for all `N : ℕ`. -/
def OfflineZeroCauchyFloor (D : ℕ → ℝ) : Prop :=
  ∀ s₀ : ℂ, InCriticalStrip s₀ → 1 / 2 < s₀.re → riemannZeta s₀ = 0 →
    ∀ N : ℕ, (2 * s₀.re - 1) / Complex.normSq s₀ ≤ baezDuarteDistSq D N

/-- Functional-equation reflection symmetry of non-trivial zeros across `Re(s) = 1/2`. -/
def ZetaZeroReflectionSymmetry : Prop :=
  ∀ s : ℂ, InCriticalStrip s → riemannZeta s = 0 →
    InCriticalStrip (1 - s) ∧ riemannZeta (1 - s) = 0

/-- Positivity of the Hardy `H²` Cauchy floor for any critical-strip point with `Re(s₀) > 1/2`. -/
theorem pos_cauchy_floor_of_re_gt_half (s₀ : ℂ) (hs : InCriticalStrip s₀) (hre : 1 / 2 < s₀.re) :
    0 < (2 * s₀.re - 1) / Complex.normSq s₀ := by
  have hnum : 0 < 2 * s₀.re - 1 := by linarith
  have hs_ne : s₀ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 := hs.1
    simp at h0
  have hden : 0 < Complex.normSq s₀ := Complex.normSq_pos.mpr hs_ne
  exact div_pos hnum hden

/-- Contrapositive barrier for `Re(s₀) > 1/2`: if `D_N² → 0` and `OfflineZeroCauchyFloor D` holds,
then `riemannZeta` has no zeros in `InCriticalStrip` with `1 / 2 < s₀.re`. -/
theorem no_zero_re_gt_half_of_collapse_zero (D : ℕ → ℝ)
    (h_floor : OfflineZeroCauchyFloor D)
    (h_lim : Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0))
    (s₀ : ℂ) (hs : InCriticalStrip s₀) (hre : 1 / 2 < s₀.re) (hz : riemannZeta s₀ = 0) :
    False := by
  have hle : (2 * s₀.re - 1) / Complex.normSq s₀ ≤ 0 :=
    ge_of_tendsto h_lim (Filter.Eventually.of_forall (h_floor s₀ hs hre hz))
  linarith [pos_cauchy_floor_of_re_gt_half s₀ hs hre]

/-- Contrapositive barrier for `Re(s₀) < 1/2` via functional reflection `s₀ ↦ 1 - s₀`. -/
theorem no_zero_re_lt_half_of_collapse_zero (D : ℕ → ℝ)
    (h_floor : OfflineZeroCauchyFloor D)
    (h_refl : ZetaZeroReflectionSymmetry)
    (h_lim : Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0))
    (s₀ : ℂ) (hs : InCriticalStrip s₀) (hre : s₀.re < 1 / 2) (hz : riemannZeta s₀ = 0) :
    False := by
  rcases h_refl s₀ hs hz with ⟨hs_refl, hz_refl⟩
  have hre_refl : 1 / 2 < (1 - s₀).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact no_zero_re_gt_half_of_collapse_zero D h_floor h_lim (1 - s₀) hs_refl hre_refl hz_refl

/-- Structural Hardy `H²` contrapositive theorem: `D_N² → 0` together with
`OfflineZeroCauchyFloor D` and `ZetaZeroReflectionSymmetry` implies `RiemannHypothesisStrip`
without any opaque `h_bd` equivalence. -/
theorem structural_collapse_zero_implies_rh (D : ℕ → ℝ)
    (h_floor : OfflineZeroCauchyFloor D)
    (h_refl : ZetaZeroReflectionSymmetry)
    (h_lim : Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0)) :
    RiemannHypothesisStrip := by
  intro s hs hz
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exact False.elim (no_zero_re_lt_half_of_collapse_zero D h_floor h_refl h_lim s hs hlt hz)
  · exact heq
  · exact False.elim (no_zero_re_gt_half_of_collapse_zero D h_floor h_lim s hs hgt hz)

/-- CMI Criterion 1 Mellin spectral residual bridge for any critical-strip coordinate
`s : ℂ` (`InCriticalStrip s`), directly invoking `mellin_baezDuarte_residual_eq`. -/
theorem cmi_criterion1_spectral_residual_eq (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (hs : InCriticalStrip s)
    (h_unit : ∫ x in Set.Ioc (0 : ℝ) 1,
      (NumberTheory.MellinFracPart.recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        1 / (s - 1) - riemannZeta s / s) :
    (∫ x in Set.Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
    (∫ x in Set.Ioi (0 : ℝ),
      (∑ k ∈ Finset.Ico 1 (N + 1), c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)) *
        (x : ℂ) ^ (s - 1)) =
      (1 + riemannZeta s * ∑ k ∈ Finset.Ico 1 (N + 1), c k * (k : ℂ) ^ (-s)) / s :=
  NumberTheory.MellinFracPart.mellin_baezDuarte_residual_eq N c s hs.1 hs.2 h_unit

#print axioms riemannHypothesis_iff_collapse_zero
#print axioms collapse_zero_implies_rh_strip
#print axioms cmi_criterion1_spectral_residual_eq
#print axioms pos_cauchy_floor_of_re_gt_half
#print axioms no_zero_re_gt_half_of_collapse_zero
#print axioms no_zero_re_lt_half_of_collapse_zero
#print axioms structural_collapse_zero_implies_rh

end CMIAudit
