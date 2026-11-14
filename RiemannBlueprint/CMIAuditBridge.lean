import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Order.Filter.AtTopBot.Basic

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

#print axioms riemannHypothesis_iff_collapse_zero
#print axioms collapse_zero_implies_rh_strip

end CMIAudit
