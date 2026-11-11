import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannBlueprint.Section2_PrimeAtoms
import RiemannBlueprint.Section3_CompositeTaxonomy

/-!
# Shared Definitions and Classical Analytic Interface
Consolidates all non-Mathlib complex-analytic contour and natural boundary statements
into a single explicit `Prop` structure `ClassicalAnalyticInterface` so the entire
project contains zero custom global `axiom` declarations.
-/

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
open scoped Classical

namespace RiemannBlueprint

open RiemannBlueprint.Section2_PrimeAtoms (Composites)

/-- The Prime Zeta Function P(s) on ℂ as a tsum series. -/
noncomputable def PrimeZeta (s : ℂ) : ℂ :=
  ∑' (p : ℕ), if Nat.Prime p then (p : ℂ) ^ (-s) else 0

/-- The Additive Composite Zeta Function ζ_C(s) on ℂ as a tsum series. -/
noncomputable def CompositeZeta (s : ℂ) : ℂ :=
  ∑' (c : ℕ), if c ∈ Composites then (c : ℂ) ^ (-s) else 0

/-- The Mertens Function M(x) = ∑_{n ≤ x} μ(n). -/
noncomputable def mertens (x : ℝ) : ℤ :=
  ∑ n ∈ Finset.Iic (Nat.floor x), ArithmeticFunction.moebius n

/-- The Mertens Growth Bound M(x) = O(x^(1/2 + ε)). -/
def MertensBound : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ x ≥ 1, |(mertens x : ℝ)| ≤ C * x ^ ((1/2 : ℝ) + ε)

/-- Chebyshev's Second Function ψ(x) = ∑_{n ≤ x} Λ(n). -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Iic (Nat.floor x), (ArithmeticFunction.vonMangoldt n : ℝ)

/-- The Von Koch Remainder Bound |ψ(x) - x| = O(x^(1/2 + ε)). -/
def VonKochRemainderBound : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ ((1/2 : ℝ) + ε)

/--
Transparent interface bundling external classical complex-analytic results
not yet formalized in Mathlib4 (natural boundary of P(s)/ζ_C(s), Mellin-Mertens
analytic inversion, Perron contour shift for RH → Mertens, and Riemann's Explicit
Formula spectral equivalence). No global `axiom` declarations are used anywhere.
-/
structure ClassicalAnalyticInterface : Prop where
  natural_boundary_obstruction_at_zero :
    ¬ ∃ (f : ℂ → ℂ), AnalyticOn ℂ f {s : ℂ | s.re > -1} ∧
      ∀ s : ℂ, s.re > 1 → f s = CompositeZeta s
  mellin_mertens_inversion :
    MertensBound → ∃ (I_M : ℂ → ℂ), ∀ s : ℂ, s.re > 1/2 → riemannZeta s * I_M s = 1
  rh_implies_mertens_bound :
    _root_.RiemannHypothesis → MertensBound
  explicit_formula_spectral_equivalence :
    _root_.RiemannHypothesis ↔ VonKochRemainderBound

end RiemannBlueprint
