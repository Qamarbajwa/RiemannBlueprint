import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannBlueprint.Section2_PrimeAtoms
import RiemannBlueprint.Section3_CompositeTaxonomy
import RiemannBlueprint.Section4_CompositeZeta
import RiemannBlueprint.Section5_MobiusMertens
import RiemannBlueprint.Section6_CriticalStripAudit
import RiemannBlueprint.ClassicalAnalyticInterface

/-!
# Section 7: The Explicit Formula & Spectral Equivalences
Upgraded formalization of Section 7:
- Re-exports `chebyshevPsi` and `VonKochRemainderBound`.
- Replaces bare `axiom explicit_formula_spectral_equivalence` with explicit `(H : ClassicalAnalyticInterface)` hypothesis.
-/

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
open scoped Classical

namespace RiemannBlueprint.Section7_SpectralBridge

open RiemannBlueprint
open RiemannBlueprint.Section2_PrimeAtoms (Primes Composites)
open RiemannBlueprint.Section3_CompositeTaxonomy (PureComposites MixedComposites omega)
open RiemannBlueprint.Section5_MobiusMertens (MertensBound mertens_riemann_equivalence)

/-- Definition 7.1: Chebyshev's First Function θ(x) = ∑_{p ≤ x} ln(p). -/
noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic (Nat.floor x)), Real.log (p : ℝ)

/-- Definition 7.2: Chebyshev's Second Function ψ(x) = ∑_{n ≤ x} Λ(n). -/
noncomputable abbrev chebyshevPsi (x : ℝ) : ℝ := RiemannBlueprint.chebyshevPsi x

/-- Proposition 7.3: Von Mangoldt Weight Annihilation on Mixed Composites.
Mixed composites contribute zero weight to the Chebyshev function ψ(x). -/
theorem mixed_composites_von_mangoldt_vanish (n : ℕ) (hn : n ∈ MixedComposites) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  have h_omega : omega n ≥ 2 := hn.2
  exact RiemannBlueprint.Section3_CompositeTaxonomy.von_mangoldt_isolation n h_omega

/-- Definition 7.4: The Von Koch Remainder Bound of Order 1/2 + ε. -/
abbrev VonKochRemainderBound : Prop := RiemannBlueprint.VonKochRemainderBound

/-- Theorem 7.5 (Spectral Stability Theorem):
Under the explicit classical analytic interface, the Riemann Hypothesis is equivalent
to the optimal square-root remainder bound for Chebyshev's prime counting function. -/
theorem spectral_stability_theorem (H : ClassicalAnalyticInterface) :
    _root_.RiemannHypothesis ↔ VonKochRemainderBound :=
  H.explicit_formula_spectral_equivalence

/-- Theorem 7.6 (Master Dual-System Equivalence):
The Mertens squarefree inversion bound is equivalent to the Chebyshev prime-power
remainder bound via the spectral zeros of the Riemann zeta function. -/
theorem master_dual_system_equivalence (H : ClassicalAnalyticInterface) :
    MertensBound ↔ VonKochRemainderBound :=
  (mertens_riemann_equivalence H).symm.trans (spectral_stability_theorem H)

end RiemannBlueprint.Section7_SpectralBridge
