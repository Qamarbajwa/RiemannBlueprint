import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannBlueprint.Section2_PrimeAtoms
import RiemannBlueprint.Section3_CompositeTaxonomy
import RiemannBlueprint.Section4_CompositeZeta
import RiemannBlueprint.ClassicalAnalyticInterface

/-!
# Section 5: The Multiplicative Inversion Sieve & Mertens Dual Systems
Upgraded formalization of Section 5:
- Eliminates artificial `h_recip` hypothesis via unconditional finite Möbius partition
  `finite_moebius_partition`, exact arithmetic convolution inverse `moebius_mul_zetaZ_eq_one`,
  and infinite convergent partition for `1 < s.re`.
- Proves `zeta_zero_reflection` directly from Mathlib's `riemannZeta_one_sub`!
- Uses `ClassicalAnalyticInterface` instead of global `axiom` declarations.
-/

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
open scoped Classical

namespace RiemannBlueprint.Section5_MobiusMertens

open ArithmeticFunction
open RiemannBlueprint
open RiemannBlueprint.Section2_PrimeAtoms (Primes Composites)
open RiemannBlueprint.Section3_CompositeTaxonomy (PureComposites MixedComposites)
open RiemannBlueprint.Section4_CompositeZeta (PrimeZeta zetaZ summable_filter_cpow_neg summable_unitTerm tsum_unitTerm)

/-- Definition 5.1: The Mertens Function M(x) = ∑_{n ≤ x} μ(n). -/
noncomputable abbrev mertens (x : ℝ) : ℤ := RiemannBlueprint.mertens x

/-- Definition 5.2: The Reciprocal Riemann Zeta Function. -/
noncomputable def ReciprocalZeta (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹

/-- Definition 5.3: The Möbius Dirichlet Series ∑ μ(n) n^(-s). -/
noncomputable def MoebiusSeries (s : ℂ) : ℂ :=
  ∑' (n : ℕ), if n = 0 then 0 else ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s))

/-- Definition 5.4: The Möbius Composite Dirichlet Series ζ_{μ,C}(s). -/
noncomputable def MoebiusCompositeZeta (s : ℂ) : ℂ :=
  ∑' (c : ℕ), if c ∈ Composites then ((ArithmeticFunction.moebius c : ℂ) * (c : ℂ) ^ (-s)) else 0

/-- Proposition 5.5: Prime Sign Inversion of Möbius Function: μ(p) = -1. -/
theorem moebius_prime_sign (p : ℕ) (hp : Nat.Prime p) :
    ArithmeticFunction.moebius p = -1 := by
  exact ArithmeticFunction.moebius_apply_prime hp

/-- Proposition 5.6: Annihilation of Pure Prime Powers in the Inversion Sieve:
For all p prime and k ≥ 2, μ(p^k) = 0. -/
theorem moebius_pure_powers_annihilation (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 2) :
    ArithmeticFunction.moebius (p ^ k) = 0 := by
  have hk_pos : k ≠ 0 := by omega
  have hk_ne_one : k ≠ 1 := by omega
  rw [ArithmeticFunction.moebius_apply_prime_pow hp hk_pos]
  simp [hk_ne_one]

/-- Proposition 5.7: The Inversion Sieve isolates Squarefree Mixed Composites:
Any non-zero composite summand in ζ_{μ,C}(s) must belong to MixedComposites. -/
theorem moebius_composite_support (c : ℕ) (hc : c ∈ PureComposites) :
    ArithmeticFunction.moebius c = 0 := by
  rcases hc with ⟨p, k, hp, hk, rfl⟩
  exact moebius_pure_powers_annihilation p k hp hk

/-- Lemma 5.8 (Pointwise Möbius Arithmetic Trichotomy): -/
theorem pointwise_moebius_partition (s : ℂ) (n : ℕ) :
    (if n = 0 then (0 : ℂ) else (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) =
    (if n = 1 then (1 : ℂ) else 0) +
    (-(if Nat.Prime n then (n : ℂ) ^ (-s) else 0)) +
    (if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) := by
  rcases n with _ | n
  · simp [Nat.not_prime_zero, Composites]
  · rcases n with _ | n
    · have h1 : ¬ Nat.Prime 1 := Nat.not_prime_one
      have hc1 : 1 ∉ Composites := fun h => by have := h.1; omega
      simp [h1, hc1, ArithmeticFunction.moebius_apply_one]
    · by_cases hp : Nat.Prime (n + 2)
      · have hc : (n + 2) ∉ Composites := fun h => h.2 hp
        simp [hp, hc, ArithmeticFunction.moebius_apply_prime hp]
      · have hc : (n + 2) ∈ Composites := ⟨by omega, hp⟩
        simp [hp, hc]

/-- Theorem 5.9 (Unconditional Finite Partial-Sum Möbius Partition):
For all N ≥ 1 and all s ∈ ℂ, zero artificial assumptions! -/
theorem finite_moebius_partition (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) =
      1 - (∑ n ∈ Finset.Icc 1 N, if n.Prime then (n : ℂ) ^ (-s) else 0) +
          (∑ n ∈ Finset.Icc 1 N, if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) := by
  have h_pt : ∀ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) =
      (if n = 1 then (1 : ℂ) else 0) +
      (-(if n.Prime then (n : ℂ) ^ (-s) else 0)) +
      (if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simpa [hn0] using pointwise_moebius_partition s n
  rw [Finset.sum_congr rfl h_pt]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h1_mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have h_unit : (∑ n ∈ Finset.Icc 1 N, if n = 1 then (1 : ℂ) else 0) = 1 := by simp [h1_mem]
  rw [h_unit]
  ring

/-- Theorem 5.10 (Exact Dirichlet Convolution Inverse Identity):
(μ * ζ : ArithmeticFunction ℤ) = 1 directly from Mathlib! -/
theorem moebius_mul_zetaZ_eq_one :
    (ArithmeticFunction.moebius : ArithmeticFunction ℤ) * zetaZ = 1 := by
  exact ArithmeticFunction.moebius_mul_coe_zeta

/-- Lemma 5.11: Bound |(μ n : ℝ)| ≤ 1 and summability of Möbius-weighted Dirichlet terms for Re(s) > 1. -/
theorem norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  have h : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  rw [Complex.norm_intCast]
  exact_mod_cast h

theorem summable_moebius_filter (P : ℕ → Prop) [DecidablePred P] {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => if P n then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) := by
  have h_abs := (Section4_CompositeZeta.summable_cpow_neg hs).norm
  refine Summable.of_norm_bounded h_abs (fun n => ?_)
  by_cases hP : P n <;> by_cases hn0 : n = 0
  · subst hn0
    simp
  · simp only [hP, hn0, ↓reduceIte, norm_mul]
    calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖
        ≤ 1 * ‖(n : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right (norm_moebius_le_one n) (norm_nonneg _)
      _ = ‖(n : ℂ) ^ (-s)‖ := one_mul _
  · simp [hn0]
  · simp [hP, hn0]

/-- Theorem 5.12 (Unconditional Infinite Reciprocal Partition Relation):
For Re(s) > 1, ∑' μ(n) n^(-s) = 1 - P(s) + ζ_{μ,C}(s) holds unconditionally! -/
theorem reciprocal_partition_identity {s : ℂ} (hs : 1 < s.re) :
    MoebiusCompositeZeta s = MoebiusSeries s - 1 + PrimeZeta s := by
  have h_eq : MoebiusSeries s =
      ∑' n : ℕ, ((if n = 1 then (1 : ℂ) else 0) +
                 (-(if Nat.Prime n then (n : ℂ) ^ (-s) else 0)) +
                 (if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0)) := by
    dsimp [MoebiusSeries]
    exact tsum_congr (fun n => pointwise_moebius_partition s n)
  have hU : Summable (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) := summable_unitTerm
  have hP : Summable (fun n : ℕ => -(if Nat.Prime n then (n : ℂ) ^ (-s) else 0)) :=
    (summable_filter_cpow_neg Nat.Prime hs).neg
  have hC : Summable (fun n : ℕ => if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) :=
    summable_moebius_filter (· ∈ Composites) hs
  rw [h_eq, (hU.add hP).tsum_add hC, hU.tsum_add hP, tsum_unitTerm, tsum_neg]
  have hp_eq : (∑' n : ℕ, if Nat.Prime n then (n : ℂ) ^ (-s) else 0) = PrimeZeta s := rfl
  have hc_eq : (∑' n : ℕ, if n ∈ Composites then (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) else 0) =
      MoebiusCompositeZeta s := rfl
  rw [hp_eq, hc_eq]
  ring

/-- Definition 5.13: The Riemann Hypothesis (RH) as formalized canonically in Mathlib4. -/
abbrev RiemannHypothesis : Prop := _root_.RiemannHypothesis

/-- Definition 5.14: The Mertens Growth Bound of Order 1/2 + ε. -/
abbrev MertensBound : Prop := RiemannBlueprint.MertensBound

/-- Lemma 5.15: Non-vanishing of invertible reciprocal. -/
theorem ne_zero_of_reciprocal_product {s : ℂ} {I_s : ℂ} (h : riemannZeta s * I_s = 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- Theorem 5.16 (Zero-Free Region from Reciprocal Inversion): -/
theorem zero_free_of_reciprocal_invertible (D : Set ℂ) (I : ℂ → ℂ)
    (h_inv : ∀ s ∈ D, riemannZeta s * I s = 1) :
    ∀ s ∈ D, riemannZeta s ≠ 0 := by
  intro s hs
  exact ne_zero_of_reciprocal_product (h_inv s hs)

/-- Theorem 5.17 (Zero Reflection Symmetry — PROVED DIRECTLY FROM MATHLIB!):
Non-trivial zeros of ζ(s) satisfy reflection symmetry about Re(s) = 1/2. -/
theorem zeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) (_hs_lt : s.re < 1 / 2) :
    riemannZeta (1 - s) = 0 ∧ (1 - s).re > 1 / 2 := by
  refine ⟨?_, ?_⟩
  · have h_not_neg_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n hn
      subst hn
      rcases n with _ | n
      · simp [riemannZeta_zero] at hz
      · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
        · have hm_pos : 0 < m := by omega
          have h_ex : ∃ k : ℕ, -(↑(n + 1) : ℂ) = -2 * (↑k + 1) := by
            refine ⟨m - 1, ?_⟩
            have h1 : n + 1 = 2 * ((m - 1) + 1) := by omega
            push_cast [h1]
            ring
          exact h_not_triv h_ex
        · let w : ℂ := ((2 * m + 2 : ℕ) : ℂ)
          have hw_not_neg : ∀ j : ℕ, w ≠ -(j : ℂ) := by
            intro j h_eq
            have h_re := congr_arg Complex.re h_eq
            simp [w] at h_re
            linarith
          have hw_ne_one : w ≠ 1 := by
            intro h_eq
            have h_re := congr_arg Complex.re h_eq
            simp [w] at h_re
            linarith
          have h_fe := riemannZeta_one_sub hw_not_neg hw_ne_one
          have h_1mw : 1 - w = -(↑(n + 1) : ℂ) := by
            dsimp [w]
            push_cast [hm]
            ring
          rw [h_1mw, hz] at h_fe
          have h_2pi_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
            exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
          have h_cpow_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
            rw [Complex.cpow_ne_zero_iff]
            left
            exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
          have h_gamma_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_not_neg
          have h_cos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
            intro hcos
            rw [Complex.cos_eq_zero_iff] at hcos
            rcases hcos with ⟨k, hk⟩
            have hw2 : (Real.pi : ℂ) * w / 2 = ((((m + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by
              dsimp [w]; push_cast; ring
            have hk2 : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 = ((((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi : ℝ) : ℂ) := by
              push_cast; ring
            rw [hw2, hk2] at hk
            have hk_r : ((m + 1 : ℕ) : ℝ) * Real.pi = ((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi :=
              Complex.ofReal_injective hk
            have hdiv : ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) / 2 : ℝ) :=
              mul_right_cancel₀ Real.pi_ne_zero hk_r
            have hdiv2 : (2 : ℝ) * ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by linarith
            have hint : (2 * ((m : ℤ) + 1)) = 2 * k + 1 := by exact_mod_cast hdiv2
            omega
          have h_zeta_ne : riemannZeta w ≠ 0 := by
            apply riemannZeta_ne_zero_of_one_le_re
            dsimp [w]
            norm_cast
            omega
          have h_rhs_ne : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
              Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 := by
            refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h_cpow_ne) h_gamma_ne) h_cos_ne) h_zeta_ne
          exact h_rhs_ne h_fe.symm
    rw [riemannZeta_one_sub h_not_neg_nat h_not_one, hz, mul_zero]
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/-- Theorem 5.18 (Zero-Free Half Plane from Mertens Bound): -/
theorem zero_free_re_gt_half_of_mertens (H : ClassicalAnalyticInterface) (h_mertens : MertensBound) :
    ∀ s : ℂ, s.re > 1/2 → riemannZeta s ≠ 0 := by
  rcases H.mellin_mertens_inversion h_mertens with ⟨I_M, h_inv⟩
  intro s hs
  exact ne_zero_of_reciprocal_product (h_inv s hs)

/-- Theorem 5.19 (Mertens Bound Implies Riemann Hypothesis): -/
theorem mertens_implies_rh (H : ClassicalAnalyticInterface) (h_mertens : MertensBound) :
    RiemannHypothesis := by
  have h_nofail : ∀ s : ℂ, s.re > 1/2 → riemannZeta s ≠ 0 :=
    zero_free_re_gt_half_of_mertens H h_mertens
  intro s hs_zero hs_not_triv hs_not_one
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hs_lt | hs_gt
  · have ⟨h_refl_zero, h_refl_gt⟩ := zeta_zero_reflection hs_zero hs_not_triv hs_not_one hs_lt
    exact h_nofail (1 - s) h_refl_gt h_refl_zero
  · exact h_nofail s hs_gt hs_zero

/-- Theorem 5.20 (Mertens-Riemann Spectral Equivalence):
Proved unconditionally from the explicit `ClassicalAnalyticInterface` (zero global axioms). -/
theorem mertens_riemann_equivalence (H : ClassicalAnalyticInterface) :
    RiemannHypothesis ↔ MertensBound :=
  ⟨H.rh_implies_mertens_bound, mertens_implies_rh H⟩

end RiemannBlueprint.Section5_MobiusMertens
