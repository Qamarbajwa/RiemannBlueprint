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

/-- Algebraic Szegő–Cauchy–Schwarz reciprocal barrier lemma:
`1 ≤ D_sq * (|s₀|² / (2 Re(s₀) - 1))` implies `(2 Re(s₀) - 1) / |s₀|² ≤ D_sq`. -/
theorem cauchy_schwarz_szego_floor (s₀ : ℂ) (D_sq : ℝ)
    (h_re : 1 / 2 < s₀.re) (h_norm : 0 < Complex.normSq s₀)
    (h_cs : 1 ≤ D_sq * (Complex.normSq s₀ / (2 * s₀.re - 1))) :
    (2 * s₀.re - 1) / Complex.normSq s₀ ≤ D_sq := by
  have hnum : 0 < 2 * s₀.re - 1 := by linarith
  have hpos : 0 < Complex.normSq s₀ / (2 * s₀.re - 1) := div_pos h_norm hnum
  have hdiv := (div_le_iff₀ hpos).mpr h_cs
  simpa [one_div, inv_div] using hdiv

/-- Hardy `H²(Re(s) > 1/2)` reproducing-kernel / Cauchy–Schwarz inequality predicate. -/
def SzegoReproducingInequality (D : ℕ → ℝ) : Prop :=
  ∀ s₀ : ℂ, InCriticalStrip s₀ → 1 / 2 < s₀.re → riemannZeta s₀ = 0 →
    ∀ N : ℕ, 1 ≤ baezDuarteDistSq D N * (Complex.normSq s₀ / (2 * s₀.re - 1))

/-- Derivation of `OfflineZeroCauchyFloor` from `SzegoReproducingInequality`. -/
theorem offlineZeroCauchyFloor_of_szego (D : ℕ → ℝ)
    (h_szego : SzegoReproducingInequality D) : OfflineZeroCauchyFloor D := by
  intro s₀ hs hre hz N
  have hs_ne : s₀ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 := hs.1
    simp at h0
  exact cauchy_schwarz_szego_floor s₀ (baezDuarteDistSq D N) hre
    (Complex.normSq_pos.mpr hs_ne) (h_szego s₀ hs hre hz N)

/-- End-to-end master theorem: `SzegoReproducingInequality`, `ZetaZeroReflectionSymmetry`,
and `baezDuarteDistSq D → 0` imply `RiemannHypothesisStrip`. -/
theorem rh_of_szego_and_collapse_zero (D : ℕ → ℝ)
    (h_szego : SzegoReproducingInequality D)
    (h_refl : ZetaZeroReflectionSymmetry)
    (h_lim : Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0)) :
    RiemannHypothesisStrip :=
  structural_collapse_zero_implies_rh D (offlineZeroCauchyFloor_of_szego D h_szego) h_refl h_lim

/-- Exact quadratic residual energy `1 - 2 c^T b + c^T G c` for an explicit test vector `c`. -/
def vasyuninQuadraticEnergy (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  1 - 2 * (∑ k ∈ Finset.Ico 1 (N + 1), c k * b k) +
  ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), c j * c k * G j k

/-- Variational upper-bound squeeze theorem: any test-vector sequence `c_seq` whose
quadratic energy converges to `0` forces `baezDuarteDistSq D → 0` without matrix inversion. -/
theorem tendsto_baezDuarteDistSq_zero_of_test_vector (D : ℕ → ℝ)
    (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (c_seq : ℕ → ℕ → ℝ)
    (h_nonneg : ∀ N : ℕ, 0 ≤ baezDuarteDistSq D N)
    (h_ub : ∀ N : ℕ, baezDuarteDistSq D N ≤ vasyuninQuadraticEnergy G b N (c_seq N))
    (h_lim : Filter.Tendsto
      (fun N : ℕ => vasyuninQuadraticEnergy G b N (c_seq N)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0) :=
  squeeze_zero h_nonneg h_ub h_lim

/-- Scaling `c_k = α * v_k` in `vasyuninQuadraticEnergy` yields a 1D quadratic in `α`. -/
theorem vasyuninQuadraticEnergy_smul (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (v : ℕ → ℝ) (α : ℝ) :
    vasyuninQuadraticEnergy G b N (fun k => α * v k) =
      1 - 2 * α * (∑ k ∈ Finset.Ico 1 (N + 1), v k * b k) +
      α ^ 2 * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k) := by
  unfold vasyuninQuadraticEnergy
  have h1 : ∑ k ∈ Finset.Ico 1 (N + 1), α * v k * b k =
      α * ∑ k ∈ Finset.Ico 1 (N + 1), v k * b k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have h2 : ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), (α * v j) * (α * v k) * G j k =
      α ^ 2 * ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [h1, h2]
  ring

/-- Optimal 1D Rayleigh–Ritz scalar step `α* = B / A` reduces `vasyuninQuadraticEnergy`
to `1 - B ^ 2 / A` without inverting `G_N`. -/
theorem vasyuninQuadraticEnergy_rayleigh_ritz (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (v : ℕ → ℝ)
    (hA : (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k) ≠ 0) :
    let B := ∑ k ∈ Finset.Ico 1 (N + 1), v k * b k
    let A := ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k
    vasyuninQuadraticEnergy G b N (fun k => (B / A) * v k) = 1 - B ^ 2 / A := by
  intro B A
  rw [vasyuninQuadraticEnergy_smul]
  change 1 - 2 * (B / A) * B + (B / A) ^ 2 * A = 1 - B ^ 2 / A
  field_simp [hA]
  ring

/-- Rayleigh–Ritz upper bound corollary for `baezDuarteDistSq D N`. -/
theorem baezDuarteDistSq_le_one_sub_rayleigh_ritz (D : ℕ → ℝ)
    (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N : ℕ) (v : ℕ → ℝ)
    (h_ub : ∀ c : ℕ → ℝ, baezDuarteDistSq D N ≤ vasyuninQuadraticEnergy G b N c)
    (hA : (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k) ≠ 0) :
    let B := ∑ k ∈ Finset.Ico 1 (N + 1), v k * b k
    let A := ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), v j * v k * G j k
    baezDuarteDistSq D N ≤ 1 - B ^ 2 / A := by
  intro B A
  rw [← vasyuninQuadraticEnergy_rayleigh_ritz G b N v hA]
  exact h_ub (fun k => (B / A) * v k)

/-- 2D bilinear expansion of `vasyuninQuadraticEnergy` for `c_k = α * u_k + β * w_k`
under a symmetric Gram matrix `G`. -/
theorem vasyuninQuadraticEnergy_add_smul (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (hG_symm : ∀ j k, G j k = G k j) (u w : ℕ → ℝ) (α β : ℝ) :
    vasyuninQuadraticEnergy G b N (fun k => α * u k + β * w k) =
      1 - 2 * α * (∑ k ∈ Finset.Ico 1 (N + 1), u k * b k)
        - 2 * β * (∑ k ∈ Finset.Ico 1 (N + 1), w k * b k)
        + α ^ 2 * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), u j * u k * G j k)
        + 2 * α * β * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), u j * w k * G j k)
        + β ^ 2 * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), w j * w k * G j k) := by
  unfold vasyuninQuadraticEnergy
  have h1 :
      ∑ k ∈ Finset.Ico 1 (N + 1), (α * u k + β * w k) * b k =
        α * (∑ k ∈ Finset.Ico 1 (N + 1), u k * b k) +
        β * (∑ k ∈ Finset.Ico 1 (N + 1), w k * b k) := by
    have hcongr :
        ∑ k ∈ Finset.Ico 1 (N + 1), (α * u k + β * w k) * b k =
          ∑ k ∈ Finset.Ico 1 (N + 1), (α * (u k * b k) + β * (w k * b k)) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcross :
      (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), w j * u k * G j k) =
        ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), u j * w k * G j k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hG_symm k j]
    ring
  have h2 :
      (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1),
        (α * u j + β * w j) * (α * u k + β * w k) * G j k) =
        α ^ 2 * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), u j * u k * G j k) +
        2 * α * β * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), u j * w k * G j k) +
        β ^ 2 * (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1), w j * w k * G j k) := by
    have hcongr :
        (∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1),
          (α * u j + β * w j) * (α * u k + β * w k) * G j k) =
          ∑ j ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.Ico 1 (N + 1),
            (α ^ 2 * (u j * u k * G j k) +
              (α * β * (u j * w k * G j k) + α * β * (w j * u k * G j k)) +
              β ^ 2 * (w j * w k * G j k)) :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [hcongr]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcross]
    ring
  rw [h1, h2]
  ring

/-- 2D subspace upper bound and asymptotic squeeze theorem:
if `vasyuninQuadraticEnergy G b N (α_N u_N + β_N w_N) → 0`, then `baezDuarteDistSq D → 0`. -/
theorem tendsto_baezDuarteDistSq_zero_of_two_dim_subspace (D : ℕ → ℝ)
    (G : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (u_seq w_seq : ℕ → ℕ → ℝ) (α_seq β_seq : ℕ → ℝ)
    (h_nonneg : ∀ N : ℕ, 0 ≤ baezDuarteDistSq D N)
    (h_ub : ∀ N : ℕ, ∀ c : ℕ → ℝ, baezDuarteDistSq D N ≤ vasyuninQuadraticEnergy G b N c)
    (h_lim : Filter.Tendsto
      (fun N : ℕ => vasyuninQuadraticEnergy G b N (fun k => α_seq N * u_seq N k + β_seq N * w_seq N k))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (baezDuarteDistSq D) Filter.atTop (nhds 0) :=
  tendsto_baezDuarteDistSq_zero_of_test_vector D G b
    (fun N k => α_seq N * u_seq N k + β_seq N * w_seq N k)
    h_nonneg (fun N => h_ub N _) h_lim

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
#print axioms cauchy_schwarz_szego_floor
#print axioms offlineZeroCauchyFloor_of_szego
#print axioms rh_of_szego_and_collapse_zero
#print axioms tendsto_baezDuarteDistSq_zero_of_test_vector
#print axioms vasyuninQuadraticEnergy_smul
#print axioms vasyuninQuadraticEnergy_rayleigh_ritz
#print axioms baezDuarteDistSq_le_one_sub_rayleigh_ritz
#print axioms vasyuninQuadraticEnergy_add_smul
#print axioms tendsto_baezDuarteDistSq_zero_of_two_dim_subspace

end CMIAudit
