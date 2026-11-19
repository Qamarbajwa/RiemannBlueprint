/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannBlueprint.UnconditionalTitchmarshBridge
import RiemannBlueprint.UpstreamPRs.UpstreamPR_8U_EuclideanExhaustionTailBound

/-!
# Matrix Factorization, Exact Möbius–Difference Inversion, and Half-Observation Laws

This module transcribes the Báez–Duarte / Vasyunin / Riemann Zeta framework into explicit
matrix relations and proves the three half-observation theorems without additional axioms:

* **Part I (Additive–Multiplicative Factorization & Exact Inversion):**
  `floorMatrix M N = cumSumMatrix M * divisorMatrix M N`,
  `firstDiffMatrix M * cumSumMatrix M = 1`,
  `mobiusMatrix M * divisorMatrix M M = 1`, and
  `(mobiusMatrix M * firstDiffMatrix M) * floorMatrix M M = 1`.
* **Part II (Three-Matrix Sandwich Energy & Lebesgue Bridge):**
  `residualVec c M N = onesVec M + (cumSumMatrix M * divisorMatrix M N).mulVec (coeffVec c N)`,
  identifying `harmonicCellL2PartialSum c N M` and `∫ x in Ioc (1/(M+1)) 1, residual^2`
  with the diagonal quadratic form `rᵀ W_M r` and proving the Book X.1 tail bound.
* **Part III (Half-Observation Laws — Spatial & Palindromic Period):**
  `upperHalf_observation_zero` (vanishing on `(1/2, 1]` under Dirichlet anchoring),
  `halfObservation_quadForm_eq_double_half` (abstract reversal involution `J` folding), and
  `harmonicCellL2PartialSum_period_eq_double_halfObservation` (exact `[1, L-2]` period folding
  onto `[1, H]` with symmetric double-cone weights `W̄_half = (1/2) • (W_L + J W_R J)`).
* **Part IV (Core `(N - 2) × (N - 2)` Matrices & Half-Plane Matrix RH Criterion):**
  `dipoleGramMatrix`, `purePlaqueMatrix`, and `unitDefectMatrix`, rank-2 boundary shifts,
  universal superdiagonal zeros `dipoleGramMatrix_superdiag_eq_zero`, unconditional
  off-line zero floor `unitDefectMatrix_offline_zero_floor_unconditional` on `Re(s) > 1/2`,
  and `riemannHypothesis_of_unitDefectMatrix_vanishing_unconditional`.
-/

namespace RiemannBlueprint.MatrixHalfObservation

open scoped BigOperators Matrix
open MeasureTheory Set Finset

private lemma sum_fin_succ_eq_sum_Icc (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, f (i.1 + 1)) = ∑ m ∈ Finset.Icc 1 n, f m := by
  refine Finset.sum_bij (fun i _ => i.1 + 1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _; exact Finset.mem_Icc.mpr ⟨by omega, i.isLt⟩
  · intro i₁ _ i₂ _ h; exact Fin.ext (by omega)
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    refine ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp; omega

/-! ## Part I: Additive–Multiplicative Factorization & Exact Inversion -/

/-- Lower-triangular summation matrix `Σ` (`M × M`): `(i, m) ↦ 1` if `m ≤ i`, else `0`. -/
def cumSumMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i m => if m.1 ≤ i.1 then 1 else 0

/-- Divisibility incidence matrix `D` (`M × N`): `(m, j) ↦ 1` if `(j + 1) ∣ (m + 1)`, else `0`. -/
def divisorMatrix (M N : ℕ) : Matrix (Fin M) (Fin N) ℝ :=
  fun m j => if j.1 + 1 ∣ m.1 + 1 then 1 else 0

/-- Integer-floor quotient matrix `F` (`M × N`): `(i, j) ↦ ⌊(i + 1) / (j + 1)⌋`. -/
def floorMatrix (M N : ℕ) : Matrix (Fin M) (Fin N) ℝ :=
  fun i j => (((i.1 + 1) / (j.1 + 1) : ℕ) : ℝ)

/-- Backward first-difference matrix `Δ` (`M × M`), the left/right inverse of `Σ`. -/
def firstDiffMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i m => if i.1 = m.1 then 1 else if i.1 = m.1 + 1 then -1 else 0

/-- Möbius divisor-inversion matrix `M_μ` (`M × M`): `(i, m) ↦ μ((i + 1)/(m + 1))` when
`(m + 1) ∣ (i + 1)`, else `0`. -/
def mobiusMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i m => if m.1 + 1 ∣ i.1 + 1 then (ArithmeticFunction.moebius ((i.1 + 1) / (m.1 + 1)) : ℝ)
    else 0

private lemma card_Icc_filter_dvd (n d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 n).filter (d ∣ ·)).card = n / d := by
  have hdpos : 0 < d := by omega
  have hbij : ((Finset.Icc 1 n).filter (d ∣ ·)).card = (Finset.range (n / d)).card := by
    symm
    refine Finset.card_bij (fun q _ => (q + 1) * d) ?_ ?_ ?_
    · intro q hq
      have hq' : q < n / d := Finset.mem_range.mp hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) hdpos, ?_⟩,
        dvd_mul_left d (q + 1)⟩
      exact (Nat.mul_le_mul_right d (by omega : q + 1 ≤ n / d)).trans (Nat.div_mul_le_self n d)
    · intro q₁ _ q₂ _ h
      have := Nat.mul_right_cancel hdpos h
      omega
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hm_icc, hdvd⟩
      rcases hdvd with ⟨q, hdq⟩
      have hm_pos : 1 ≤ d * q := by rw [← hdq]; exact (Finset.mem_Icc.mp hm_icc).1
      have hm_le : d * q ≤ n := by rw [← hdq]; exact (Finset.mem_Icc.mp hm_icc).2
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hqpos
        · simp at hm_pos
        · exact hqpos
      have hq_le : q ≤ n / d := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [mul_comm] using hm_le)
      refine ⟨q - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show q - 1 + 1 = q by omega, mul_comm, hdq]
  rw [hbij, Finset.card_range]

/-- **Two-Matrix Additive–Multiplicative Factorization**: `F = Σ * D` for all dimensions `M, N`. -/
theorem floorMatrix_eq_cumSum_mul_divisor (M N : ℕ) :
    floorMatrix M N = cumSumMatrix M * divisorMatrix M N := by
  ext i j
  rw [Matrix.mul_apply]
  have hi : i.1 < M := i.isLt
  have h1 : (∑ m : Fin M, cumSumMatrix M i m * divisorMatrix M N m j) =
      ∑ m ∈ (Finset.univ : Finset (Fin M)),
        if m.1 ≤ i.1 ∧ j.1 + 1 ∣ m.1 + 1 then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp [cumSumMatrix, divisorMatrix]
    by_cases hm : m.1 ≤ i.1 <;> by_cases hd : j.1 + 1 ∣ m.1 + 1 <;> simp [hm, hd]
  have h2 : (∑ m ∈ (Finset.univ : Finset (Fin M)),
        if m.1 ≤ i.1 ∧ j.1 + 1 ∣ m.1 + 1 then (1 : ℝ) else 0) =
      ∑ n ∈ (Finset.Icc 1 (i.1 + 1)).filter (j.1 + 1 ∣ ·), (1 : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun m _ => m.1 + 1) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨_, hmi, hd⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hd⟩
    · intro m₁ _ m₂ _ h
      exact Fin.ext (by omega)
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn_icc, hd⟩
      have hn' := Finset.mem_Icc.mp hn_icc
      refine ⟨⟨n - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · dsimp; omega
      · dsimp; rwa [show n - 1 + 1 = n by omega]
      · dsimp; omega
  rw [h1, h2, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_Icc_filter_dvd (i.1 + 1) (j.1 + 1) (by omega)]
  rfl

/-- **Left Inversion of Summation**: `Δ * Σ = I` for every dimension `M`. -/
theorem firstDiffMatrix_mul_cumSumMatrix (M : ℕ) :
    firstDiffMatrix M * cumSumMatrix M = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
  · have hsum : (∑ m : Fin M, firstDiffMatrix M i m * cumSumMatrix M m j) =
        if j.1 ≤ 0 then 1 else 0 := by
      have hterm : ∀ m : Fin M, firstDiffMatrix M i m * cumSumMatrix M m j =
          if m = i then (if j.1 ≤ 0 then 1 else 0) else 0 := fun m => by
        dsimp [firstDiffMatrix, cumSumMatrix]
        by_cases hm : m = i
        · subst hm; simp [hi0]
        · have hne1 : i.1 ≠ m.1 := fun h => hm (Fin.ext h.symm)
          have hne2 : i.1 ≠ m.1 + 1 := by omega
          simp [hne1, hne2, hm]
      rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq']
      simp
    rw [hsum]
    by_cases hji : i = j
    · subst hji; simp [hi0]
    · have hjne0 : ¬ j.1 ≤ 0 := fun hle => hji (Fin.ext (by omega))
      simp [hji, hjne0]
  · set p : Fin M := ⟨i.1 - 1, by omega⟩
    have hp_ne : p ≠ i := fun h => by
      have := congrArg Fin.val h
      dsimp [p] at this
      omega
    have hterm : ∀ m : Fin M, firstDiffMatrix M i m * cumSumMatrix M m j =
        (if m = i then (if j.1 ≤ i.1 then 1 else 0) else 0) +
          (if m = p then (if j.1 ≤ i.1 - 1 then -1 else 0) else 0) := fun m => by
      dsimp [firstDiffMatrix, cumSumMatrix]
      by_cases hmi : m = i
      · subst hmi; simp [hp_ne.symm]
      · by_cases hmp : m = p
        · subst hmp
          have hne1 : i.1 ≠ p.1 := by dsimp [p]; omega
          have heq2 : i.1 = p.1 + 1 := by dsimp [p]; omega
          simp [heq2, hp_ne]
        · have hne1 : i.1 ≠ m.1 := fun h => hmi (Fin.ext h.symm)
          have hne2 : i.1 ≠ m.1 + 1 := fun h => hmp (Fin.ext (by dsimp [p]; omega))
          simp [hne1, hne2, hmi, hmp]
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    by_cases hji : i = j
    · subst hji
      have hnot : ¬ i.1 ≤ i.1 - 1 := by omega
      simp [hnot]
    · simp only [Matrix.one_apply, hji, ↓reduceIte]
      by_cases hle : j.1 ≤ i.1
      · have hle1 : j.1 ≤ i.1 - 1 := by
          have hne : j.1 ≠ i.1 := fun h => hji (Fin.ext h.symm)
          omega
        simp [hle, hle1]
      · have hnot : ¬ j.1 ≤ i.1 - 1 := by omega
        simp [hle, hnot]

private lemma sum_moebius_div_divisors (q : ℕ) (_hq : 1 ≤ q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℝ)) = if q = 1 then 1 else 0 := by
  have hZ := congrArg (fun f : ArithmeticFunction ℝ => f q)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply,
    Nat.sum_divisorsAntidiagonal' (fun x₁ x₂ =>
      (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) x₁ *
        (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) x₂)] at hZ
  have hsum : (∑ d ∈ q.divisors,
      (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) (q / d) *
        (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) d) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℝ) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hd0]
  rw [hsum] at hZ
  exact hZ

/-- **Left Möbius Inversion of Divisibility**: `M_μ * D = I` for every dimension `M`. -/
theorem mobiusMatrix_mul_divisorMatrix (M : ℕ) :
    mobiusMatrix M * divisorMatrix M M = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have haM : i.1 + 1 ≤ M := i.isLt
  by_cases hba : j.1 + 1 ∣ i.1 + 1
  · rcases hba with ⟨q, hq⟩
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | hqp
      · simp at hq
      · exact hqp
    have hsum : (∑ m : Fin M, mobiusMatrix M i m * divisorMatrix M M m j) =
        ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℝ) := by
      have hterm : ∀ m : Fin M, mobiusMatrix M i m * divisorMatrix M M m j =
          if m.1 + 1 ∣ i.1 + 1 ∧ j.1 + 1 ∣ m.1 + 1 then
            (ArithmeticFunction.moebius ((i.1 + 1) / (m.1 + 1)) : ℝ) else 0 := fun m => by
        dsimp [mobiusMatrix, divisorMatrix]
        by_cases h1 : m.1 + 1 ∣ i.1 + 1 <;> by_cases h2 : j.1 + 1 ∣ m.1 + 1 <;> simp [h1, h2]
      rw [Finset.sum_congr rfl fun m _ => hterm m, ← Finset.sum_filter]
      refine Finset.sum_bij (fun m _ => (m.1 + 1) / (j.1 + 1)) ?_ ?_ ?_ ?_
      · intro m hm
        rcases Finset.mem_filter.mp hm with ⟨_, hc_dvd_a, hb_dvd_c⟩
        rcases hb_dvd_c with ⟨d, hd_eq⟩
        have hc_div : (m.1 + 1) / (j.1 + 1) = d := by
          rw [hd_eq, Nat.mul_div_right d (by omega)]
        rw [hc_div]
        refine Nat.mem_divisors.mpr ⟨?_, by omega⟩
        rcases hc_dvd_a with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        apply Nat.mul_left_cancel (by omega : 0 < j.1 + 1)
        calc (j.1 + 1) * q = i.1 + 1 := hq.symm
          _ = (m.1 + 1) * r := hr
          _ = (j.1 + 1) * (d * r) := by rw [hd_eq, mul_assoc]
      · intro m₁ hm₁ m₂ hm₂ h
        rcases Finset.mem_filter.mp hm₁ with ⟨_, _, hb₁⟩
        rcases Finset.mem_filter.mp hm₂ with ⟨_, _, hb₂⟩
        have hc : m₁.1 + 1 = m₂.1 + 1 := by
          calc m₁.1 + 1 = (j.1 + 1) * ((m₁.1 + 1) / (j.1 + 1)) := (Nat.mul_div_cancel' hb₁).symm
            _ = (j.1 + 1) * ((m₂.1 + 1) / (j.1 + 1)) := by rw [h]
            _ = m₂.1 + 1 := Nat.mul_div_cancel' hb₂
        exact Fin.ext (by omega)
      · intro d hd
        rcases Nat.mem_divisors.mp hd with ⟨⟨r, hqdr⟩, _⟩
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        have hbd_le_a : (j.1 + 1) * d ≤ i.1 + 1 := by
          have hr1 : 1 ≤ r := by
            rcases Nat.eq_zero_or_pos r with rfl | hrp
            · simp at hqdr; omega
            · exact hrp
          calc (j.1 + 1) * d ≤ (j.1 + 1) * (d * r) :=
              Nat.mul_le_mul_left (j.1 + 1) (Nat.le_mul_of_pos_right d hr1)
            _ = (j.1 + 1) * q := by rw [hqdr]
            _ = i.1 + 1 := hq.symm
        have hbd_pos : 1 ≤ (j.1 + 1) * d := Nat.mul_pos (by omega) hd1
        refine ⟨⟨(j.1 + 1) * d - 1, by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
        · dsimp
          rw [show (j.1 + 1) * d - 1 + 1 = (j.1 + 1) * d by omega]
          exact ⟨r, by calc i.1 + 1 = (j.1 + 1) * q := hq
            _ = (j.1 + 1) * (d * r) := by rw [hqdr]
            _ = (j.1 + 1) * d * r := by ring⟩
        · dsimp
          rw [show (j.1 + 1) * d - 1 + 1 = (j.1 + 1) * d by omega]
          exact dvd_mul_right (j.1 + 1) d
        · dsimp
          rw [show (j.1 + 1) * d - 1 + 1 = (j.1 + 1) * d by omega,
            Nat.mul_div_right d (by omega)]
      · intro m hm
        rcases Finset.mem_filter.mp hm with ⟨_, _, hb_dvd_c⟩
        rcases hb_dvd_c with ⟨d, hd_eq⟩
        have hc_div : (m.1 + 1) / (j.1 + 1) = d := by
          rw [hd_eq, Nat.mul_div_right d (by omega)]
        rw [hc_div, hq, hd_eq, Nat.mul_div_mul_left q d (by omega)]
    rw [hsum, sum_moebius_div_divisors q hq1]
    by_cases hij : i = j
    · have hq_one : q = 1 := by
        have hab : i.1 + 1 = j.1 + 1 := by rw [hij]
        apply Nat.mul_left_cancel (by omega : 0 < j.1 + 1)
        linarith [hq]
      simp [Matrix.one_apply, hij, hq_one]
    · have hq_ne : q ≠ 1 := by
        intro hq1'
        apply hij
        apply Fin.ext
        have : i.1 + 1 = j.1 + 1 := by rw [hq, hq1', mul_one]
        omega
      simp [hij, hq_ne]
  · have hzero : ∀ m : Fin M, mobiusMatrix M i m * divisorMatrix M M m j = 0 := fun m => by
      dsimp [mobiusMatrix, divisorMatrix]
      by_cases h1 : m.1 + 1 ∣ i.1 + 1
      · have h2 : ¬ j.1 + 1 ∣ m.1 + 1 := fun h => hba (dvd_trans h h1)
        simp [h1, h2]
      · simp [h1]
    have hij : i ≠ j := fun h => hba (by simp [h])
    simp [Finset.sum_congr rfl fun m _ => hzero m, hij]

/-- **Exact Additive–Multiplicative Left Inverse of `floorMatrix`**:
`(M_μ * Δ) * F = I` for every dimension `M`. -/
theorem inverse_floorMatrix_mul (M : ℕ) :
    (mobiusMatrix M * firstDiffMatrix M) * floorMatrix M M = 1 := by
  rw [floorMatrix_eq_cumSum_mul_divisor, Matrix.mul_assoc,
    ← Matrix.mul_assoc (firstDiffMatrix M) (cumSumMatrix M) (divisorMatrix M M),
    firstDiffMatrix_mul_cumSumMatrix, Matrix.one_mul, mobiusMatrix_mul_divisorMatrix]

/-! ## Part II: Three-Matrix Sandwich Energy Form & Lebesgue Bridge -/

/-- Diagonal harmonic slab-width matrix `W_M = diag(1 / (n * (n + 1)))`. -/
noncomputable def slabWeightMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.diagonal fun i => harmonicCellWidth (i.1 + 1)

/-- Constant all-ones vector `1_n : Fin n → ℝ`. -/
def onesVec (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- Finite coefficient vector `cVec = (c 1, ..., c N)`. -/
def coeffVec (c : ℕ → ℝ) (N : ℕ) : Fin N → ℝ := fun j => c (j.1 + 1)

/-- Discrete cell residual vector `r_M(n) = discreteCellResidual c N n` for `1 ≤ n ≤ M`. -/
noncomputable def residualVec (c : ℕ → ℝ) (M N : ℕ) : Fin M → ℝ :=
  fun i => discreteCellResidual c N (i.1 + 1)

/-- **Factorized Matrix-Vector Residual Law**: `r_M = 1_M + (Σ_M * D_{M,N}) *ᵥ c_N`. -/
theorem residualVec_eq_ones_add_factorized (c : ℕ → ℝ) (M N : ℕ) :
    residualVec c M N = onesVec M + (cumSumMatrix M * divisorMatrix M N).mulVec (coeffVec c N) := by
  rw [← floorMatrix_eq_cumSum_mul_divisor]
  ext i
  simp only [Pi.add_apply, residualVec, onesVec, Matrix.mulVec, dotProduct,
    floorMatrix, coeffVec, discreteCellResidual]
  congr 1
  rw [← sum_fin_succ_eq_sum_Icc N (fun k => c k * (((i.1 + 1) / k : ℕ) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **Discrete L² Quadratic Form Identity**: `harmonicCellL2PartialSum c N M = r_Mᵀ W_M r_M`. -/
theorem harmonicCellL2PartialSum_eq_quadForm (c : ℕ → ℝ) (M N : ℕ) :
    harmonicCellL2PartialSum c N M =
      dotProduct (residualVec c M N) ((slabWeightMatrix M).mulVec (residualVec c M N)) := by
  unfold harmonicCellL2PartialSum slabWeightMatrix
  simp only [Matrix.mulVec_diagonal, dotProduct, residualVec]
  rw [← sum_fin_succ_eq_sum_Icc M (fun n => (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n)]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Three-Matrix Sandwich Identity on `L²(1/(M+1), 1]`**: on `D1 c N = 0` (`1 ≤ M`),
the Lebesgue set integral equals `(1 + Σ D c)ᵀ W_M (1 + Σ D c) = r_Mᵀ W_M r_M`. -/
theorem setIntegral_Ioc_eq_matrix_quadForm (c : ℕ → ℝ) (N M : ℕ) (hM : 1 ≤ M)
    (hD1 : D1 c N = 0) :
    ∫ x in Set.Ioc (1 / ((M : ℝ) + 1)) 1, (continuousNymanResidual c N x) ^ 2 =
      dotProduct (residualVec c M N) ((slabWeightMatrix M).mulVec (residualVec c M N)) := by
  rw [harmonicCellL2PartialSum_eq_setIntegral_Ioc c N hM hD1,
    harmonicCellL2PartialSum_eq_quadForm]

/-- **Matrix Quadratic-Form Book X.1 Tail Bound**: on `D1 c N = 0`, for `1 ≤ M ≤ M'`,
increasing dimension from `M` to `M'` changes `rᵀ W r` by at most `B(c, N)² / (M + 1)`. -/
theorem matrix_quadForm_tail_bound (c : ℕ → ℝ) (N M M' : ℕ) (hD1 : D1 c N = 0)
    (hM : 1 ≤ M) (hMM' : M ≤ M') :
    dotProduct (residualVec c M' N) ((slabWeightMatrix M').mulVec (residualVec c M' N)) -
        dotProduct (residualVec c M N) ((slabWeightMatrix M).mulVec (residualVec c M N)) ≤
      (uniformCellBound c N) ^ 2 / ((M : ℝ) + 1) := by
  rw [← harmonicCellL2PartialSum_eq_quadForm, ← harmonicCellL2PartialSum_eq_quadForm,
    harmonicCellL2PartialSum_sub_eq_tailSum c N hM hMM']
  exact harmonicCellL2TailSum_le_uniformCellBound_sq_div_succ hD1 hM hMM'

/-! ## Part III: Half-Observation Laws (Spatial Upper-Half & Palindromic Period Folding) -/

/-- **Spatial Upper-Half Annihilation Law (`(1/2, 1]`)**: under Dirichlet anchoring
`IsDirichletAnchored c N` (`2 ≤ N`), the upper-half interval `(1/2, 1]` carries zero `L²` residual,
so the full `L²(0, 1]` energy concentrates strictly inside the lower half `(0, 1/2]`. -/
theorem upperHalf_observation_zero {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) :
    (∫ x in Set.Ioc (1 / 2 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 = 0) ∧
      (∫ x in Set.Ioc (0 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 =
        ∫ x in Set.Ioc (0 : ℝ) (1 / 2 : ℝ), (continuousNymanResidual c N x) ^ 2) := by
  have hcell : ∫ x in Set.Ioc (1 / 2 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 = 0 := by
    have h1 := setIntegral_Ioc_harmonicCell_eq c N le_rfl hc.1
    simp only [Nat.cast_one, div_one] at h1
    rw [discreteCellResidual_one_eq c (by omega : 1 ≤ N), hc.2.2] at h1
    norm_num at h1
    simpa [one_div] using h1
  have hf := continuousNymanResidual_sq_integrableOn_Ioc c N
  have hunion : Set.Ioc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) (1 / 2) ∪ Set.Ioc (1 / 2) 1 := by
    ext x; simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ⟨h0, h1⟩
      by_cases hx : x ≤ 1 / 2
      · exact Or.inl ⟨h0, hx⟩
      · exact Or.inr ⟨lt_of_not_ge hx, h1⟩
    · intro h
      rcases h with ⟨h0, hx⟩ | ⟨hx, h1⟩
      · exact ⟨h0, hx.trans (by norm_num)⟩
      · exact ⟨lt_trans (by norm_num) hx, h1⟩
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (1 / 2)) (Set.Ioc (1 / 2) 1) :=
    Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
  have hsub1 : Set.Ioc (0 : ℝ) (1 / 2) ⊆ Set.Ioc (0 : ℝ) 1 :=
    Set.Ioc_subset_Ioc le_rfl (by norm_num)
  have hsub2 : Set.Ioc (1 / 2 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 1 :=
    Set.Ioc_subset_Ioc (by norm_num) le_rfl
  refine ⟨hcell, ?_⟩
  rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
    (hf.mono_set hsub1) (hf.mono_set hsub2), hcell, add_zero]

/-- Anti-diagonal reversal permutation matrix `J` (`H × H`): `J i j = 1` iff `i + j + 1 = H`. -/
def revPermMatrix (H : ℕ) : Matrix (Fin H) (Fin H) ℝ :=
  fun i j => if i.1 + j.1 + 1 = H then 1 else 0

/-- Symmetry of the reversal involution: `Jᵀ = J`. -/
theorem revPermMatrix_transpose (H : ℕ) : (revPermMatrix H).transpose = revPermMatrix H := by
  ext i j
  simp only [Matrix.transpose_apply, revPermMatrix]
  rw [add_comm i.1 j.1]

/-- Involution identity of reversal: `J * J = I`. -/
theorem revPermMatrix_mul_self (H : ℕ) : revPermMatrix H * revPermMatrix H = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  set k : Fin H := ⟨H - 1 - i.1, by omega⟩
  have hterm : ∀ m : Fin H, revPermMatrix H i m * revPermMatrix H m j =
      if m = k then (if i = j then 1 else 0) else 0 := fun m => by
    dsimp [revPermMatrix]
    by_cases hmk : m = k
    · subst hmk
      have hik : i.1 + k.1 + 1 = H := by dsimp [k]; omega
      have hki : k.1 + i.1 + 1 = H := by omega
      by_cases hij : i = j
      · subst hij; simp [hik, hki]
      · have hne : k.1 + j.1 + 1 ≠ H := by
          intro heq
          apply hij; apply Fin.ext
          dsimp [k] at heq; omega
        simp [hik, hij, hne]
    · have hne : i.1 + m.1 + 1 ≠ H := fun heq =>
        hmk (Fin.ext (by dsimp [k]; omega))
      simp [hne, hmk]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq']
  simp [Matrix.one_apply]

/-- **Abstract Half-Observation Folding Theorem**: whenever `a_R = -J *ᵥ a_L` with `Jᵀ = J`,
the full two-half energy reduces identically to double the half-dimensional quadratic form under
the folded kernel `W̄_half = (1/2) • (W_L + J W_R J)`. -/
theorem halfObservation_quadForm_eq_double_half (H : ℕ)
    (WL WR : Matrix (Fin H) (Fin H) ℝ) (aL aR : Fin H → ℝ)
    (hanti : aR = -((revPermMatrix H).mulVec aL)) :
    dotProduct aL (WL.mulVec aL) + dotProduct aR (WR.mulVec aR) =
      2 * dotProduct aL
        ((((1 / 2 : ℝ) • (WL + revPermMatrix H * WR * revPermMatrix H))).mulVec aL) := by
  set J := revPermMatrix H
  have hsym : ∀ x y : Fin H → ℝ,
      dotProduct (J.mulVec x) y = dotProduct x (J.mulVec y) := fun x y => by
    calc dotProduct (J.mulVec x) y
        = dotProduct (Matrix.vecMul x J.transpose) y := by rw [Matrix.vecMul_transpose]
      _ = dotProduct (Matrix.vecMul x J) y := by rw [revPermMatrix_transpose]
      _ = dotProduct x (J.mulVec y) := (Matrix.dotProduct_mulVec x J y).symm
  have hR_quad : dotProduct aR (WR.mulVec aR) =
      dotProduct aL ((J * WR * J).mulVec aL) := by
    rw [hanti]
    simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
    rw [hsym aL (WR.mulVec (J.mulVec aL)), Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hR_quad]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul]
  ring

/-- Left half modular residual vector on `[1, H]` for period `L = 2 * H + 2`. -/
noncomputable def leftHalfResidual (c : ℕ → ℝ) (N H : ℕ) : Fin H → ℝ :=
  fun i => modularCellResidual c N (i.1 + 1)

/-- Right half modular residual vector on `[H + 1, 2 * H]` for period `L = 2 * H + 2`. -/
noncomputable def rightHalfResidual (c : ℕ → ℝ) (N H : ℕ) : Fin H → ℝ :=
  fun i => modularCellResidual c N (H + 1 + i.1)

/-- Diagonal harmonic slab weights on the left half `[1, H]`. -/
noncomputable def leftHalfWeights (H : ℕ) : Matrix (Fin H) (Fin H) ℝ :=
  Matrix.diagonal fun i => harmonicCellWidth (i.1 + 1)

/-- Diagonal harmonic slab weights on the right half `[H + 1, 2 * H]`. -/
noncomputable def rightHalfWeights (H : ℕ) : Matrix (Fin H) (Fin H) ℝ :=
  Matrix.diagonal fun i => harmonicCellWidth (H + 1 + i.1)

/-- Symmetric half-folded double-cone diagonal matrix `W̄_half = diag(doubleConeSymmetricWidth)`. -/
noncomputable def doubleConeHalfWeights (H : ℕ) : Matrix (Fin H) (Fin H) ℝ :=
  Matrix.diagonal fun i => doubleConeSymmetricWidth (2 * H + 2) (i.1 + 1)

/-- **Palindromic Half-Period Antisymmetry**: `a_R = -J *ᵥ a_L` on `[1, 2H]` for `L = 2H + 2`. -/
theorem rightHalfResidual_eq_neg_rev_mulVec (c : ℕ → ℝ) (N H : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ 2 * H + 2) :
    rightHalfResidual c N H = -((revPermMatrix H).mulVec (leftHalfResidual c N H)) := by
  ext i
  simp only [Pi.neg_apply, rightHalfResidual, Matrix.mulVec, dotProduct]
  set k : Fin H := ⟨H - 1 - i.1, by omega⟩
  have hterm : ∀ j : Fin H, revPermMatrix H i j * leftHalfResidual c N H j =
      if j = k then modularCellResidual c N (k.1 + 1) else 0 := fun j => by
    dsimp [revPermMatrix, leftHalfResidual]
    by_cases hjk : j = k
    · subst hjk
      have hik : i.1 + k.1 + 1 = H := by dsimp [k]; omega
      simp [hik]
    · have hne : i.1 + j.1 + 1 ≠ H := fun heq => hjk (Fin.ext (by dsimp [k]; omega))
      simp [hne, hjk]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  have href : H + 1 + i.1 = (2 * H + 2) - 1 - (k.1 + 1) := by dsimp [k]; omega
  rw [href, modularCellResidual_palindromic_neg c N (2 * H + 2) (k.1 + 1) hD1 hD0 hL (by omega)]

/-- **Folded Half-Weight Identity**: `(1/2) • (W_L + J * W_R * J) = doubleConeHalfWeights H`. -/
theorem foldedHalfWeights_eq_doubleCone (H : ℕ) :
    (1 / 2 : ℝ) • (leftHalfWeights H + revPermMatrix H * rightHalfWeights H * revPermMatrix H) =
      doubleConeHalfWeights H := by
  have hconj : revPermMatrix H * rightHalfWeights H * revPermMatrix H =
      Matrix.diagonal fun i => harmonicCellWidth (2 * H + 2 - 1 - (i.1 + 1)) := by
    ext i j
    rw [Matrix.mul_apply]
    set k : Fin H := ⟨H - 1 - i.1, by omega⟩
    have hrow : ∀ m : Fin H, (revPermMatrix H * rightHalfWeights H) i m =
        if m = k then harmonicCellWidth (H + 1 + k.1) else 0 := fun m => by
      rw [Matrix.mul_apply]
      have hinner : ∀ r : Fin H, revPermMatrix H i r * rightHalfWeights H r m =
          if r = m then (if r = k then harmonicCellWidth (H + 1 + k.1) else 0) else 0 := fun r => by
        dsimp [revPermMatrix, rightHalfWeights, Matrix.diagonal]
        by_cases hrm : r = m
        · subst hrm
          by_cases hrk : r = k
          · subst hrk
            have hik : i.1 + k.1 + 1 = H := by dsimp [k]; omega
            simp [hik]
          · have hne : i.1 + r.1 + 1 ≠ H := fun heq => hrk (Fin.ext (by dsimp [k]; omega))
            simp [hne, hrk]
        · simp [hrm]
      rw [Finset.sum_congr rfl fun r _ => hinner r, Finset.sum_ite_eq']
      by_cases hmk : m = k
      · subst hmk; simp
      · have hne : ¬ k = m := fun h => hmk h.symm
        simp [hmk]
    have hterm : ∀ m : Fin H, (revPermMatrix H * rightHalfWeights H) i m * revPermMatrix H m j =
        if m = k then (if i = j then harmonicCellWidth (2 * H + 2 - 1 - (i.1 + 1)) else 0)
          else 0 := fun m => by
      rw [hrow m]
      by_cases hmk : m = k
      · subst hmk
        dsimp [revPermMatrix]
        have hidx : H + 1 + k.1 = 2 * H + 2 - 1 - (i.1 + 1) := by dsimp [k]; omega
        by_cases hij : i = j
        · subst hij
          have hki : k.1 + i.1 + 1 = H := by dsimp [k]; omega
          simp [hki, hidx]
        · have hne : k.1 + j.1 + 1 ≠ H := fun heq => hij (Fin.ext (by dsimp [k] at heq; omega))
          simp [hne, hij]
      · simp [hmk]
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply_eq]
    · simp [hij, Matrix.diagonal_apply_ne]
  rw [hconj]
  ext i j
  dsimp [leftHalfWeights, doubleConeHalfWeights, doubleConeSymmetricWidth, Matrix.diagonal]
  by_cases hij : i = j
  · subst hij; simp [two_mul]; ring
  · simp [hij]

/-- **Concrete Period Half-Observation Folding Theorem**: for any period `L = 2 * H + 2` divisible
by `1..N`, the interior energy across `[1, L - 2]` equals twice the half-observation quadratic form
on `[1, H]` with symmetric double-cone weights. -/
theorem harmonicCellL2PartialSum_period_eq_double_halfObservation (c : ℕ → ℝ) (N H : ℕ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ 2 * H + 2) :
    harmonicCellL2PartialSum c N (2 * H) =
      2 * dotProduct (leftHalfResidual c N H)
        ((doubleConeHalfWeights H).mulVec (leftHalfResidual c N H)) := by
  have hsplit_sum : harmonicCellL2PartialSum c N (2 * H) =
      dotProduct (leftHalfResidual c N H) ((leftHalfWeights H).mulVec (leftHalfResidual c N H)) +
        dotProduct (rightHalfResidual c N H)
          ((rightHalfWeights H).mulVec (rightHalfResidual c N H)) := by
    unfold harmonicCellL2PartialSum
    have hmod : ∀ n ∈ Finset.Icc 1 (2 * H),
        (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n =
          (modularCellResidual c N n) ^ 2 * harmonicCellWidth n := fun n _ => by
      rw [discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N n hD1]
    rw [Finset.sum_congr rfl hmod]
    have hunion : Finset.Icc 1 (2 * H) = Finset.Icc 1 H ∪ Finset.Icc (H + 1) (2 * H) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Icc (H + 1) (2 * H)) :=
      Finset.disjoint_left.mpr fun n h1 h2 => by simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj]
    congr 1
    · simp only [leftHalfWeights, Matrix.mulVec_diagonal, dotProduct, leftHalfResidual]
      rw [← sum_fin_succ_eq_sum_Icc H
        (fun n => (modularCellResidual c N n) ^ 2 * harmonicCellWidth n)]
      refine Finset.sum_congr rfl fun i _ => by ring
    · simp only [rightHalfWeights, Matrix.mulVec_diagonal, dotProduct, rightHalfResidual]
      symm
      refine Finset.sum_bij (fun i _ => H + 1 + i.1) ?_ ?_ ?_ (fun i _ => by ring)
      · intro i _; exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
      · intro i₁ _ i₂ _ h; exact Fin.ext (by omega)
      · intro n hn
        have hn' := Finset.mem_Icc.mp hn
        refine ⟨⟨n - (H + 1), by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp; omega
  rw [hsplit_sum,
    halfObservation_quadForm_eq_double_half H (leftHalfWeights H) (rightHalfWeights H)
      (leftHalfResidual c N H) (rightHalfResidual c N H)
      (rightHalfResidual_eq_neg_rev_mulVec c N H hD1 hD0 hL),
    foldedHalfWeights_eq_doubleCone H]

/-! ## Part IV: Core `(N - 2) × (N - 2)` Matrices & Right Half-Plane Criterion -/

/-- The `(N - 2) × (N - 2)` cumulative-dipole Gram matrix `G̃_N`. -/
noncomputable def dipoleGramMatrix (N : ℕ) : Matrix (Fin (N - 2)) (Fin (N - 2)) ℝ :=
  fun i j => dipoleGramEntry (i.1 + 1) (j.1 + 1)

/-- The `(N - 2) × (N - 2)` pure 4-point plaque matrix `P_N`. -/
noncomputable def purePlaqueMatrix (N : ℕ) : Matrix (Fin (N - 2)) (Fin (N - 2)) ℝ :=
  fun i j => dipolePlaqueEntry (i.1 + 1) (j.1 + 1)

/-- The `(N - 2) × (N - 2)` homogeneous Dirichlet-simplex unit-defect matrix `M_N`. -/
noncomputable def unitDefectMatrix (N : ℕ) : Matrix (Fin (N - 2)) (Fin (N - 2)) ℝ :=
  fun i j => unitDefectEntry (i.1 + 1) (j.1 + 1)

/-- Boundary cotangent drive-difference vector `u_N(i) = δ(i + 3) - δ(i + 2)`. -/
noncomputable def driveDiffVec (N : ℕ) : Fin (N - 2) → ℝ :=
  fun i => deltaCot (i.1 + 3) - deltaCot (i.1 + 2)

/-- Outer product rank-1 matrix `(u ⊗ v)_{ij} = u_i * v_j`. -/
def rankOneMatrix {n : ℕ} (u v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * v j

/-- Symmetry of `dipoleGramMatrix N`. -/
theorem dipoleGramMatrix_isSymm (N : ℕ) : (dipoleGramMatrix N).IsSymm := by
  ext i j; exact dipoleGramEntry_comm (j.1 + 1) (i.1 + 1)

/-- Symmetry of `purePlaqueMatrix N`. -/
theorem purePlaqueMatrix_isSymm (N : ℕ) : (purePlaqueMatrix N).IsSymm := by
  ext i j; exact dipolePlaqueEntry_comm (j.1 + 1) (i.1 + 1)

/-- Symmetry of `unitDefectMatrix N`. -/
theorem unitDefectMatrix_isSymm (N : ℕ) : (unitDefectMatrix N).IsSymm := by
  ext i j; exact unitDefectEntry_comm (j.1 + 1) (i.1 + 1)

/-- **Universal Superdiagonal Orthogonality in Matrix Form**: `(G̃_N)_{i, i+1} = 0` for all `i`. -/
theorem dipoleGramMatrix_superdiag_eq_zero (N : ℕ) (i j : Fin (N - 2)) (h : j.1 = i.1 + 1) :
    dipoleGramMatrix N i j = 0 := by
  dsimp [dipoleGramMatrix]
  rw [h, show i.1 + 1 + 1 = (i.1 + 1) + 1 by omega]
  exact (dipoleGramEntry_self_succ_eq_zero (i.1 + 1)).1

/-- **Rank-2 Shift Identity (`G̃_N` vs. `P_N`)**:
`G̃_N = P_N + (π / 2) * (u 1ᵀ + 1 uᵀ)`. -/
theorem dipoleGramMatrix_eq_purePlaque_add_boundary (N : ℕ) :
    dipoleGramMatrix N =
      purePlaqueMatrix N +
        (Real.pi / 2) •
          (rankOneMatrix (driveDiffVec N) (onesVec (N - 2)) +
            rankOneMatrix (onesVec (N - 2)) (driveDiffVec N)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    dipoleGramMatrix, purePlaqueMatrix, rankOneMatrix, driveDiffVec, onesVec,
    dipoleGramEntry_eq_boundary_add_plaque]
  rw [show i.1 + 1 + 2 = i.1 + 3 by omega, show i.1 + 1 + 1 = i.1 + 2 by omega,
    show j.1 + 1 + 2 = j.1 + 3 by omega, show j.1 + 1 + 1 = j.1 + 2 by omega]
  ring

/-- **Homogeneous Unit-Defect Matrix Identity (`M_N` vs. `P_N`)**:
`M_N = 1 1ᵀ - (π / 2) * (u 1ᵀ + 1 uᵀ) + P_N`. -/
theorem unitDefectMatrix_eq_rankOne_sub_boundary_add_plaque (N : ℕ) :
    unitDefectMatrix N =
      rankOneMatrix (onesVec (N - 2)) (onesVec (N - 2)) -
        (Real.pi / 2) •
          (rankOneMatrix (driveDiffVec N) (onesVec (N - 2)) +
            rankOneMatrix (onesVec (N - 2)) (driveDiffVec N)) +
        purePlaqueMatrix N := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    unitDefectMatrix, purePlaqueMatrix, rankOneMatrix, driveDiffVec, onesVec, unitDefectEntry]
  rw [show i.1 + 1 + 2 = i.1 + 3 by omega, show i.1 + 1 + 1 = i.1 + 2 by omega,
    show j.1 + 1 + 2 = j.1 + 3 by omega, show j.1 + 1 + 1 = j.1 + 2 by omega]
  ring

/-- **Homogeneous Unit-Defect Matrix Identity (`M_N` vs. `G̃_N`)**:
`M_N = 1 1ᵀ - π * (u 1ᵀ + 1 uᵀ) + G̃_N`. -/
theorem unitDefectMatrix_eq_rankOne_sub_two_boundary_add_gram (N : ℕ) :
    unitDefectMatrix N =
      rankOneMatrix (onesVec (N - 2)) (onesVec (N - 2)) -
        Real.pi •
          (rankOneMatrix (driveDiffVec N) (onesVec (N - 2)) +
            rankOneMatrix (onesVec (N - 2)) (driveDiffVec N)) +
        dipoleGramMatrix N := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    unitDefectMatrix, dipoleGramMatrix, rankOneMatrix, driveDiffVec, onesVec,
    unitDefectEntry_eq_one_sub_drive_add_gram]
  rw [show i.1 + 1 + 2 = i.1 + 3 by omega, show i.1 + 1 + 1 = i.1 + 2 by omega,
    show j.1 + 1 + 2 = j.1 + 3 by omega, show j.1 + 1 + 1 = j.1 + 2 by omega]
  ring

/-- Dipole-coordinate vector `α_N ∈ ℝ^{N - 2}` extracted from `c`. -/
noncomputable def dipoleCoordVec (c : ℕ → ℝ) (N : ℕ) : Fin (N - 2) → ℝ :=
  fun i => dipoleCoord c N (i.1 + 1)

/-- **Dirichlet Simplex Constraint in Vector Form**: `1ᵀ α_N = 1` on `IsDirichletAnchored c N`. -/
theorem dotProduct_ones_dipoleCoordVec_eq_one {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    dotProduct (onesVec (N - 2)) (dipoleCoordVec c N) = 1 := by
  rw [← sum_dipoleCoord_eq_one_of_isDirichletAnchored hN hc]
  simp only [dotProduct, onesVec, dipoleCoordVec, one_mul]
  exact sum_fin_succ_eq_sum_Icc (N - 2) (dipoleCoord c N)

private lemma quadForm_unitDefectMatrix_eq_double_sum {N : ℕ} (α : Fin (N - 2) → ℝ)
    (α' : ℕ → ℝ) (hα : ∀ i : Fin (N - 2), α' (i.1 + 1) = α i) :
    dotProduct α ((unitDefectMatrix N).mulVec α) =
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        α' a * α' b * unitDefectEntry a b := by
  simp only [dotProduct, Matrix.mulVec, unitDefectMatrix, Finset.mul_sum]
  rw [← sum_fin_succ_eq_sum_Icc (N - 2) fun a =>
    ∑ b ∈ Finset.Icc 1 (N - 2), α' a * α' b * unitDefectEntry a b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_fin_succ_eq_sum_Icc (N - 2) fun b =>
    α' (i.1 + 1) * α' b * unitDefectEntry (i.1 + 1) b]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hα i, hα j]
  ring

/-- **Matrix Defect Reduction**: on `IsDirichletAnchored c N`, `1 - SCot c N = αᵀ M_N α`. -/
theorem one_sub_SCot_eq_unitDefectMatrix_quadForm {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    1 - SCot vasyuninGCot c N =
      dotProduct (dipoleCoordVec c N) ((unitDefectMatrix N).mulVec (dipoleCoordVec c N)) := by
  rw [one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored hN hc,
    quadForm_unitDefectMatrix_eq_double_sum (dipoleCoordVec c N) (dipoleCoord c N) fun _ => rfl]

private lemma exists_dirichletAnchored_of_simplex {N : ℕ} (hN : 2 ≤ N) (α : Fin (N - 2) → ℝ)
    (hα : dotProduct (onesVec (N - 2)) α = 1) :
    ∃ c : ℕ → ℝ, IsDirichletAnchored c N ∧ dipoleCoordVec c N = α := by
  let α' : ℕ → ℝ := fun m =>
    if hm : 1 ≤ m ∧ m ≤ N - 2 then α ⟨m - 1, by omega⟩ else 0
  have hα' : ∑ m ∈ Finset.Icc 1 (N - 2), α' m = 1 := by
    rw [← hα]
    simp only [dotProduct, onesVec, one_mul]
    rw [← sum_fin_succ_eq_sum_Icc (N - 2) α']
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [α']
    have hi : 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ N - 2 := ⟨by omega, i.isLt⟩
    simp [hi]
  let c : ℕ → ℝ := fun k =>
    cBaseAnchor k + ∑ m ∈ Finset.Icc 1 (N - 2), α' m * cumulativeDipole m k
  have hbase := cBaseAnchor_mem_A_N hN
  have hs_m : ∀ m ∈ Finset.Icc 1 (N - 2), 1 ≤ m ∧ m + 2 ≤ N := fun m hm =>
    ⟨(Finset.mem_Icc.mp hm).1, by have := (Finset.mem_Icc.mp hm).2; omega⟩
  have hcD1 : D1 c N = 0 := by
    unfold D1 at hbase ⊢
    simp_rw [c, add_div, Finset.sum_add_distrib, hbase.1, zero_add, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hd := (cumulativeDipole_mem_tangent (hs_m m hm).1 (hs_m m hm).2).1
    unfold D1 at hd
    simp_rw [mul_div_assoc, ← Finset.mul_sum, hd, mul_zero]
  have hcD0 : D0 c N = 2 := by
    unfold D0 at hbase ⊢
    simp_rw [c, Finset.sum_add_distrib, hbase.2, add_eq_left]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hd := (cumulativeDipole_mem_tangent (hs_m m hm).1 (hs_m m hm).2).2
    unfold D0 at hd
    rw [← Finset.mul_sum, hd, mul_zero]
  have hcum1 : ∀ m ∈ Finset.Icc 1 (N - 2), cumulativeDipole m 1 = 1 := fun m hm => by
    unfold cumulativeDipole
    rw [Finset.sum_eq_single 1]
    · simp [harmonicWavelet]
    · intro r hr hne
      rcases r with _ | _ | r <;> [exact absurd (Finset.mem_Icc.mp hr).1 (by decide);
        exact absurd rfl hne; simp [harmonicWavelet]]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, (Finset.mem_Icc.mp hm).1⟩) h
  have hc1 : c 1 = -1 := by
    have h1 : ∑ m ∈ Finset.Icc 1 (N - 2), α' m * cumulativeDipole m 1 = 1 := by
      rw [Finset.sum_congr rfl fun m hm => by rw [hcum1 m hm, mul_one], hα']
    dsimp [c, cBaseAnchor]; rw [h1]; norm_num
  have hcoord : ∀ a ∈ Finset.Icc 1 (N - 2), dipoleCoord c N a = α' a := fun a ha => by
    rw [← dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp ha).1 (N := N) (c := c),
      show (fun k => c k - cBaseAnchor k) = fun k =>
        ∑ m ∈ Finset.Icc 1 (N - 2), α' m * cumulativeDipole m k by ext k; dsimp [c]; ring]
    unfold dipoleCoord; simp_rw [Finset.sum_div]; rw [Finset.sum_comm]
    have ht : ∀ m ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc (a + 2) N,
        α' m * cumulativeDipole m j / (j : ℝ) = if m = a then α' a else 0 := fun m hm => by
      let F : ℕ → ℝ := fun k => if a + 2 ≤ k then 1 else 0
      have hs := cumulativeDipole_div_sum_eq_four_point F (hs_m m hm).1 (hs_m m hm).2
      rw [Finset.sum_congr rfl fun k _ => show cumulativeDipole m k * (F k / (k : ℝ)) =
        if a + 2 ≤ k then cumulativeDipole m k / (k : ℝ) else 0 from by
          dsimp [F]; split_ifs <;> ring] at hs
      simp_rw [mul_div_assoc, ← Finset.mul_sum]
      rw [show Finset.Icc (a + 2) N = (Finset.Icc 1 N).filter (fun k => a + 2 ≤ k) by
        ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega, Finset.sum_filter, hs]
      have ha1 := (Finset.mem_Icc.mp ha).1
      by_cases hma : m = a <;> (dsimp [F]; split_ifs <;> norm_num <;> try omega)
      subst hma; simp
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']; simp [ha]
  refine ⟨c, ⟨hcD1, hcD0, hc1⟩, ?_⟩
  ext i
  have hi : i.1 + 1 ∈ Finset.Icc 1 (N - 2) := Finset.mem_Icc.mpr ⟨by omega, i.isLt⟩
  rw [dipoleCoordVec, hcoord (i.1 + 1) hi]
  dsimp [α']
  have hi' : 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ N - 2 := ⟨by omega, i.isLt⟩
  simp [hi']

/-- **Matrix Positive Semi-Definiteness on the Simplex**: for any `N ≥ 2` and `1ᵀ α = 1`,
`0 ≤ αᵀ M_N α`. -/
theorem unitDefectMatrix_quadForm_nonneg_of_simplex {N : ℕ} (hN : 2 ≤ N)
    (α : Fin (N - 2) → ℝ) (hα : dotProduct (onesVec (N - 2)) α = 1) :
    0 ≤ dotProduct α ((unitDefectMatrix N).mulVec α) := by
  obtain ⟨c, hc, hvec⟩ := exists_dirichletAnchored_of_simplex hN α hα
  rw [← hvec, ← one_sub_SCot_eq_unitDefectMatrix_quadForm hN hc,
    ← affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1]
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

/-- **Right Half-Plane Observational Limit (`Re(s) > 1/2`) Floor — Unconditional**:
Any nontrivial off-line zero `riemannZeta s = 0` in the right half-plane `1/2 < Re(s) < 1` forces
every simplex vector `1ᵀ α = 1` at every truncation `N ≥ 2` to satisfy the uniform lower floor
`(2 * Re(s) - 1) / ‖s‖² ≤ αᵀ M_N α`. -/
theorem unitDefectMatrix_offline_zero_floor_unconditional {N : ℕ} (hN : 2 ≤ N)
    (α : Fin (N - 2) → ℝ) (hα : dotProduct (onesVec (N - 2)) α = 1)
    {s : ℂ} (hs_lo : 1 / 2 < s.re) (hs_hi : s.re < 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ dotProduct α ((unitDefectMatrix N).mulVec α) := by
  obtain ⟨c, hc, hvec⟩ := exists_dirichletAnchored_of_simplex hN α hα
  have hfloor := mellin_l2_floor_of_zeta_zero_unconditional c N hc.1 hs_lo hs_hi hz
  rwa [affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1,
    one_sub_SCot_eq_unitDefectMatrix_quadForm hN hc, hvec] at hfloor

/-- **Unconditional Matrix-Simplex RH Equivalence Criterion**:
`_root_.RiemannHypothesis` follows if `inf { αᵀ M_N α | 1ᵀ α = 1 } → 0` as `N → ∞`,
with `TitchmarshMellinProperty` discharged unconditionally via `UnconditionalTitchmarshBridge`. -/
theorem riemannHypothesis_of_unitDefectMatrix_vanishing_unconditional
    (h_vanish : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (α : Fin (N - 2) → ℝ),
      2 ≤ N ∧ dotProduct (onesVec (N - 2)) α = 1 ∧
        dotProduct α ((unitDefectMatrix N).mulVec α) < ε) :
    _root_.RiemannHypothesis := by
  refine riemannHypothesis_of_unitDefectEntry_simplex_vanishing
    titchmarshMellinProperty_unconditional fun ε hε => ?_
  obtain ⟨N, α, hN, hα, hlt⟩ := h_vanish ε hε
  let α' : ℕ → ℝ := fun m =>
    if hm : 1 ≤ m ∧ m ≤ N - 2 then α ⟨m - 1, by omega⟩ else 0
  have hα' : ∑ m ∈ Finset.Icc 1 (N - 2), α' m = 1 := by
    rw [← hα]
    simp only [dotProduct, onesVec, one_mul]
    rw [← sum_fin_succ_eq_sum_Icc (N - 2) α']
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [α']
    have hi : 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ N - 2 := ⟨by omega, i.isLt⟩
    simp [hi]
  have hsum_eq : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      α' a * α' b * unitDefectEntry a b =
      dotProduct α ((unitDefectMatrix N).mulVec α) := by
    rw [quadForm_unitDefectMatrix_eq_double_sum α α' fun i => by
      dsimp [α']
      have hi : 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ N - 2 := ⟨by omega, i.isLt⟩
      simp [hi]]
  exact ⟨N, α', hN, hα', hsum_eq ▸ hlt⟩

end RiemannBlueprint.MatrixHalfObservation
