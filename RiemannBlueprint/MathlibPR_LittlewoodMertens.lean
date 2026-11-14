/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Littlewood's (1912) and von Koch's (1901) Forward Theorems for the Riemann Hypothesis

This file formalizes both forward implications in Mathlib style:
1. **Littlewood (1912):** if `M(x) = ∑ n ≤ ⌊x⌋₊, μ(n)` satisfies `M(x) = O(x ^ (1 / 2 + ε))` as
   `x → ∞` for every `ε > 0`, then `riemannZeta s ≠ 0` for `1 / 2 < s.re`, and `RiemannHypothesis`.
2. **von Koch (1901):** if `ψ(x) = ∑ n ≤ ⌊x⌋₊, Λ(n)` satisfies `ψ(x) - x = O(x ^ (1 / 2 + ε))`
   as `x → ∞` for every `ε > 0`, then `riemannZeta s ≠ 0` for `1 / 2 < s.re`, and `RiemannHypothesis`.

## Main results

* `mertens` : the Mertens summatory function `∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.moebius n`.
* `riemannZeta_zero_reflection` : non-trivial zeros of `riemannZeta` reflect across `s.re = 1 / 2`.
* `chiFactor` and `chi_critical_line_modulus` : unitary modulus `‖χ(1 / 2 + I * t)‖ = 1` on the
  critical line.
* `mertens_inversion_of_bound` : existence of an explicit right inverse of `riemannZeta` on
  `{s : ℂ | 1 / 2 < s.re}` assuming `M(x) = O(x ^ (1 / 2 + ε))` for all `ε > 0`.
* `RiemannHypothesis.of_mertens_isBigO` : Littlewood's (1912) forward theorem.
* `chebyshevPsi` and `mellinVonKochRemainder` : Chebyshev's `ψ(x)` and its Mellin remainder `J_ψ(s)`.
* `mellinVonKochRemainder_analyticOnNhd` : analytic continuation of `J_ψ(s)` to `1 / 2 < s.re`.
* `zeta_deriv_cleared_eq_zero_of_half_lt_re_ne_one` : `ζ'(s) + (s / (s - 1) + J_ψ(s)) * ζ(s) = 0`.
* `zero_free_re_gt_half_of_vonKoch` : zero-free half-plane `1 / 2 < s.re` under von Koch's bound.
* `RiemannHypothesis.of_chebyshevPsi_sub_self_isBigO` : von Koch's (1901) forward theorem.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius LSeries.notation Topology
open Asymptotics Complex Filter MeasureTheory Set

/-- The Mertens summatory function `M(x) = ∑_{n ≤ x} μ(n)`. -/
noncomputable def mertens (x : ℝ) : ℤ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.moebius n

/-- Mellin-Mertens integral `s * ∫_{t > 1} M(t) * t^{-(s+1)} dt`, representing `1 / ζ(s)`. -/
noncomputable def mellinMertens (s : ℂ) : ℂ :=
  s * ∫ x in Set.Ioi (1 : ℝ), (mertens x : ℂ) * (x : ℂ) ^ (-(s + 1))

private noncomputable def moebiusC : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)

private noncomputable def mertensIndicator (x : ℝ) : ℂ :=
  if 1 < x then (mertens x : ℂ) else 0

private noncomputable def mellinMertensInv (s : ℂ) : ℂ :=
  if s = 1 then (riemannZeta 1)⁻¹ else mellinMertens s

private lemma mertens_cast_eq_sum_Icc (x : ℝ) :
    (mertens x : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, moebiusC k := by
  dsimp [mertens, moebiusC]
  push_cast
  have hIic : Finset.Iic ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hIic, Finset.sum_insert (by simp)]
  simp

private lemma moebiusC_sum_norm_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have h_le : ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖ ≤ (n : ℝ) := by
    calc ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          simpa [moebiusC, Complex.norm_intCast] using
            (show |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k))
      _ = (Finset.Icc 1 n).card := by simp
      _ ≤ n := by
          norm_cast
          simp [Nat.card_Icc]
  have h_nn : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  simpa [Real.norm_of_nonneg h_nn, Real.rpow_one, Real.norm_natCast] using h_le

/-- On `1 < s.re`, Abel summation identifies `LSeries ↗μ s = mellinMertens s`, giving
`riemannZeta s * mellinMertens s = 1`. -/
theorem riemannZeta_mul_mellinMertens_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mellinMertens s = 1 := by
  have h_int : LSeries moebiusC s = mellinMertens s := by
    rw [LSeries_eq_mul_integral' moebiusC zero_le_one hs moebiusC_sum_norm_isBigO]
    dsimp [mellinMertens]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mertens_cast_eq_sum_Icc]
  have h_mul : riemannZeta s * LSeries moebiusC s = 1 := by
    have hz : LSeries (1 : ℕ → ℂ) s = riemannZeta s := LSeries_one_eq_riemannZeta hs
    have hmul : LSeries (1 : ℕ → ℂ) s * LSeries (↗ArithmeticFunction.moebius) s = 1 :=
      LSeries_one_mul_Lseries_moebius hs
    rw [hz] at hmul
    have h_congr : LSeries (↗ArithmeticFunction.moebius) s = LSeries moebiusC s :=
      LSeries_congr (fun _ => by simp [moebiusC]) s
    rwa [h_congr] at hmul
  rwa [← h_int]

private lemma mellinMertens_eq_mul_mellin (s : ℂ) :
    mellinMertens s = s * mellin mertensIndicator (-s) := by
  dsimp [mellinMertens, mellin]
  congr 1
  have h_eq : EqOn
      ((Set.Ioi 1).indicator fun t : ℝ => (mertens t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) * mertensIndicator t)
      (Set.Ioi 0) := by
    intro t _ht
    by_cases ht1 : 1 < t
    · have h_exp : (-s - 1 : ℂ) = -(s + 1) := by ring
      simp [mertensIndicator, ht1, mul_comm, h_exp]
    · simp [mertensIndicator, ht1]
  rw [← setIntegral_congr_fun measurableSet_Ioi h_eq, setIntegral_indicator measurableSet_Ioi]
  have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioi 1 = Set.Ioi 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨zero_lt_one.trans h, h⟩⟩
  rw [h_inter]

private lemma locallyIntegrableOn_mertensIndicator :
    LocallyIntegrableOn mertensIndicator (Set.Ioi 0) := by
  have h_sum : LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, moebiusC k)
      (Set.Ici 0) := by
    simpa using locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (c := moebiusC) (m := 1)
      le_rfl (locallyIntegrableOn_const (1 : ℂ))
  have h_loc : LocallyIntegrableOn (fun t : ℝ => (mertens t : ℂ)) (Set.Ioi 0) := by
    have h_fn : (fun t : ℝ => (mertens t : ℂ)) =
        fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, moebiusC k :=
      funext mertens_cast_eq_sum_Icc
    rw [h_fn]
    exact h_sum.mono_set Set.Ioi_subset_Ici_self
  rw [locallyIntegrableOn_iff isLocallyClosed_Ioi]
  intro K hK_sub hK_cpt
  have hK_int : IntegrableOn (fun t : ℝ => (mertens t : ℂ)) K :=
    h_loc.integrableOn_compact_subset hK_sub hK_cpt
  have h_ind : IntegrableOn ((Set.Ioi 1).indicator (fun t : ℝ => (mertens t : ℂ))) K :=
    hK_int.indicator measurableSet_Ioi
  refine h_ind.congr_fun (fun t _ => ?_) hK_cpt.measurableSet
  by_cases ht : 1 < t <;> simp [mertensIndicator, ht]

private lemma mertensIndicator_isBigO_atTop {ε : ℝ}
    (hO : (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ ((1 / 2 : ℝ) + ε)) :
    mertensIndicator =O[atTop] fun x : ℝ => x ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC⟩ := hO.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with x hx
  by_cases hx1 : 1 < x
  · simpa [mertensIndicator, hx1, Complex.norm_intCast] using hx
  · simp only [mertensIndicator, hx1, ↓reduceIte, norm_zero]
    exact le_trans (norm_nonneg _) hx

private lemma mertensIndicator_isBigO_nhdsWithin_zero (b : ℝ) :
    mertensIndicator =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
  refine (isBigO_zero (fun x : ℝ => x ^ (-b)) (𝓝[>] 0)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds one_pos)] with x hx
  simp [mertensIndicator, not_lt.mpr (le_of_lt hx)]

/-- Under the `O(x ^ (1/2 + ε))` Mertens growth hypothesis, `mellinMertens` is
complex-differentiable at every point `s` with `1 / 2 < s.re`. -/
theorem mellinMertens_differentiableAt_of_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ mellinMertens s := by
  have h_fn : mellinMertens = fun z : ℂ => z * mellin mertensIndicator (-z) :=
    funext mellinMertens_eq_mul_mellin
  rw [h_fn]
  have hε : 0 < (s.re - 1 / 2) / 2 := by linarith
  set ε : ℝ := (s.re - 1 / 2) / 2
  set a : ℝ := -((1 / 2 : ℝ) + ε)
  set b : ℝ := (-s).re - 1
  have hf_top : mertensIndicator =O[atTop] (· ^ (-a)) := by
    simpa [a, neg_neg] using mertensIndicator_isBigO_atTop (hM ε hε)
  have hs_top : (-s).re < a := by
    rw [neg_re]
    dsimp [a, ε]
    linarith
  have hs_bot : b < (-s).re := by
    dsimp [b]
    linarith
  have hm_diff : DifferentiableAt ℂ (mellin mertensIndicator) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_mertensIndicator
      hf_top hs_top (mertensIndicator_isBigO_nhdsWithin_zero b) hs_bot
  have h_comp : DifferentiableAt ℂ (fun z : ℂ => mellin mertensIndicator (-z)) s :=
    hm_diff.comp s differentiableAt_id.neg
  exact differentiableAt_id.mul h_comp

private lemma isOpen_re_gt (r : ℝ) : IsOpen {s : ℂ | r < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma isOpen_im_gt (r : ℝ) : IsOpen {s : ℂ | r < s.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private lemma convex_combination_gt {r u v a b : ℝ} (hu : r < u) (hv : r < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : r < a * u + b * v := by
  by_cases ha0 : 0 < a
  · calc r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ < a * u + b * v := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hu ha0) (mul_le_mul_of_nonneg_left hv.le hb)
  · have ha0' : a = 0 := le_antisymm (not_lt.mp ha0) ha
    have hb1 : b = 1 := by linarith
    rw [ha0', hb1]
    linarith

private lemma convex_combination_lt {r u v a b : ℝ} (hu : u < r) (hv : v < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a * u + b * v < r := by
  have h := convex_combination_gt (neg_lt_neg hu) (neg_lt_neg hv) ha hb hab
  linarith

private lemma convex_re_gt (r : ℝ) : Convex ℝ {s : ℂ | r < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
  exact convex_combination_gt hx hy ha hb hab

private lemma convex_re_lt (r : ℝ) : Convex ℝ {s : ℂ | s.re < r} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
  exact convex_combination_lt hx hy ha hb hab

private lemma convex_im_gt (r : ℝ) : Convex ℝ {s : ℂ | r < s.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
  exact convex_combination_gt hx hy ha hb hab

private lemma convex_im_lt (r : ℝ) : Convex ℝ {s : ℂ | s.im < r} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
  exact convex_combination_lt hx hy ha hb hab

/-- Analytic continuation of `riemannZeta s * mellinMertens s = 1` to all `s` with
`1 / 2 < s.re` and `s ≠ 1`. -/
theorem riemannZeta_mul_mellinMertens_eq_one_of_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s * mellinMertens s = 1 := by
  let F : ℂ → ℂ := fun s => riemannZeta s * mellinMertens s
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re} \ {1}
  have hU_open : IsOpen U := (isOpen_re_gt (1 / 2)).sdiff isClosed_singleton
  have hF_diff : DifferentiableOn ℂ F U := fun s hs =>
    ((differentiableAt_riemannZeta hs.2).mul
      (mellinMertens_differentiableAt_of_isBigO hM hs.1)).differentiableWithinAt
  have hF_ana : AnalyticOnNhd ℂ F U := hF_diff.analyticOnNhd hU_open
  let U_top : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}
  let U_bot : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0}
  let U_strip : Set ℂ := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1}
  have hU_top_sub : U_top ⊆ U := by
    intro s hs
    refine ⟨hs.1, fun h1 => ?_⟩
    subst h1
    simp [U_top] at hs
  have hU_bot_sub : U_bot ⊆ U := by
    intro s hs
    refine ⟨hs.1, fun h1 => ?_⟩
    subst h1
    simp [U_bot] at hs
  have hU_strip_sub : U_strip ⊆ U := by
    intro s hs
    refine ⟨hs.1, fun h1 => ?_⟩
    subst h1
    simp [U_strip] at hs
  have hU_top_pre : IsPreconnected U_top :=
    ((convex_re_gt (1 / 2)).inter (convex_im_gt 0)).isPreconnected
  have hU_bot_pre : IsPreconnected U_bot :=
    ((convex_re_gt (1 / 2)).inter (convex_im_lt 0)).isPreconnected
  have hU_strip_pre : IsPreconnected U_strip :=
    ((convex_re_gt (1 / 2)).inter (convex_re_lt 1)).isPreconnected
  have h_one_ana : ∀ V : Set ℂ, AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) V :=
    fun _ => analyticOnNhd_const
  have h_eq_top : EqOn F (fun _ => (1 : ℂ)) U_top := by
    have hz0 : (2 : ℂ) + Complex.I ∈ U_top := by norm_num [U_top]
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) + Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : 1 < ((2 : ℂ) + Complex.I).re)]
        with z hz
      exact riemannZeta_mul_mellinMertens_of_one_lt_re hz
    exact (hF_ana.mono hU_top_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_top) hU_top_pre hz0 h_ev
  have h_eq_bot : EqOn F (fun _ => (1 : ℂ)) U_bot := by
    have hz0 : (2 : ℂ) - Complex.I ∈ U_bot := by norm_num [U_bot]
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) - Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : 1 < ((2 : ℂ) - Complex.I).re)]
        with z hz
      exact riemannZeta_mul_mellinMertens_of_one_lt_re hz
    exact (hF_ana.mono hU_bot_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_bot) hU_bot_pre hz0 h_ev
  have h_eq_strip : EqOn F (fun _ => (1 : ℂ)) U_strip := by
    have hz0 : ((3 / 4 : ℝ) : ℂ) + Complex.I ∈ U_strip := by norm_num [U_strip]
    have h_U_top_open : IsOpen U_top := (isOpen_re_gt (1 / 2)).inter (isOpen_im_gt 0)
    have h_ev : F =ᶠ[𝓝 (((3 / 4 : ℝ) : ℂ) + Complex.I)] (fun _ => (1 : ℂ)) := by
      filter_upwards [h_U_top_open.mem_nhds
          (by norm_num [U_top] : ((3 / 4 : ℝ) : ℂ) + Complex.I ∈ U_top)]
        with z hz
      exact h_eq_top hz
    exact (hF_ana.mono hU_strip_sub).eqOn_of_preconnected_of_eventuallyEq
      (h_one_ana U_strip) hU_strip_pre hz0 h_ev
  intro s hs hne
  rcases lt_trichotomy s.re 1 with hlt | heq | hgt
  · exact h_eq_strip ⟨hs, hlt⟩
  · have him : s.im ≠ 0 := by
      intro h0
      apply hne
      apply Complex.ext <;> simp [heq, h0]
    rcases lt_or_gt_of_ne him with him_lt | him_gt
    · exact h_eq_bot ⟨hs, him_lt⟩
    · exact h_eq_top ⟨hs, him_gt⟩
  · exact riemannZeta_mul_mellinMertens_of_one_lt_re hgt

/-- Under `M(x) = O(x ^ (1 / 2 + ε))` for all `ε > 0`, `mellinMertensInv` furnishes a right
inverse to `riemannZeta` across the open half-plane `{s : ℂ | 1 / 2 < s.re}`. -/
theorem mertens_inversion_of_bound
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    ∃ I_M : ℂ → ℂ, ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s * I_M s = 1 := by
  refine ⟨mellinMertensInv, fun s hs => ?_⟩
  by_cases h1 : s = 1
  · subst h1
    simp only [mellinMertensInv, ↓reduceIte]
    exact mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  · simp only [mellinMertensInv, h1, ↓reduceIte]
    exact riemannZeta_mul_mellinMertens_eq_one_of_isBigO hM s hs h1

/-- Reflection symmetry for non-trivial zeros of `riemannZeta` across the critical line
`Re(s) = 1 / 2`, proved directly from Mathlib's functional equation `riemannZeta_one_sub`. -/
theorem riemannZeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) (_hs_lt : s.re < 1 / 2) :
    riemannZeta (1 - s) = 0 ∧ 1 / 2 < (1 - s).re := by
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
          have h_cpow_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
            rw [Complex.cpow_ne_zero_iff]
            left
            exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
          have h_gamma_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_not_neg
          have h_cos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
            intro hcos
            rw [Complex.cos_eq_zero_iff] at hcos
            rcases hcos with ⟨k, hk⟩
            have hw2 :
                (Real.pi : ℂ) * w / 2 = ((((m + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by
              dsimp [w]; push_cast; ring
            have hk2 : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 =
                ((((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi : ℝ) : ℂ) := by
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
              Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 :=
            mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h_cpow_ne)
              h_gamma_ne) h_cos_ne) h_zeta_ne
          exact h_rhs_ne h_fe.symm
    rw [riemannZeta_one_sub h_not_neg_nat h_not_one, hz, mul_zero]
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/-- Explicit functional equation reflection factor
`χ(s) = 2 ^ s * π ^ (s - 1) * sin (π * s / 2) * Γ (1 - s)`. -/
noncomputable def chiFactor (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin ((Real.pi : ℂ) * s / 2) *
    Complex.Gamma (1 - s)

private lemma conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (z : ℂ) :
    starRingEnd ℂ ((r : ℂ) ^ z) = (r : ℂ) ^ (starRingEnd ℂ z) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  have hc := Complex.cpow_conj (r : ℂ) z harg
  rw [Complex.conj_ofReal] at hc
  exact hc.symm

/-- On the critical line `Re(s) = 1 / 2`, the reflection factor `χ(1 / 2 + i * t)` has
unitary modulus `‖χ(1 / 2 + i * t)‖ = 1`. -/
theorem chi_critical_line_modulus (t : ℝ) :
    ‖chiFactor (1 / 2 + Complex.I * t)‖ = 1 := by
  let s : ℂ := 1 / 2 + Complex.I * t
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs_conj : starRingEnd ℂ s = 1 - s := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have h_conj_chi : starRingEnd ℂ (chiFactor s) = chiFactor (1 - s) := by
    dsimp [chiFactor]
    simp only [map_mul]
    have h2 : starRingEnd ℂ ((2 : ℂ) ^ s) = (2 : ℂ) ^ (1 - s) := by
      have h := conj_ofReal_cpow (by norm_num : (0 : ℝ) < 2) s
      norm_cast at h
      rw [h, hs_conj]
    have hpi : starRingEnd ℂ ((Real.pi : ℂ) ^ (s - 1)) = (Real.pi : ℂ) ^ (1 - s - 1) := by
      have h := conj_ofReal_cpow Real.pi_pos (s - 1)
      rw [h, map_sub, map_one, hs_conj]
    have hsin : starRingEnd ℂ (Complex.sin ((Real.pi : ℂ) * s / 2)) =
        Complex.sin ((Real.pi : ℂ) * (1 - s) / 2) := by
      rw [← Complex.sin_conj, map_div₀, map_mul, Complex.conj_ofReal, map_ofNat, hs_conj]
    have hgam : starRingEnd ℂ (Complex.Gamma (1 - s)) = Complex.Gamma (1 - (1 - s)) := by
      rw [← Complex.Gamma_conj, map_sub, map_one, hs_conj]
    rw [h2, hpi, hsin, hgam]
  have h_prod : chiFactor s * chiFactor (1 - s) = 1 := by
    dsimp [chiFactor]
    have h2_prod : (2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s) = 2 := by
      rw [← Complex.cpow_add s (1 - s) (by norm_num)]
      simp
    have hpi_prod :
        (Real.pi : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (1 - s - 1) = (Real.pi : ℂ)⁻¹ := by
      rw [← Complex.cpow_add (s - 1) (1 - s - 1)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      have hexp : (s - 1) + (1 - s - 1) = -1 := by ring
      rw [hexp, Complex.cpow_neg_one]
    have h_sin_cos :
        Complex.sin ((Real.pi : ℂ) * (1 - s) / 2) = Complex.cos ((Real.pi : ℂ) * s / 2) := by
      have heq : (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 := by
        ring
      rw [heq, Complex.sin_pi_div_two_sub]
    have h_double :
        Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.cos ((Real.pi : ℂ) * s / 2) =
          Complex.sin ((Real.pi : ℂ) * s) / 2 := by
      have h2m := Complex.sin_two_mul ((Real.pi : ℂ) * s / 2)
      have heq : 2 * ((Real.pi : ℂ) * s / 2) = (Real.pi : ℂ) * s := by ring
      rw [heq] at h2m
      linear_combination (1 / 2 : ℂ) * h2m.symm
    have h_gam : Complex.Gamma (1 - s) * Complex.Gamma (1 - (1 - s)) =
        (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s) := by
      have hsub : 1 - (1 - s) = s := by ring
      rw [hsub, mul_comm, Complex.Gamma_mul_Gamma_one_sub s]
    have h_sin_ne : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
      intro hzero
      rw [Complex.sin_eq_zero_iff] at hzero
      rcases hzero with ⟨k, hk⟩
      have h_re := congr_arg Complex.re hk
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      have hre1 : ((Real.pi : ℂ) * s).re = Real.pi * (1 / 2 : ℝ) := by simp [hs_re]
      have hre2 : ((k : ℂ) * (Real.pi : ℂ)).re = (k : ℝ) * Real.pi := by simp
      rw [hre1, hre2] at h_re
      have hhalf : (1 / 2 : ℝ) = (k : ℝ) := mul_right_cancel₀ hpi_ne (by linarith)
      have hk_int : (1 : ℝ) = 2 * (k : ℝ) := by linarith
      have hk2 : (1 : ℤ) = 2 * k := by exact_mod_cast hk_int
      omega
    have hpi_ne_c : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    calc
      (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.Gamma (1 - s) *
          ((2 : ℂ) ^ (1 - s) * (Real.pi : ℂ) ^ (1 - s - 1) *
            Complex.sin ((Real.pi : ℂ) * (1 - s) / 2) * Complex.Gamma (1 - (1 - s)))
        = ((2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s)) *
            ((Real.pi : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (1 - s - 1)) *
            (Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.sin ((Real.pi : ℂ) * (1 - s) / 2)) *
            (Complex.Gamma (1 - s) * Complex.Gamma (1 - (1 - s))) := by ring
      _ = 2 * (Real.pi : ℂ)⁻¹ * (Complex.sin ((Real.pi : ℂ) * s) / 2) *
            ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
          rw [h2_prod, hpi_prod, h_sin_cos, h_double, h_gam]
      _ = 1 := by field_simp [hpi_ne_c, h_sin_ne]
  have h_normSq : Complex.normSq (chiFactor s) = 1 := by
    have hm := Complex.mul_conj (chiFactor s)
    rw [h_conj_chi, h_prod] at hm
    have hre := congr_arg Complex.re hm.symm
    simpa using hre
  have h_norm_sq : ‖chiFactor s‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h_normSq
  have h_nonneg : 0 ≤ ‖chiFactor s‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖chiFactor s‖]

/-- **Littlewood's (1912) Forward Theorem:** If `M(x) = O(x ^ (1 / 2 + ε))` as `x → ∞` for every
`ε > 0`, then `RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_mertens_isBigO
    (hM : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    RiemannHypothesis := by
  have h_inv := mertens_inversion_of_bound hM
  rcases h_inv with ⟨I_M, hI⟩
  have h_nz : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := fun s hs h0 => by
    have h1 := hI s hs
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  intro s hs_zero hs_not_triv hs_not_one
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hs_lt | hs_gt
  · have ⟨h_refl_zero, h_refl_gt⟩ :=
      riemannZeta_zero_reflection hs_zero hs_not_triv hs_not_one hs_lt
    exact h_nz (1 - s) h_refl_gt h_refl_zero
  · exact h_nz s hs_gt hs_zero

/-! ### von Koch's (1901) Forward Theorem: Chebyshev `ψ` Remainder Bound Implies RH -/

/-- Chebyshev's second summatory function `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- Indicator remainder `(ψ(x) - x : ℂ)` on `(1, ∞)`, zero otherwise. -/
noncomputable def chebyshevPsiRemainder (x : ℝ) : ℂ :=
  if 1 < x then ((chebyshevPsi x - x : ℝ) : ℂ) else 0

/-- Mellin-von Koch remainder `J_ψ(s) = s * mellin chebyshevPsiRemainder (-s)`. -/
noncomputable def mellinVonKochRemainder (s : ℂ) : ℂ :=
  s * mellin chebyshevPsiRemainder (-s)

private lemma psi_monotone : Monotone chebyshevPsi := by
  intro x y hxy
  unfold chebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Iic_subset_Iic.mpr (Nat.floor_mono hxy)
  · intro i _ _; exact ArithmeticFunction.vonMangoldt_nonneg

private lemma psi_nonneg (x : ℝ) : 0 ≤ chebyshevPsi x := by
  unfold chebyshevPsi
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

private lemma psi_measurable : Measurable chebyshevPsi := psi_monotone.measurable

private lemma psi_icc_eq (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k) = chebyshevPsi t := by
  unfold chebyshevPsi
  have hsub : Finset.Iic ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
    ext k; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsub, Finset.sum_insert (by simp)]
  simp

private lemma sum_vonMangoldt_Icc_le_mul_log (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) ≤ (n : ℝ) * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hle : ∀ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k ≤ Real.log n := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
      calc
        ArithmeticFunction.vonMangoldt k ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hkn)
    calc
      (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
          ≤ ∑ _k ∈ Finset.Icc 1 n, Real.log n := Finset.sum_le_sum hle
      _ = ((Finset.Icc 1 n).card : ℝ) * Real.log n := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (n : ℝ) * Real.log n := by simp

private lemma id_mul_log_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => x * Real.log x) =O[atTop] fun x : ℝ => x ^ (1 + ε) := by
  have h1 : (fun x : ℝ => x * Real.log x) =O[atTop] fun x : ℝ => x * x ^ ε :=
    (isBigO_refl _ atTop).mul (isLittleO_log_rpow_atTop hε).isBigO
  refine h1.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [one_mul, Real.rpow_add hx, Real.rpow_one]

private lemma sum_vonMangoldt_Icc_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 + ε) := by
  have hcast : (fun n : ℕ => (n : ℝ) * Real.log n) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 + ε) :=
    (id_mul_log_isBigO_rpow hε).comp_tendsto tendsto_natCast_atTop_atTop
  refine (IsBigO.of_bound 1 ?_).trans hcast
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k :=
    Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hlog_nonneg : 0 ≤ (n : ℝ) * Real.log n :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  rw [one_mul, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hlog_nonneg]
  exact sum_vonMangoldt_Icc_le_mul_log n

private lemma chebyshevPsiRemainder_eq_indicator :
    chebyshevPsiRemainder =
      Set.indicator (Set.Ioi 1) (fun x : ℝ => ((chebyshevPsi x - x : ℝ) : ℂ)) := by
  ext x
  simp [chebyshevPsiRemainder, Set.indicator_apply]

private lemma chebyshevPsiRemainder_measurable : Measurable chebyshevPsiRemainder := by
  rw [chebyshevPsiRemainder_eq_indicator]
  exact (Complex.continuous_ofReal.measurable.comp
    (psi_measurable.sub measurable_id)).indicator measurableSet_Ioi

private lemma chebyshevPsiRemainder_locallyIntegrableOn :
    LocallyIntegrableOn chebyshevPsiRemainder (Set.Ioi 0) volume := by
  rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk_sub hk_comp
  obtain ⟨M, hM⟩ := hk_comp.bddAbove
  set R : ℝ := max M 0
  refine IntegrableOn.of_bound hk_comp.measure_lt_top
    chebyshevPsiRemainder_measurable.aestronglyMeasurable (chebyshevPsi R + R) ?_
  filter_upwards [ae_restrict_mem hk_comp.measurableSet] with x hx
  have hx_pos : 0 < x := hk_sub hx
  have hx_le_R : x ≤ R := le_trans (hM hx) (le_max_left _ _)
  unfold chebyshevPsiRemainder
  split_ifs with hx1
  · calc
      ‖((chebyshevPsi x - x : ℝ) : ℂ)‖ = |chebyshevPsi x - x| := Complex.norm_real _
      _ ≤ |chebyshevPsi x| + |x| := abs_sub _ _
      _ = chebyshevPsi x + x := by rw [abs_of_nonneg (psi_nonneg x), abs_of_pos hx_pos]
      _ ≤ chebyshevPsi R + R := add_le_add (psi_monotone hx_le_R) hx_le_R
  · simp only [norm_zero]
    exact add_nonneg (psi_nonneg R) (le_max_right M 0)

private lemma chebyshevPsiRemainder_isBigO_atTop_uncond {ε : ℝ} (hε : 0 < ε) :
    chebyshevPsiRemainder =O[atTop] fun x : ℝ => x ^ (1 + ε) := by
  have hlog : (fun x : ℝ => x * Real.log x) =O[atTop] fun x : ℝ => x ^ (1 + ε) :=
    id_mul_log_isBigO_rpow hε
  have hid : (fun x : ℝ => x) =O[atTop] fun x : ℝ => x ^ (1 + ε) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have hxpow0 : 0 ≤ x ^ (1 + ε) := Real.rpow_nonneg hx0 _
    rw [Real.norm_of_nonneg hx0, one_mul, Real.norm_of_nonneg hxpow0]
    calc
      x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hsum : (fun x : ℝ => x * Real.log x + x) =O[atTop] fun x : ℝ => x ^ (1 + ε) := hlog.add hid
  refine (IsBigO.of_bound 1 ?_).trans hsum
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx1 : 1 < x := by linarith
  have hfloor1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfloor_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor1
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hpsi_le : chebyshevPsi x ≤ x * Real.log x := by
    rw [← psi_icc_eq]
    calc
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k)
          ≤ (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) := sum_vonMangoldt_Icc_le_mul_log ⌊x⌋₊
      _ ≤ x * Real.log x := mul_le_mul hfloor_le (Real.log_le_log hfloor_pos hfloor_le)
          (Real.log_nonneg (by exact_mod_cast hfloor1)) (by linarith)
  have hxr : 0 ≤ x * Real.log x + x := by
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    nlinarith
  have hval : chebyshevPsiRemainder x = ((chebyshevPsi x - x : ℝ) : ℂ) := by
    simp [chebyshevPsiRemainder, hx1]
  rw [hval, Complex.norm_real, one_mul, Real.norm_of_nonneg hxr]
  calc
    |chebyshevPsi x - x| ≤ |chebyshevPsi x| + |x| := abs_sub _ _
    _ = chebyshevPsi x + x := by rw [abs_of_nonneg (psi_nonneg x), abs_of_pos (by linarith)]
    _ ≤ x * Real.log x + x := by linarith [hpsi_le]

private lemma chebyshevPsiRemainder_isBigO_atTop_of_vonKoch
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε))
    {ε : ℝ} (hε : 0 < ε) :
    chebyshevPsiRemainder =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  obtain ⟨C, hC⟩ := (hψ ε hε).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hval : chebyshevPsiRemainder x = ((chebyshevPsi x - x : ℝ) : ℂ) := by
    simp [chebyshevPsiRemainder, hx1]
  rw [hval, Complex.norm_real]
  exact hx

private lemma chebyshevPsiRemainder_isBigO_nhdsGT (b : ℝ) :
    chebyshevPsiRemainder =O[nhdsWithin 0 (Set.Ioi 0)] fun x : ℝ => x ^ (-b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  have hx1 : ¬ (1 < x) := not_lt.mpr hx.2.le
  have hval : chebyshevPsiRemainder x = 0 := by
    simp [chebyshevPsiRemainder, hx1]
  rw [hval, norm_zero, one_mul]
  exact norm_nonneg _

private lemma mellinVonKochRemainder_differentiableAt
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ mellinVonKochRemainder s := by
  let ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hm : DifferentiableAt ℂ (mellin chebyshevPsiRemainder) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 2 + ε)) (b := -s.re - 1)
      chebyshevPsiRemainder_locallyIntegrableOn ?_ ?_ (chebyshevPsiRemainder_isBigO_nhdsGT _) ?_
    · simpa only [neg_neg] using chebyshevPsiRemainder_isBigO_atTop_of_vonKoch hψ hε
    · simp only [neg_re, ε]; linarith
    · simp only [neg_re]; linarith
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- Under the von Koch remainder bound `ψ(x) - x = O(x ^ (1 / 2 + ε))` for all `ε > 0`,
`mellinVonKochRemainder` is analytic on `{s : ℂ | 1 / 2 < s.re}`. -/
theorem mellinVonKochRemainder_analyticOnNhd
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    AnalyticOnNhd ℂ mellinVonKochRemainder {s : ℂ | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro s hs
  exact (mellinVonKochRemainder_differentiableAt hψ hs).differentiableWithinAt

private lemma mellinConvergent_psiRemainder_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent chebyshevPsiRemainder (-s) := by
  let ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  refine mellinConvergent_of_isBigO_rpow (a := -(1 + ε)) (b := -s.re - 1)
    chebyshevPsiRemainder_locallyIntegrableOn ?_ ?_ (chebyshevPsiRemainder_isBigO_nhdsGT _) ?_
  · simpa only [neg_neg] using chebyshevPsiRemainder_isBigO_atTop_uncond hε
  · simp only [neg_re, ε]; linarith
  · simp only [neg_re]; linarith

private lemma mellin_psiRemainder_integrableOn_Ioi_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) volume := by
  have hm : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * chebyshevPsiRemainder t)
      (Set.Ioi 0) volume := by
    simpa [MellinConvergent, smul_eq_mul] using mellinConvergent_psiRemainder_of_one_lt_re hs
  have hind : IntegrableOn (Set.indicator (Set.Ioi 1)
      (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))))
      (Set.Ioi 0) volume := by
    refine hm.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only
    rw [chebyshevPsiRemainder_eq_indicator, mul_comm, Set.indicator_apply]
    have hexp : (-s - 1 : ℂ) = -(s + 1) := by ring
    rw [hexp, Set.indicator_apply]
    split_ifs <;> simp
  have hiff := (integrableOn_indicator_iff (s := Set.Ioi (1 : ℝ)) (t := Set.Ioi (0 : ℝ))
    (f := fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
    measurableSet_Ioi.nullMeasurableSet).mp hind
  have hinter : Set.Ioi (1 : ℝ) ∩ Set.Ioi (0 : ℝ) = Set.Ioi 1 :=
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one)
  rwa [hinter] at hiff

private lemma mellin_psiRemainder_eq_integral_Ioi_one (s : ℂ) :
    mellin chebyshevPsiRemainder (-s) =
      ∫ t in Set.Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  have hcongr : Set.EqOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) • chebyshevPsiRemainder t)
      (Set.indicator (Set.Ioi 1)
        (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))))
      (Set.Ioi 0) := by
    intro t _
    simp only [smul_eq_mul, chebyshevPsiRemainder_eq_indicator, Set.indicator_apply]
    have hexp : (-s - 1 : ℂ) = -(s + 1) := by ring
    rw [hexp]
    split_ifs <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioi]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioi (1 : ℝ) = Set.Ioi 1 :=
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)
  rw [hinter]

private lemma integrableOn_id_mul_cpow_Ioi_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) volume := by
  have hcpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) volume :=
    (integrableOn_Ioi_cpow_iff zero_lt_one).mpr (by simp; linarith)
  refine hcpow.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [Set.mem_Ioi.mp ht])
  calc
    (t : ℂ) ^ (-s) = (t : ℂ) ^ (1 + -(s + 1)) := by ring_nf
    _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := Complex.cpow_add _ _ ht0
    _ = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]

private lemma integral_id_mul_cpow_Ioi_one {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
  have hcongr : Set.EqOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [Set.mem_Ioi.mp ht])
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        rw [Complex.cpow_one]
      _ = (t : ℂ) ^ (1 + -(s + 1)) := (Complex.cpow_add _ _ ht0).symm
      _ = (t : ℂ) ^ (-s) := by ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by rw [h] at hs; norm_num at hs)
  have h1s : -s + 1 ≠ 0 := fun h => hs1 (by linear_combination -h)
  field_simp [hs1, h1s]
  ring

private lemma neg_deriv_riemannZeta_div_eq_pole_add_mellinVonKochRemainder
    {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = s / (s - 1) + mellinVonKochRemainder s := by
  let ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hint := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    (r := 1 + ε) (by linarith) (s := s) (by simp only [ε]; linarith)
    (sum_vonMangoldt_Icc_isBigO_rpow hε) (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  have hsplit : (∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) * (t : ℂ) ^ (-(s + 1))) =
      mellin chebyshevPsiRemainder (-s) + 1 / (s - 1) := by
    have hcongr : ∀ t : ℝ,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) * (t : ℂ) ^ (-(s + 1)) =
        ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) +
          (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      intro t
      have hpsi : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) =
          (chebyshevPsi t : ℂ) := by
        exact_mod_cast psi_icc_eq t
      rw [hpsi]
      push_cast
      ring
    simp_rw [hcongr]
    rw [integral_add (mellin_psiRemainder_integrableOn_Ioi_one hs)
        (integrableOn_id_mul_cpow_Ioi_one hs),
      mellin_psiRemainder_eq_integral_Ioi_one, integral_id_mul_cpow_Ioi_one hs]
  rw [← hL, hint, hsplit]
  unfold mellinVonKochRemainder
  ring

private lemma zeta_deriv_cleared_eq_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s + (s / (s - 1) + mellinVonKochRemainder s) * riemannZeta s = 0 := by
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h := neg_deriv_riemannZeta_div_eq_pole_add_mellinVonKochRemainder hs
  calc
    deriv riemannZeta s + (s / (s - 1) + mellinVonKochRemainder s) * riemannZeta s
        = deriv riemannZeta s + (-deriv riemannZeta s / riemannZeta s) * riemannZeta s := by rw [h]
    _ = 0 := by field_simp [hne]; ring

/-- Analytic continuation of the cleared logarithmic-derivative identity across
`{s : ℂ | 1 / 2 < s.re} \ {1}` under the von Koch remainder bound. -/
theorem zeta_deriv_cleared_eq_zero_of_half_lt_re_ne_one
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε))
    {s : ℂ} (hs_re : 1 / 2 < s.re) (hs_ne : s ≠ 1) :
    deriv riemannZeta s + (s / (s - 1) + mellinVonKochRemainder s) * riemannZeta s = 0 := by
  let F : ℂ → ℂ := fun z =>
    deriv riemannZeta z + (z / (z - 1) + mellinVonKochRemainder z) * riemannZeta z
  let U_dom : Set ℂ := {z : ℂ | 1 / 2 < z.re} \ {1}
  let U_top : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ 0 < z.im}
  let U_bot : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.im < 0}
  let U_left : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 1}
  have hU_dom_open : IsOpen U_dom :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ_ana : AnalyticOnNhd ℂ riemannZeta U_dom := by
    refine DifferentiableOn.analyticOnNhd ?_ hU_dom_open
    intro z hz
    exact (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have hpole_ana : AnalyticOnNhd ℂ (fun z : ℂ => z / (z - 1)) U_dom := by
    refine DifferentiableOn.analyticOnNhd ?_ hU_dom_open
    intro z hz
    have hnum : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hden : DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
      differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
    exact (hnum.div hden (sub_ne_zero.mpr hz.2)).differentiableWithinAt
  have hF_ana : AnalyticOnNhd ℂ F U_dom :=
    hζ_ana.deriv.add ((hpole_ana.add ((mellinVonKochRemainder_analyticOnNhd hψ).mono
      Set.sdiff_subset)).mul hζ_ana)
  have hU_top_sub : U_top ⊆ U_dom := fun z hz =>
    ⟨hz.1, fun h1 => by rcases Set.mem_singleton_iff.mp h1 with rfl; simp [U_top] at hz⟩
  have hU_bot_sub : U_bot ⊆ U_dom := fun z hz =>
    ⟨hz.1, fun h1 => by rcases Set.mem_singleton_iff.mp h1 with rfl; simp [U_bot] at hz⟩
  have hU_left_sub : U_left ⊆ U_dom := fun z hz =>
    ⟨hz.1, fun h1 => by rcases Set.mem_singleton_iff.mp h1 with rfl; simp [U_left] at hz⟩
  have hlin_gt : ∀ {a b c x y : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → c < x → c < y →
      c < a * x + b * y := by
    intro a b c x y ha hb hab hx hy
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 : a * c < a * x := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
      have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith
  have hlin_lt : ∀ {a b c x y : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → x < c → y < c →
      a * x + b * y < c := by
    intro a b c x y ha hb hab hx hy
    have h := hlin_gt ha hb hab (neg_lt_neg hx) (neg_lt_neg hy)
    linarith
  have hU_top_pre : IsPreconnected U_top := by
    have hconv : Convex ℝ U_top := by
      intro x hx y hy a b ha hb hab
      change 1 / 2 < (a • x + b • y).re ∧ 0 < (a • x + b • y).im
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      exact ⟨hlin_gt ha hb hab hx.1 hy.1, hlin_gt ha hb hab hx.2 hy.2⟩
    exact hconv.isPreconnected
  have hU_bot_pre : IsPreconnected U_bot := by
    have hconv : Convex ℝ U_bot := by
      intro x hx y hy a b ha hb hab
      change 1 / 2 < (a • x + b • y).re ∧ (a • x + b • y).im < 0
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      exact ⟨hlin_gt ha hb hab hx.1 hy.1, hlin_lt ha hb hab hx.2 hy.2⟩
    exact hconv.isPreconnected
  have hU_left_pre : IsPreconnected U_left := by
    have hconv : Convex ℝ U_left := by
      intro x hx y hy a b ha hb hab
      change 1 / 2 < (a • x + b • y).re ∧ (a • x + b • y).re < 1
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact ⟨hlin_gt ha hb hab hx.1 hy.1, hlin_lt ha hb hab hx.2 hy.2⟩
    exact hconv.isPreconnected
  have hright_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have htop_open : IsOpen U_top :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzero_top : Set.EqOn F 0 U_top := by
    refine (hF_ana.mono hU_top_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hU_top_pre (z₀ := (2 : ℂ) + I) (by simp [U_top]; norm_num) ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z : ℂ | 1 < z.re},
      hright_open.mem_nhds (by simp), fun z hz => zeta_deriv_cleared_eq_zero_of_one_lt_re hz⟩
  have hzero_bot : Set.EqOn F 0 U_bot := by
    refine (hF_ana.mono hU_bot_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hU_bot_pre (z₀ := (2 : ℂ) - I) (by simp [U_bot]; norm_num) ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z : ℂ | 1 < z.re},
      hright_open.mem_nhds (by simp), fun z hz => zeta_deriv_cleared_eq_zero_of_one_lt_re hz⟩
  have hzero_left : Set.EqOn F 0 U_left := by
    refine (hF_ana.mono hU_left_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hU_left_pre (z₀ := (3 / 4 : ℂ) + I) (by simp [U_left]; norm_num) ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨U_top,
      htop_open.mem_nhds (by simp [U_top]; norm_num), fun z hz => hzero_top hz⟩
  rcases lt_trichotomy s.re 1 with hlt | heq | hgt
  · exact hzero_left ⟨hs_re, hlt⟩
  · have him : s.im ≠ 0 := fun h0 => hs_ne (Complex.ext heq h0)
    rcases lt_or_gt_of_ne him with hneg | hpos
    · exact hzero_bot ⟨hs_re, hneg⟩
    · exact hzero_top ⟨hs_re, hpos⟩
  · exact zeta_deriv_cleared_eq_zero_of_one_lt_re hgt

private lemma riemannZeta_analyticOnNhd_ne_one :
    AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ne
  intro z hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

private lemma riemannZeta_not_eventually_zero {ρ : ℂ} (hre : 1 / 2 < ρ.re) :
    ¬ ∀ᶠ z in nhds ρ, riemannZeta z = 0 := by
  intro hev
  by_cases hge : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re hge hev.self_of_nhds
  push Not at hge
  let U_top : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ 0 < z.im}
  let U_left : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 1}
  have hlin_gt : ∀ {a b c x y : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → c < x → c < y →
      c < a * x + b * y := by
    intro a b c x y ha hb hab hx hy
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 : a * c < a * x := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
      have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith
  have hlin_lt : ∀ {a b c x y : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → x < c → y < c →
      a * x + b * y < c := by
    intro a b c x y ha hb hab hx hy
    have h := hlin_gt ha hb hab (neg_lt_neg hx) (neg_lt_neg hy)
    linarith
  have hU_top_pre : IsPreconnected U_top := by
    have hconv : Convex ℝ U_top := by
      intro x hx y hy a b ha hb hab
      change 1 / 2 < (a • x + b • y).re ∧ 0 < (a • x + b • y).im
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      exact ⟨hlin_gt ha hb hab hx.1 hy.1, hlin_gt ha hb hab hx.2 hy.2⟩
    exact hconv.isPreconnected
  have hU_left_pre : IsPreconnected U_left := by
    have hconv : Convex ℝ U_left := by
      intro x hx y hy a b ha hb hab
      change 1 / 2 < (a • x + b • y).re ∧ (a • x + b • y).re < 1
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact ⟨hlin_gt ha hb hab hx.1 hy.1, hlin_lt ha hb hab hx.2 hy.2⟩
    exact hconv.isPreconnected
  have hU_top_sub : U_top ⊆ {z : ℂ | z ≠ 1} := fun z hz h1 => by
    subst h1; simp [U_top] at hz
  have hU_left_sub : U_left ⊆ {z : ℂ | z ≠ 1} := fun z hz h1 => by
    subst h1; simp [U_left] at hz
  have hleft_open : IsOpen U_left :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hzero_left : Set.EqOn riemannZeta 0 U_left :=
    (riemannZeta_analyticOnNhd_ne_one.mono hU_left_sub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_left_pre ⟨hre, hge⟩ hev
  have hp : (3 / 4 : ℂ) + I ∈ U_left := by simp [U_left]; norm_num
  have hev2 : riemannZeta =ᶠ[nhds ((3 / 4 : ℂ) + I)] 0 :=
    Filter.eventually_of_mem (hleft_open.mem_nhds hp) fun z hz => hzero_left hz
  have hzero_top : Set.EqOn riemannZeta 0 U_top :=
    (riemannZeta_analyticOnNhd_ne_one.mono hU_top_sub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_top_pre (by simp [U_top]; norm_num) hev2
  have h2I : riemannZeta ((2 : ℂ) + I) = 0 := hzero_top (by simp [U_top]; norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by simp) h2I

/-- Zero-free half-plane `1 / 2 < s.re` under the von Koch remainder bound. -/
theorem zero_free_re_gt_half_of_vonKoch
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  intro ρ hre hζ
  have hne : ρ ≠ 1 := by
    intro h1
    subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp : (1 : ℝ) ≤ (1 : ℂ).re) hζ
  let P : ℂ → ℂ := fun z => z / (z - 1) + mellinVonKochRemainder z
  have hP : AnalyticAt ℂ P ρ := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => z / (z - 1)) ρ :=
      analyticAt_id.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne)
    exact h1.add (mellinVonKochRemainder_analyticOnNhd hψ ρ hre)
  have hζ_an : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_ne_one ρ hne
  obtain ⟨n, h, hh_an, hh_ne, hfac⟩ :=
    hζ_an.exists_eventuallyEq_pow_smul_nonzero_iff.mpr (riemannZeta_not_eventually_zero hre)
  simp only [smul_eq_mul] at hfac
  cases n with
  | zero =>
    have := hfac.self_of_nhds
    rw [hζ, pow_zero, one_mul] at this
    exact hh_ne this.symm
  | succ m =>
    have hdom : ∀ᶠ z in nhds ρ, 1 / 2 < z.re ∧ z ≠ 1 :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds ⟨hre, hne⟩
    have hcl : ∀ᶠ z in nhds ρ, deriv riemannZeta z + P z * riemannZeta z = 0 :=
      hdom.mono fun z hz => zeta_deriv_cleared_eq_zero_of_half_lt_re_ne_one hψ hz.1 hz.2
    have hd : ∀ᶠ z in nhds ρ, deriv riemannZeta z =
        ((m : ℂ) + 1) * (z - ρ) ^ m * h z + (z - ρ) ^ (m + 1) * deriv h z := by
      filter_upwards [hfac.eventually_nhds, hh_an.eventually_analyticAt] with y hy hhy
      rw [Filter.EventuallyEq.deriv_eq (f := fun z => (z - ρ) ^ (m + 1) * h z) hy]
      have hA : HasDerivAt (fun z : ℂ => (z - ρ) ^ (m + 1))
          (((m + 1 : ℕ) : ℂ) * (y - ρ) ^ (m + 1 - 1) * 1) y :=
        ((hasDerivAt_id y).sub_const ρ).pow (m + 1)
      have hB : HasDerivAt (fun z : ℂ => (z - ρ) ^ (m + 1) * h z)
          (((m + 1 : ℕ) : ℂ) * (y - ρ) ^ (m + 1 - 1) * 1 * h y +
            (y - ρ) ^ (m + 1) * deriv h y) y :=
        hA.mul hhy.differentiableAt.hasDerivAt
      rw [hB.deriv]
      simp only [Nat.add_sub_cancel, mul_one]
      push_cast
      ring
    let K : ℂ → ℂ := fun z => ((m : ℂ) + 1) * h z + (z - ρ) * (deriv h z + P z * h z)
    have hmain : ∀ᶠ z in nhds ρ, (z - ρ) ^ m * K z = 0 := by
      filter_upwards [hcl, hd, hfac] with z hcz hdz hfz
      have : (z - ρ) ^ m * K z = deriv riemannZeta z + P z * riemannZeta z := by
        rw [hdz, hfz]; simp only [K]; ring
      rw [this, hcz]
    have hK_ev : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, K z = 0 := by
      filter_upwards [nhdsWithin_le_nhds hmain, self_mem_nhdsWithin] with z hz hzne
      have hpow : (z - ρ) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hzne)
      exact (mul_eq_zero.mp hz).resolve_left hpow
    have hKc : ContinuousAt K ρ := by
      have h1 : ContinuousAt h ρ := hh_an.continuousAt
      have h2 : ContinuousAt (deriv h) ρ := hh_an.deriv.continuousAt
      have h3 : ContinuousAt P ρ := hP.continuousAt
      exact (continuousAt_const.mul h1).add
        ((continuousAt_id.sub continuousAt_const).mul (h2.add (h3.mul h1)))
    have hlim1 : Filter.Tendsto K (nhdsWithin ρ {ρ}ᶜ) (nhds (K ρ)) :=
      hKc.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Filter.Tendsto K (nhdsWithin ρ {ρ}ᶜ) (nhds 0) :=
      tendsto_const_nhds.congr' (hK_ev.mono fun z hz => hz.symm)
    have hK0 : K ρ = 0 := tendsto_nhds_unique hlim1 hlim2
    simp only [K, sub_self, zero_mul, add_zero] at hK0
    have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    exact hh_ne ((mul_eq_zero.mp hK0).resolve_left hm)

/-- **von Koch's (1901) Forward Theorem:** If `ψ(x) - x = O(x ^ (1 / 2 + ε))` as `x → ∞` for
every `ε > 0`, then `RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_chebyshevPsi_sub_self_isBigO
    (hψ : ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => chebyshevPsi x - x) =O[atTop] fun x => x ^ ((1 / 2 : ℝ) + ε)) :
    RiemannHypothesis := by
  have h_nofail := zero_free_re_gt_half_of_vonKoch hψ
  intro s hs_zero hs_not_triv hs_not_one
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hs_lt | hs_gt
  · have ⟨h_refl_zero, h_refl_gt⟩ :=
      riemannZeta_zero_reflection hs_zero hs_not_triv hs_not_one hs_lt
    exact h_nofail (1 - s) h_refl_gt h_refl_zero
  · exact h_nofail s hs_gt hs_zero
