import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Titchmarsh §2.1.5: Mellin Transform of `{1 / x}` & Abel Telescope (`MellinFracPart.lean`)

Formalizes:
1. Boundedness & integrability of `recipFract x = Int.fract (1 / x)` weighted by
   `x ^ (s - 1)` on `Ioc 0 1` (`0 < Re(s)`) and `Ioi 1` (`Re(s) < 1`).
2. Unconditional domain split `mellin_recipFract_split` via `setIntegral_union`,
   eliminating `h_split` from `mellin_frac_part_eq_neg_zeta_div`.
3. Algebraic Abel summation telescope `abel_harmonic_telescope` on `Finset.Ico 1 (M + 1)`.
-/

open MeasureTheory Set Filter

namespace NumberTheory.MellinFracPart

/-- Fractional part of the reciprocal: `recipFract x = {1 / x}`. -/
noncomputable def recipFract (x : ℝ) : ℝ :=
  Int.fract (1 / x)

/-- On the tail `1 < x`, `0 ≤ 1 / x < 1`, so `{1 / x} = 1 / x`. -/
lemma recipFract_eq_one_div_of_gt_one {x : ℝ} (hx : 1 < x) :
    recipFract x = 1 / x := by
  unfold recipFract
  rw [Int.fract_eq_self]
  exact ⟨div_nonneg zero_le_one (by linarith), div_lt_one (by linarith) |>.mpr hx⟩

/-- Pointwise bound `‖(recipFract x : ℂ)‖ ≤ 1` for all `x : ℝ`. -/
lemma norm_recipFract_le_one (x : ℝ) : ‖(recipFract x : ℂ)‖ ≤ 1 := by
  unfold recipFract
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- Measurability of `recipFract`. -/
lemma measurable_recipFract : Measurable recipFract :=
  measurable_fract.comp (measurable_const.div measurable_id)

/-- Integrability on `Ioc 0 1` for `0 < Re(s)`. -/
lemma integrableOn_Ioc_recipFract_cpow (s : ℂ) (hs_pos : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  refine hint_rpow.mono' ?_ ?_
  · refine (measurable_recipFract.complex_ofReal.aestronglyMeasurable.restrict).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono (fun x hx => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    have h1 : ‖(recipFract x : ℂ)‖ ≤ 1 := norm_recipFract_le_one x
    have h2 : 0 ≤ x ^ (s - 1).re := Real.rpow_nonneg hx.1.le _
    have hre : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    rw [hre] at h2 ⊢
    calc
      ‖(recipFract x : ℂ)‖ * x ^ (s.re - 1) ≤ 1 * x ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right h1 h2
      _ = x ^ (s.re - 1) := one_mul _

/-- Integrability on `Ioi 1` for `Re(s) < 1`. -/
lemma integrableOn_Ioi_recipFract_cpow (s : ℂ) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) := by
  have ha_lt : (s - 2).re < -1 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt ha_lt zero_lt_one).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx_gt : 1 < x := hx
  have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx_gt
  rw [recipFract_eq_one_div_of_gt_one hx_gt]
  push_cast
  rw [one_div, ← Complex.cpow_neg_one]
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  rw [← Complex.cpow_add _ _ hx_ne]
  congr 1
  ring

/-- Unconditional domain split of the Mellin integral of `recipFract` on `Ioi 0`
for `0 < Re(s) < 1` via `setIntegral_union`. -/
theorem mellin_recipFract_split (s : ℂ) (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
      (∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x 1 with hle | hgt
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr hgt
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [disjoint_left]
    intro x hx1 hx2
    linarith [hx1.2, mem_Ioi.mp hx2]
  rw [hunion]
  exact setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_Ioc_recipFract_cpow s hs_pos)
    (integrableOn_Ioi_recipFract_cpow s hs_lt_one)

/-- Improper integral of `x ^ a` on `(1, ∞)` for `Re(a) < -1`:
`∫ x in Ioi 1, (x : ℂ) ^ a = -(1 / (a + 1))`. -/
theorem integral_Ioi_cpow_of_lt_one {a : ℂ} (ha : a.re < -1) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ a = -(1 / (a + 1)) := by
  have ha1_ne : a + 1 ≠ 0 := by
    intro h
    have : (a + 1).re = (0 : ℂ).re := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hd : ∀ x ∈ Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) ((x : ℂ) ^ a) x := by
    intro x hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hpow := (hasDerivAt_ofReal_cpow_const hx_pos.ne' ha1_ne).div_const (a + 1)
    convert hpow using 1
    simp [ha1_ne, mul_div_cancel_left₀]
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    apply Tendsto.div_const
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hre : (a + 1).re < 0 := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hnorm : (fun t : ℝ => ‖(t : ℂ) ^ (a + 1)‖) =ᶠ[atTop] fun t : ℝ => t ^ (a + 1).re := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht_pos
      exact Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (a + 1)
    rw [tendsto_congr' hnorm]
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1).re)
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ a) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht
  simpa [zero_div, Complex.ofReal_one, Complex.one_cpow, neg_div] using hres

/-- Tail Mellin integral of `recipFract` on `(1, ∞)` for `Re(s) < 1`:
`∫ x in Ioi 1, {1 / x} * x ^ (s - 1) = -(1 / (s - 1))`. -/
theorem mellin_recipFract_tail (s : ℂ) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = -(1 / (s - 1)) := by
  have hcongr :
      ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx_gt : 1 < x := hx
    have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx_gt
    rw [recipFract_eq_one_div_of_gt_one hx_gt]
    push_cast
    rw [one_div, ← Complex.cpow_neg_one]
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    rw [← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  rw [hcongr]
  have ha_lt : (s - 2).re < -1 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  have htail := integral_Ioi_cpow_of_lt_one ha_lt
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rwa [hs21] at htail

/-- Master Titchmarsh §2.1.5 bridge: depends strictly on `h_unit` alone
(with `mellin_recipFract_split` and `mellin_recipFract_tail` both discharged). -/
theorem mellin_frac_part_eq_neg_zeta_div (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1)
    (h_unit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s) :
    ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = -(riemannZeta s / s) := by
  rw [mellin_recipFract_split s hs_pos hs_lt_one, h_unit, mellin_recipFract_tail s hs_lt_one]
  ring

/-- Algebraic Abel summation telescope for harmonic floor integrals over `n ∈ [1, M]`. -/
theorem abel_harmonic_telescope (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), ((n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))) =
      (∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
    push_cast
    ring

/-- On the harmonic sub-interval `(1 / (n + 1), 1 / n)` for `n ≥ 1`, `⌊1 / x⌋ = n`. -/
lemma floor_one_div_eq_of_mem_Ioo {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    ⌊1 / x⌋ = (n : ℤ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hx_pos : 0 < x := lt_trans (one_div_pos.mpr hn1_pos) hx.1
  rw [Int.floor_eq_iff]
  constructor
  · have h1 : (n : ℝ) = 1 / (1 / (n : ℝ)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h1]
    exact one_div_le_one_div_of_le hx_pos hx.2.le
  · have h2 : (n : ℝ) + 1 = 1 / (1 / ((n : ℝ) + 1)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h2]
    exact one_div_lt_one_div_of_lt (one_div_pos.mpr hn1_pos) hx.1

/-- Weighted sum of harmonic floor interval contributions via `abel_harmonic_telescope`. -/
theorem sum_harmonic_floor_integral_eq (s : ℂ) (_hs_ne_zero : s ≠ 0) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), ((n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))) =
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hterm :
      (∑ n ∈ Finset.Ico 1 (M + 1), ((n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)))) =
        (1 / s) * ∑ n ∈ Finset.Ico 1 (M + 1), ((n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  rw [hterm, abel_harmonic_telescope]

/-- The `k`-th Vasyunin reciprocal fractional-part kernel `x ↦ {1 / (k * x)}`. -/
noncomputable def recipFractScaled (k : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((k : ℝ) * x))

/-- Mellin dilation scaling law for `recipFractScaled k` (`k ≥ 1`, `0 < Re(s) < 1`). -/
theorem mellin_recipFractScaled_eq (k : ℕ) (hk : 1 ≤ k) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1)
    (h_unit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s) :
    ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / (s * (k : ℂ) ^ s)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) 0 hk_pos
  have hmul0 : (k : ℝ) * 0 = 0 := mul_zero _
  rw [hmul0] at hscale
  have hcongr :
      ∫ x in Ioi (0 : ℝ), (recipFract ((k : ℝ) * x) : ℂ) * (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) =
        (k : ℂ) ^ (s - 1) * ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx_pos : 0 < x := hx
    have hcp : (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg hk_pos.le hx_pos.le (s - 1)
    rw [hcp]
    change (recipFract ((k : ℝ) * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1)) =
      (k : ℂ) ^ (s - 1) * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
    unfold recipFractScaled recipFract
    ring
  rw [hcongr] at hscale
  have hmellin := mellin_frac_part_eq_neg_zeta_div s hs_pos hs_lt_one h_unit
  rw [hmellin] at hscale
  have hsmul : ((k : ℝ)⁻¹ : ℝ) • -(riemannZeta s / s) = (k : ℂ)⁻¹ * -(riemannZeta s / s) := by
    rw [Complex.real_smul, Complex.ofReal_inv]
    rfl
  rw [hsmul] at hscale
  have hpow_s : (k : ℂ) ^ s = (k : ℂ) * (k : ℂ) ^ (s - 1) := by
    have h1 : s = 1 + (s - 1) := by ring
    conv_lhs => rw [h1, Complex.cpow_add _ _ hk_ne, Complex.cpow_one]
  calc
    ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
      = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ) ^ (s - 1) *
          ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    _ = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ)⁻¹ * -(riemannZeta s / s)) := by rw [hscale]
    _ = -(riemannZeta s / (s * (k : ℂ) ^ s)) := by
        rw [hpow_s]
        field_simp [hk_ne, hpow_ne]

/-- Unity indicator Mellin transform on `Ioc 0 1` for `0 < Re(s)`:
`∫ x in Ioc 0 1, (x : ℂ) ^ (s - 1) = 1 / s`. -/
theorem mellin_indicator_Ioc_one (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) = 1 / s := by
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h] at hs_pos
    simp at hs_pos
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hs_sub : (-1 : ℝ) < (s - 1).re := by
    simp [Complex.sub_re]
    linarith
  have hcp := integral_cpow (a := (0 : ℝ)) (b := (1 : ℝ)) (Or.inl hs_sub)
  rw [hcp]
  have hs1 : s - 1 + 1 = s := by ring
  rw [hs1, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hs_ne, sub_zero]

/-- Integrability of the `k`-th scaled Vasyunin kernel on `Ioi 0` for `k ≥ 1`
and `0 < Re(s) < 1`. -/
lemma integrableOn_Ioi_recipFractScaled_cpow (k : ℕ) (hk : 1 ≤ k) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x 1 with hle | hgt
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr hgt
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  have hint_unscaled : IntegrableOn (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    rw [hunion]
    exact (integrableOn_Ioc_recipFract_cpow s hs_pos).union (integrableOn_Ioi_recipFract_cpow s hs_lt_one)
  rw [← integrable_indicator_iff measurableSet_Ioi] at hint_unscaled ⊢
  have hcomp := hint_unscaled.comp_mul_left' hk_pos.ne'
  have hscale :
      Integrable (fun x : ℝ =>
        ((k : ℂ) ^ (s - 1))⁻¹ *
          ((Ioi (0 : ℝ)).indicator (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) ((k : ℝ) * x))) :=
    hcomp.const_mul ((k : ℂ) ^ (s - 1))⁻¹
  refine hscale.congr (ae_of_all _ (fun x => ?_))
  dsimp only
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · have hkx : (k : ℝ) * x ∈ Ioi (0 : ℝ) := mul_pos hk_pos hx
    rw [indicator_of_mem hx, indicator_of_mem hkx]
    have hcp : (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg hk_pos.le (mem_Ioi.mp hx).le (s - 1)
    rw [hcp]
    change ((k : ℂ) ^ (s - 1))⁻¹ * ((recipFract ((k : ℝ) * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1))) =
      (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
    unfold recipFractScaled recipFract
    field_simp [hpow_ne]
  · have hkx : (k : ℝ) * x ∉ Ioi (0 : ℝ) := by
      intro hmem
      apply hx
      exact (mul_pos_iff_of_pos_left hk_pos).mp hmem
    rw [indicator_of_notMem hx, indicator_of_notMem hkx, mul_zero]

/-- Finite `N`-term Vasyunin subspace combination Mellin transform (`0 < Re(s) < 1`). -/
theorem mellin_vasyunin_sum_eq (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1)
    (h_unit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s) :
    ∫ x in Ioi (0 : ℝ), (∑ k ∈ Finset.Ico 1 (N + 1), c k * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / s) * ∑ k ∈ Finset.Ico 1 (N + 1), c k * (k : ℂ) ^ (-s) := by
  have hsum_eq :
      (fun x : ℝ => (∑ k ∈ Finset.Ico 1 (N + 1), c k * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1)) =
        fun x : ℝ => ∑ k ∈ Finset.Ico 1 (N + 1), c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hsum_eq, integral_finsetSum]
  · calc
      ∑ k ∈ Finset.Ico 1 (N + 1),
          ∫ x in Ioi (0 : ℝ), c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
        = ∑ k ∈ Finset.Ico 1 (N + 1),
            c k * ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) := by
          refine Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
      _ = ∑ k ∈ Finset.Ico 1 (N + 1), c k * -(riemannZeta s / (s * (k : ℂ) ^ s)) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
          rw [mellin_recipFractScaled_eq k hk1 s hs_pos hs_lt_one h_unit]
      _ = -(riemannZeta s / s) * ∑ k ∈ Finset.Ico 1 (N + 1), c k * (k : ℂ) ^ (-s) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
          have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk1)
          rw [Complex.cpow_neg]
          ring
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    exact (integrableOn_Ioi_recipFractScaled_cpow k hk1 s hs_pos hs_lt_one).const_mul (c k)

/-- Full Báez-Duarte residual Mellin identity (`g_N`), yielding the exact
Criterion 1 Plancherel integrand numerator `(1 + ζ(s) * ∑ c_k k^{-s}) / s`. -/
theorem mellin_baezDuarte_residual_eq (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1)
    (h_unit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s) :
    (∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
    (∫ x in Ioi (0 : ℝ), (∑ k ∈ Finset.Ico 1 (N + 1), c k * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1)) =
      (1 + riemannZeta s * ∑ k ∈ Finset.Ico 1 (N + 1), c k * (k : ℂ) ^ (-s)) / s := by
  rw [mellin_indicator_Ioc_one s hs_pos, mellin_vasyunin_sum_eq N c s hs_pos hs_lt_one h_unit]
  ring

/-- Power integral on a single harmonic sub-interval `Ioc (1 / (n + 1)) (1 / n)`
for `n ≥ 1` and `0 < Re(s)`. -/
lemma integral_Ioc_harmonic_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (x : ℂ) ^ (s - 1) =
      ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_pos (by linarith)
  rw [← intervalIntegral.integral_of_le hle]
  have hs_sub : (-1 : ℝ) < (s - 1).re := by
    simp [Complex.sub_re]
    linarith
  rw [integral_cpow (Or.inl hs_sub)]
  have hs1 : s - 1 + 1 = s := by ring
  rw [hs1]
  have inv_cpow_nat : ∀ m : ℕ, ((1 / (m : ℝ) : ℝ) : ℂ) ^ s = (m : ℂ) ^ (-s) := by
    intro m
    push_cast
    have harg : (m : ℂ).arg ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]
      exact Real.pi_ne_zero.symm
    rw [one_div, Complex.inv_cpow_eq_ite, if_neg harg, Complex.cpow_neg]
  have h1 : ((1 / (n : ℝ) : ℝ) : ℂ) ^ s = (n : ℂ) ^ (-s) := inv_cpow_nat n
  have h2 : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ s = ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    simpa [Nat.cast_add, Nat.cast_one] using inv_cpow_nat (n + 1)
  rw [h1, h2]

/-- Floor integral on a single harmonic sub-interval `Ioc (1 / (n + 1)) (1 / n)`
for `n ≥ 1` and `0 < Re(s)`. -/
theorem integral_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))),
      ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) = (n : ℂ) * (x : ℂ) ^ (s - 1) := by
    have hdiff : ∀ᵐ x ∂volume, x ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) →
        x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
      have hne : ∀ᵐ x ∂volume, x ≠ (1 / (n : ℝ)) := ae_iff.mpr (by simp [measure_singleton])
      filter_upwards [hne] with x hne hx
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hdiff] with x hx_imp hx_ioc
    rw [floor_one_div_eq_of_mem_Ioo hn (hx_imp hx_ioc)]
    simp
  rw [integral_congr_ae hae, integral_const_mul, integral_Ioc_harmonic_cpow n hn s hs_pos]
  ring

/-- Finite harmonic sum of floor integrals over `n ∈ [1, M]` (`0 < Re(s)`). -/
theorem sum_integral_Ioc_harmonic_floor_eq (M : ℕ) (s : ℂ) (hs_pos : 0 < s.re) :
    ∑ n ∈ Finset.Ico 1 (M + 1),
      (∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1)) =
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h] at hs_pos
    simp at hs_pos
  rw [Finset.sum_congr rfl (fun n hn =>
    integral_Ioc_harmonic_floor_cpow n (Finset.mem_Ico.mp hn).1 s hs_pos)]
  exact sum_harmonic_floor_integral_eq s hs_ne M

/-- Integrability of `⌊1 / x⌋ * x ^ (s - 1)` on a single harmonic sub-interval
`Ioc (1 / (n + 1)) (1 / n)` for `n ≥ 1`. -/
lemma integrableOn_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_pos (by linarith)
  have hcont : ContinuousOn (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (s - 1))
      (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    refine ContinuousOn.mul continuousOn_const (fun x hx => ?_)
    have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx_pos.ne')).continuousWithinAt
  have hint_const : IntegrableOn (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))),
      (n : ℂ) * (x : ℂ) ^ (s - 1) = ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    have hdiff : ∀ᵐ x ∂volume, x ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) →
        x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
      have hne : ∀ᵐ x ∂volume, x ≠ (1 / (n : ℝ)) := ae_iff.mpr (by simp [measure_singleton])
      filter_upwards [hne] with x hne hx
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hdiff] with x hx_imp hx_ioc
    rw [floor_one_div_eq_of_mem_Ioo hn (hx_imp hx_ioc)]
    simp
  exact hint_const.congr hae

/-- Truncated harmonic partition integral and integrability on `Ioc (1 / (M + 1)) 1`. -/
lemma truncated_floor_partition_aux (M : ℕ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((M : ℝ) + 1)) 1) ∧
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ∑ n ∈ Finset.Ico 1 (M + 1),
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  induction M with
  | zero =>
    have hIoc : Ioc (1 / ((0 : ℝ) + 1)) 1 = ∅ := by norm_num
    simp [hIoc]
  | succ M ih =>
    rcases ih with ⟨ih_int, ih_eq⟩
    have ha : 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    have hb : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) :=
      div_le_one_of_le₀ (by linarith) (by positivity)
    have hunion : Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) 1 =
        Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)) ∪ Ioc (1 / ((M : ℝ) + 1)) 1 :=
      (Ioc_union_Ioc_eq_Ioc ha hb).symm
    have hdisj : Disjoint (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)))
        (Ioc (1 / ((M : ℝ) + 1)) 1) := by
      rw [disjoint_left]
      intro x hx1 hx2
      linarith [hx1.2, hx2.1]
    have hleft_int : IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
        (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1))) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        integrableOn_Ioc_harmonic_floor_cpow (M + 1) (by omega) s
    refine ⟨?_, ?_⟩
    · rw [hunion]
      exact hleft_int.union ih_int
    · rw [hunion, setIntegral_union hdisj measurableSet_Ioc hleft_int ih_int, ih_eq,
        Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), add_comm]
      congr 1
      simp [Nat.cast_add, Nat.cast_one]

/-- Truncated unit-interval floor integral over `Ioc (1 / (M + 1)) 1` (`0 < Re(s)`). -/
theorem integral_Ioc_truncated_floor_cpow (M : ℕ) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  rw [(truncated_floor_partition_aux M s).2]
  exact sum_integral_Ioc_harmonic_floor_eq M s hs_pos

/-- Integrability and value of `(1 / x) * x ^ (s - 1)` on `Ioc (1 / (M + 1)) 1` (`s ≠ 1`). -/
lemma integrableOn_Ioc_truncated_inv_mul_cpow (M : ℕ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((M : ℝ) + 1)) 1) := by
  have hcont : ContinuousOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Icc (1 / ((M : ℝ) + 1)) 1) := by
    refine ContinuousOn.mul ?_ (fun x hx => ?_)
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact continuousOn_const.div continuousOn_id (fun x hx => by
        have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr (by positivity)) hx.1
        exact hx_pos.ne')
    · have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr (by positivity)) hx.1
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx_pos.ne')).continuousWithinAt
  exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Power integral of `(1 / x) * x ^ (s - 1)` on `Ioc (1 / (M + 1)) 1` for `s ≠ 1`. -/
lemma integral_Ioc_truncated_inv_mul_cpow (M : ℕ) (s : ℂ) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
  have hle : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) :=
    div_le_one_of_le₀ (by linarith) (by positivity)
  have hcongr :
      ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
        ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr (by positivity)) hx.1.le
    push_cast
    rw [one_div, ← Complex.cpow_neg_one]
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    rw [← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  rw [hcongr, ← intervalIntegral.integral_of_le hle]
  have hs2_ne : s - 2 ≠ -1 := by
    intro h
    apply hs_ne_one
    linear_combination h
  have h0_not_mem : (0 : ℝ) ∉ uIcc (1 / ((M : ℝ) + 1)) 1 := by
    rw [uIcc_of_le hle, mem_Icc]
    intro h0
    linarith [one_div_pos.mpr (by positivity : (0 : ℝ) < (M : ℝ) + 1), h0.1]
  rw [integral_cpow (Or.inr ⟨hs2_ne, h0_not_mem⟩)]
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rw [hs21, Complex.ofReal_one, Complex.one_cpow]
  have hinv : ((1 / ((M : ℝ) + 1) : ℝ) : ℂ) ^ (s - 1) = ((M + 1 : ℕ) : ℂ) ^ (1 - s) := by
    push_cast
    have harg : (((M + 1 : ℕ) : ℂ)).arg ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
      exact Real.pi_ne_zero.symm
    have hcast : ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, one_div, Complex.inv_cpow_eq_ite, ite_eq_right_iff.mpr (fun h => absurd h harg),
      ← Complex.cpow_neg]
    congr 1
    ring
  rw [hinv]

/-- Truncated unit-interval `recipFract` Mellin identity on `Ioc (1 / (M + 1)) 1`
for `0 < Re(s)` and `s ≠ 1`. -/
theorem integral_Ioc_truncated_recipFract_cpow (M : ℕ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hdecomp :
      (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
        (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) - ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  rw [hdecomp, integral_sub (integrableOn_Ioc_truncated_inv_mul_cpow M s)
    (truncated_floor_partition_aux M s).1]
  rw [integral_Ioc_truncated_inv_mul_cpow M s hs_ne_one,
    integral_Ioc_truncated_floor_cpow M s hs_pos]

/-- Partition of `Ioc 0 1` at `1 / (M + 1)` (`M : ℕ`, `0 < Re(s)`). -/
theorem integral_Ioc_one_eq_near_zero_add_truncated (M : ℕ) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
      (∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
  have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
  have hunion : Ioc (0 : ℝ) 1 =
      Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)) ∪ Ioc (1 / ((M : ℝ) + 1)) 1 :=
    (Ioc_union_Ioc_eq_Ioc h0 h1).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) (Ioc (1 / ((M : ℝ) + 1)) 1) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  have hint := integrableOn_Ioc_recipFract_cpow s hs_pos
  have hint1 : IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) := hint.mono_set (Ioc_subset_Ioc_right h1)
  have hint2 : IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((M : ℝ) + 1)) 1) := hint.mono_set (Ioc_subset_Ioc_left h0)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc hint1 hint2]

/-- Explicit `L¹` norm bound on the near-zero tail `Ioc 0 (1 / (M + 1))` for `0 < Re(s)`. -/
theorem norm_integral_Ioc_near_zero_le (M : ℕ) (s : ℂ) (hs_pos : 0 < s.re) :
    ‖∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ((M : ℝ) + 1) ^ (-s.re) / s.re := by
  have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
  have hint_fn : IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) :=
    (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set (Ioc_subset_Ioc_right h1)
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1))
      (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h0]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  have hle_int :
      ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) := by
    refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc (fun x hx => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    have hre : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    rw [hre]
    calc
      ‖(recipFract x : ℂ)‖ * x ^ (s.re - 1) ≤ 1 * x ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right (norm_recipFract_le_one x) (Real.rpow_nonneg hx.1.le _)
      _ = x ^ (s.re - 1) := one_mul _
  have hval :
      ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) =
        ((M : ℝ) + 1) ^ (-s.re) / s.re := by
    rw [← intervalIntegral.integral_of_le h0,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s.re - 1))]
    have hs1 : s.re - 1 + 1 = s.re := by ring
    rw [hs1, Real.zero_rpow hs_pos.ne', sub_zero, one_div,
      Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)

/-- Near-zero tail vanishing as `M → ∞` (`0 < Re(s)`). -/
theorem tendsto_integral_Ioc_near_zero_atTop (s : ℂ) (hs_pos : 0 < s.re) :
    Tendsto (fun M : ℕ =>
      ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      atTop (nhds 0) := by
  have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re) / s.re) atTop (nhds (0 / s.re)) :=
    ((tendsto_rpow_neg_atTop hs_pos).comp hm).div_const s.re
  rw [zero_div] at ht
  exact squeeze_zero_norm (fun M => norm_integral_Ioc_near_zero_le M s hs_pos) ht

/-- Convergence of the truncated `recipFract` integral on `Ioc (1 / (M + 1)) 1`
to the full unit-interval integral as `M → ∞` (`0 < Re(s)`). -/
theorem tendsto_integral_Ioc_truncated_recipFract_atTop (s : ℂ) (hs_pos : 0 < s.re) :
    Tendsto (fun M : ℕ =>
      ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      atTop (nhds (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))) := by
  have hsub :
      (fun M : ℕ => ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
        fun M : ℕ =>
          (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) -
          (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext M
    have hsplit := integral_Ioc_one_eq_near_zero_add_truncated M s hs_pos
    linear_combination -hsplit
  rw [hsub]
  simpa using tendsto_const_nhds.sub (tendsto_integral_Ioc_near_zero_atTop s hs_pos)

/-- Truncated Titchmarsh §2.1.5 right-hand side sequence. -/
noncomputable def truncatedTitchmarshRHS (s : ℂ) (M : ℕ) : ℂ :=
  (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
  (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s))

/-- `truncatedTitchmarshRHS s` converges to the unit-interval `recipFract` Mellin
integral for `0 < Re(s)` and `s ≠ 1`. -/
theorem tendsto_truncatedTitchmarshRHS_eq_unit (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Tendsto (truncatedTitchmarshRHS s) atTop
      (nhds (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))) := by
  have heq : truncatedTitchmarshRHS s = fun M : ℕ =>
      ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext M
    exact (integral_Ioc_truncated_recipFract_cpow M s hs_pos hs_ne_one).symm
  rw [heq]
  exact tendsto_integral_Ioc_truncated_recipFract_atTop s hs_pos

/-- Discharges `h_unit` from the Euler–Maclaurin / zeta limit of `truncatedTitchmarshRHS`. -/
theorem mellin_recipFract_unit_interval_of_tendsto_rhs (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1)
    (h_rhs : Tendsto (truncatedTitchmarshRHS s) atTop (nhds (1 / (s - 1) - riemannZeta s / s))) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s :=
  tendsto_nhds_unique (tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one) h_rhs

/-- Alias for `mellin_recipFract_unit_interval_of_tendsto_rhs`. -/
theorem h_unit_of_tendsto_truncatedTitchmarshRHS (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1)
    (h_rhs : Tendsto (truncatedTitchmarshRHS s) atTop (nhds (1 / (s - 1) - riemannZeta s / s))) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s :=
  mellin_recipFract_unit_interval_of_tendsto_rhs s hs_pos hs_ne_one h_rhs

/-- The `n`-th harmonic unit-interval summand (with denominator `s - 1` matching
the positive orientation of `∫_{1/(n+1)}^{1/n} x^(s-2) dx`). -/
noncomputable def harmonicUnitSummand (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
  ((n : ℂ) / s) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))

/-- Exact telescoping representation of `truncatedTitchmarshRHS s M` for `s ≠ 0, 1`. -/
theorem sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS (s : ℂ)
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n = truncatedTitchmarshRHS s M := by
  have htelesc :
      ∑ n ∈ Finset.Ico 1 (M + 1), ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) =
        (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
    induction M with
    | zero =>
      simp
    | succ M ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
      have hcast : ((M + 1 : ℕ) : ℂ) + 1 = ((M + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [← hcast]
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne_one
      field_simp [hsub]
      ring
  unfold harmonicUnitSummand
  rw [Finset.sum_sub_distrib, htelesc, sum_harmonic_floor_integral_eq s hs_ne_zero M]
  rfl

/-- Boundary vanishing `((M + 1 : ℕ) : ℂ) ^ (1 - s) → 0` for `1 < Re(s)`. -/
lemma tendsto_succ_cpow_one_sub_atTop (s : ℂ) (hs_gt_one : 1 < s.re) :
    Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℂ) ^ (1 - s)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun M : ℕ => ‖((M + 1 : ℕ) : ℂ) ^ (1 - s)‖) =
      fun M : ℕ => ((M : ℝ) + 1) ^ (1 - s.re) := by
    ext M
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : (((M + 1 : ℕ) : ℂ)) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp [Complex.sub_re]
  rw [hnorm]
  have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hpow : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hpow' : Tendsto (fun x : ℝ => x ^ (1 - s.re)) atTop (nhds 0) := by
    simpa [neg_sub] using hpow
  exact hpow'.comp hm

/-- Boundary vanishing `(M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) → 0` for `1 < Re(s)`. -/
lemma tendsto_mul_succ_cpow_neg_atTop (s : ℂ) (hs_gt_one : 1 < s.re) :
    Tendsto (fun M : ℕ => (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds 0) := by
  have hle : ∀ M : ℕ, ‖(M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ((M : ℝ) + 1) ^ (1 - s.re) := by
    intro M
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : (((M + 1 : ℕ) : ℂ)) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.norm_natCast]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    have h1 : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
    calc
      (M : ℝ) * ((M : ℝ) + 1) ^ (-s.re)
        ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
      _ = ((M : ℝ) + 1) ^ (1 : ℝ) * ((M : ℝ) + 1) ^ (-s.re) := by rw [Real.rpow_one]
      _ = ((M : ℝ) + 1) ^ (1 - s.re) := by
          rw [← Real.rpow_add hpos, sub_eq_add_neg]
  have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hpow : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hpow' : Tendsto (fun x : ℝ => x ^ (1 - s.re)) atTop (nhds 0) := by
    simpa [neg_sub] using hpow
  have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (1 - s.re)) atTop (nhds 0) :=
    hpow'.comp hm
  exact squeeze_zero_norm hle ht

/-- Zeta partial sum convergence for `1 < Re(s)`. -/
theorem tendsto_sum_Ico_cpow_neg_eq_riemannZeta (s : ℂ) (hs_gt_one : 1 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s))
      atTop (nhds (riemannZeta s)) := by
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h] at hs_gt_one
    simp at hs_gt_one
    linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs_gt_one
  have hhas : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs_gt_one]
    exact hsum.hasSum
  have ht := hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq : (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s) =
      fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s) := by
    ext M
    induction M with
    | zero =>
      simp [Complex.zero_cpow hs_ne]
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
      congr 1
      rw [one_div, Complex.cpow_neg]
  have ht' : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s)
      atTop (nhds (riemannZeta s)) := ht
  rwa [heq] at ht'

/-- Unconditional unit-interval Titchmarsh §2.1.5 theorem for `1 < Re(s)`. -/
theorem mellin_recipFract_unit_interval_of_one_lt_re (s : ℂ) (hs_gt_one : 1 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs_gt_one
    simp at hs_gt_one
  have h_rhs : Tendsto (truncatedTitchmarshRHS s) atTop
      (nhds (1 / (s - 1) - riemannZeta s / s)) := by
    have h1 : Tendsto (fun M : ℕ => (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) atTop
        (nhds ((1 - 0) / (s - 1))) :=
      (tendsto_const_nhds.sub (tendsto_succ_cpow_one_sub_atTop s hs_gt_one)).div_const (s - 1)
    have h2 : Tendsto (fun M : ℕ => (1 / s) *
        ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) -
          (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s))) atTop
        (nhds ((1 / s) * (riemannZeta s - 0))) :=
      tendsto_const_nhds.mul
        ((tendsto_sum_Ico_cpow_neg_eq_riemannZeta s hs_gt_one).sub
          (tendsto_mul_succ_cpow_neg_atTop s hs_gt_one))
    have h12 : Tendsto (fun M : ℕ => truncatedTitchmarshRHS s M) atTop
        (nhds ((1 - 0) / (s - 1) - (1 / s) * (riemannZeta s - 0))) := by
      simpa [truncatedTitchmarshRHS] using h1.sub h2
    simpa [sub_zero, one_mul, div_eq_mul_inv, mul_comm] using h12
  exact mellin_recipFract_unit_interval_of_tendsto_rhs s hs_pos hs_ne_one h_rhs

/-- Single harmonic sub-interval `recipFract` integral identity (`n ≥ 1`, `0 < Re(s)`, `s ≠ 1`). -/
theorem integral_Ioc_harmonic_recipFract_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      harmonicUnitSummand s n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_pos (by linarith)
  have hdecomp :
      (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
        (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) -
          ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  have hint1 : IntegrableOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    have hcont : ContinuousOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
        (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
      refine ContinuousOn.mul ?_ (fun x hx => ?_)
      · refine Complex.continuous_ofReal.comp_continuousOn ?_
        exact continuousOn_const.div continuousOn_id (fun x hx => by
          have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1
          exact hx_pos.ne')
      · have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1
        exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx_pos.ne')).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint2 := integrableOn_Ioc_harmonic_floor_cpow n hn s
  have hinv :
      ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
        ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
    have hcongr :
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
          ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (x : ℂ) ^ (s - 2) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1.le
      push_cast
      rw [one_div, ← Complex.cpow_neg_one]
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
      rw [← Complex.cpow_add _ _ hx_ne]
      congr 1
      ring
    rw [hcongr, ← intervalIntegral.integral_of_le hle]
    have hs2_ne : s - 2 ≠ -1 := by
      intro h
      apply hs_ne_one
      linear_combination h
    have h0_not_mem : (0 : ℝ) ∉ uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
      rw [uIcc_of_le hle, mem_Icc]
      intro h0
      linarith [one_div_pos.mpr hn1_pos, h0.1]
    rw [integral_cpow (Or.inr ⟨hs2_ne, h0_not_mem⟩)]
    have hs21 : s - 2 + 1 = s - 1 := by ring
    rw [hs21]
    have inv_cpow_nat : ∀ m : ℕ, ((1 / (m : ℝ) : ℝ) : ℂ) ^ (s - 1) = (m : ℂ) ^ (1 - s) := by
      intro m
      push_cast
      have harg : (m : ℂ).arg ≠ Real.pi := by
        rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]
        exact Real.pi_ne_zero.symm
      rw [one_div, Complex.inv_cpow_eq_ite, ite_eq_right_iff.mpr (fun h => absurd h harg),
        ← Complex.cpow_neg]
      congr 1
      ring
    have h1 : ((1 / (n : ℝ) : ℝ) : ℂ) ^ (s - 1) = (n : ℂ) ^ (1 - s) := inv_cpow_nat n
    have h2 : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ (s - 1) = ((n + 1 : ℕ) : ℂ) ^ (1 - s) := by
      simpa [Nat.cast_add, Nat.cast_one] using inv_cpow_nat (n + 1)
    rw [h1, h2]
  rw [hdecomp, integral_sub hint1 hint2, hinv, integral_Ioc_harmonic_floor_cpow n hn s hs_pos]
  rfl

/-- Telescoping `L¹` norm bound on `harmonicUnitSummand s n` (`n ≥ 1`, `0 < Re(s)`, `s ≠ 1`). -/
theorem norm_harmonicUnitSummand_le (n : ℕ) (hn : 1 ≤ n) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ‖harmonicUnitSummand s n‖ ≤
      ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re := by
  rw [← integral_Ioc_harmonic_recipFract_cpow n hn s hs_pos hs_ne_one]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_pos (by linarith)
  have hsub : Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) ⊆ Ioc (0 : ℝ) 1 :=
    Ioc_subset_Ioc (by positivity) (div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity))
  have hint_fn : IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :=
    (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set hsub
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    have hcont : ContinuousOn (fun x : ℝ => x ^ (s.re - 1))
        (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := fun x hx =>
      (Real.continuousAt_rpow_const _ _
        (Or.inl (lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1).ne')).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle_int :
      ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (s.re - 1) := by
    refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc (fun x hx => ?_)
    have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1.le
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hre : (s - 1).re = s.re - 1 := by simp [Complex.sub_re]
    rw [hre]
    calc
      ‖(recipFract x : ℂ)‖ * x ^ (s.re - 1) ≤ 1 * x ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right (norm_recipFract_le_one x) (Real.rpow_nonneg hx_pos.le _)
      _ = x ^ (s.re - 1) := one_mul _
  have hval :
      ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (s.re - 1) =
        ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re := by
    rw [← intervalIntegral.integral_of_le hle,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s.re - 1))]
    have hs1 : s.re - 1 + 1 = s.re := by ring
    rw [hs1]
    have inv_rpow_nat : ∀ m : ℕ, (1 / (m : ℝ)) ^ s.re = (m : ℝ) ^ (-s.re) := fun m => by
      rw [one_div, Real.inv_rpow (Nat.cast_nonneg m), Real.rpow_neg (Nat.cast_nonneg m)]
    have h1 := inv_rpow_nat n
    have h2 : (1 / ((n : ℝ) + 1)) ^ s.re = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
      simpa [Nat.cast_add, Nat.cast_one] using inv_rpow_nat (n + 1)
    rw [h1, h2]
  exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)

/-- Partial sums of `harmonicUnitSummand s` converge to the unit-interval `recipFract`
Mellin integral across all `0 < Re(s)` (`s ≠ 1`). -/
theorem tendsto_sum_harmonicUnitSummand_eq_unit_integral (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n)
      atTop (nhds (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))) := by
  have hs_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at hs_pos
    simp at hs_pos
  have heq : (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n) =
      truncatedTitchmarshRHS s := by
    ext M
    exact sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS s hs_ne_zero hs_ne_one M
  rw [heq]
  exact tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one

/-- Critical-strip analytic continuation bridge: if the harmonic series `harmonicUnitSummand s`
converges to `1 / (s - 1) - riemannZeta s / s`, then both `h_unit` and `mellin_frac_part_eq_neg_zeta_div`
hold on `0 < Re(s) < 1`. -/
theorem riemannZeta_eq_of_harmonicUnitSummand (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1)
    (h_sum : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n)
      atTop (nhds (1 / (s - 1) - riemannZeta s / s))) :
    (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s) ∧
    (∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = -(riemannZeta s / s)) := by
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs_lt_one
    simp at hs_lt_one
  have h_unit :
      ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        1 / (s - 1) - riemannZeta s / s :=
    tendsto_nhds_unique (tendsto_sum_harmonicUnitSummand_eq_unit_integral s hs_pos hs_ne_one) h_sum
  exact ⟨h_unit, mellin_frac_part_eq_neg_zeta_div s hs_pos hs_lt_one h_unit⟩

#print axioms norm_recipFract_le_one
#print axioms integrableOn_Ioc_recipFract_cpow
#print axioms integrableOn_Ioi_recipFract_cpow
#print axioms mellin_recipFract_split
#print axioms mellin_recipFract_tail
#print axioms mellin_frac_part_eq_neg_zeta_div
#print axioms abel_harmonic_telescope
#print axioms floor_one_div_eq_of_mem_Ioo
#print axioms sum_harmonic_floor_integral_eq
#print axioms mellin_recipFractScaled_eq
#print axioms mellin_indicator_Ioc_one
#print axioms integrableOn_Ioi_recipFractScaled_cpow
#print axioms mellin_vasyunin_sum_eq
#print axioms mellin_baezDuarte_residual_eq
#print axioms integral_Ioc_harmonic_cpow
#print axioms integral_Ioc_harmonic_floor_cpow
#print axioms sum_integral_Ioc_harmonic_floor_eq
#print axioms integral_Ioc_truncated_floor_cpow
#print axioms integral_Ioc_truncated_inv_mul_cpow
#print axioms integral_Ioc_truncated_recipFract_cpow
#print axioms integral_Ioc_one_eq_near_zero_add_truncated
#print axioms norm_integral_Ioc_near_zero_le
#print axioms tendsto_integral_Ioc_near_zero_atTop
#print axioms tendsto_integral_Ioc_truncated_recipFract_atTop
#print axioms tendsto_truncatedTitchmarshRHS_eq_unit
#print axioms mellin_recipFract_unit_interval_of_tendsto_rhs
#print axioms h_unit_of_tendsto_truncatedTitchmarshRHS
#print axioms sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS
#print axioms tendsto_sum_Ico_cpow_neg_eq_riemannZeta
#print axioms mellin_recipFract_unit_interval_of_one_lt_re
#print axioms integral_Ioc_harmonic_recipFract_cpow
#print axioms norm_harmonicUnitSummand_le
#print axioms tendsto_sum_harmonicUnitSummand_eq_unit_integral
#print axioms riemannZeta_eq_of_harmonicUnitSummand

end NumberTheory.MellinFracPart
