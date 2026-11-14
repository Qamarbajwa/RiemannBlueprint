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

end NumberTheory.MellinFracPart
