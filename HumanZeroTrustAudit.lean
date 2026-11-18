import RiemannBlueprint.MathlibPR_ZeroFreeRegion
import RiemannBlueprint.MathlibPR_HardyZeros
import RiemannBlueprint.MathlibPR_VasyuninCrossIntegral
import RiemannBlueprint.MathlibPR_ForwardCandidate
set_option pp.all true
theorem audit_target1 : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 2 ≤ |s.im| → 1 - c / (Real.log (|s.im| + 2)) ^ 9 < s.re → _root_.riemannZeta s ≠ 0 := deLaValleePoussin_zero_free_region_unconditional
theorem audit_target2 : {t : ℝ | _root_.hardyZ t = 0}.Infinite := infinite_hardyZ_zeros
theorem audit_global_opt_four (c : ℕ → ℝ) (hc1 : MathlibPR.ForwardCandidate.D1 c 4 = 0) (hc0 : MathlibPR.ForwardCandidate.D0 c 4 = 2) : 1 - ((19 + Real.sqrt 3) / 72) * Real.pi ≤ ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 4, c k * MathlibPR.ForwardCandidate.recipFractScaled k x) ^ 2 := MathlibPR.ForwardCandidate.l2_dist_cGlobalOptFour_le_of_mem_A_four c hc1 hc0
theorem audit_cauchy_schwarz {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ) (hh1 : MathlibPR.ForwardCandidate.D1 h N = 0) (hh0 : MathlibPR.ForwardCandidate.D0 h N = 0) : (Real.pi * MathlibPR.ForwardCandidate.linearCotDrive h N) ^ 2 ≤ MathlibPR.ForwardCandidate.QCot MathlibPR.ForwardCandidate.vasyuninGCot h N := MathlibPR.ForwardCandidate.sq_linearCotDrive_le_qcot hN h hh1 hh0
theorem audit_rayleigh_rh_bridge (h_ray : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∃ h : ℕ → ℝ, MathlibPR.ForwardCandidate.D1 h N = 0 ∧ MathlibPR.ForwardCandidate.D0 h N = 0 ∧ 1 - ε < MathlibPR.ForwardCandidate.tangentRayleighQuotient h N) : _root_.RiemannHypothesis := MathlibPR.ForwardCandidate.riemannHypothesis_of_tangentRayleighQuotient_limit h_ray
#print axioms audit_target1
#print axioms audit_target2
#print axioms audit_global_opt_four
#print axioms audit_cauchy_schwarz
#print axioms audit_rayleigh_rh_bridge
