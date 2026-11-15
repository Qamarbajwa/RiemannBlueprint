import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannBlueprint.Section2_PrimeAtoms

/-!
# Section 3: Algebraic & Modular Taxonomy of the Composite System ℂ
Formalization of Section 3 from the monograph.
-/

namespace RiemannBlueprint.Section3_CompositeTaxonomy

open RiemannBlueprint.Section2_PrimeAtoms (Primes Composites)

/-- Definition 3.1: Arithmetic Factor Counting Functions ω(n) and Ω(n). -/
def omega (n : ℕ) : ℕ := n.primeFactors.card
def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Definition 3.2: Pure and Mixed Composites. -/
def PureComposites : Set ℕ := { n | ∃ (p : ℕ) (k : ℕ), Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k }
def MixedComposites : Set ℕ := { n | n ∈ Composites ∧ omega n ≥ 2 }

/-- Proposition 3.3: Exact Arithmetic Classification of ℕ = {1} ∪ ℙ ∪ ℂ (mutually disjoint). -/
theorem arithmetic_classification_partition :
    Disjoint Section2_PrimeAtoms.Units Primes ∧
    Disjoint Section2_PrimeAtoms.Units Composites ∧
    Disjoint Primes Composites := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_iff]
    intro x ⟨hx1, hx2⟩
    have h1 : x = 1 := hx1
    have hp : Nat.Prime x := hx2
    rw [h1] at hp
    exact Nat.Prime.not_dvd_one hp (dvd_refl 1)
  · rw [Set.disjoint_iff]
    intro x ⟨hx1, hx2⟩
    have h1 : x = 1 := hx1
    have hc : x > 1 ∧ ¬ Nat.Prime x := hx2
    omega
  · rw [Set.disjoint_iff]
    intro x ⟨hx1, hx2⟩
    have hp : Nat.Prime x := hx1
    have hc : x > 1 ∧ ¬ Nat.Prime x := hx2
    exact hc.2 hp

/-- Proposition 3.4: Pure and Mixed Composites are Disjoint. -/
theorem pure_mixed_composite_partition : Disjoint PureComposites MixedComposites := by
  rw [Set.disjoint_iff]
  intro x ⟨hx_pure, hx_mixed⟩
  rcases hx_pure with ⟨p, k, hp, hk, rfl⟩
  have hk_pos : k ≠ 0 := by omega
  have h_factors : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk_pos hp
  have h_omega : omega (p ^ k) = 1 := by
    dsimp [omega]
    rw [h_factors, Finset.card_singleton]
  have h_mixed_omega : omega (p ^ k) ≥ 2 := hx_mixed.2
  omega

/-- Proposition 3.5: Isolation via the von Mangoldt function. -/
theorem von_mangoldt_isolation (n : ℕ) (hn : omega n ≥ 2) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  intro h_pow
  rw [isPrimePow_iff_card_primeFactors_eq_one] at h_pow
  dsimp [omega] at hn
  omega

/-- Corollary 3.6: Divisor Count for Composites c: d(c) ≥ 3. -/
theorem divisor_count_composite (c : ℕ) (hc : c ∈ Composites) :
    c.divisors.card ≥ 3 := by
  rcases hc with ⟨hc_gt, hc_not_prime⟩
  have hc_two : 2 ≤ c := hc_gt
  have hc_ne_zero : c ≠ 0 := by omega
  have h_not_all : ¬(∀ m < c, m ∣ c → m = 1) := by
    intro h_all
    have hp : Nat.Prime c := Nat.prime_def_lt.mpr ⟨hc_two, h_all⟩
    exact hc_not_prime hp
  push Not at h_not_all
  rcases h_not_all with ⟨d, hd_lt, hd_dvd, hd_ne_one⟩
  have hd_pos : d ≠ 0 := by
    rintro rfl
    have : c = 0 := Nat.eq_zero_of_zero_dvd hd_dvd
    omega
  have hd_gt_one : 1 < d := by
    have : 1 ≤ d := Nat.pos_of_ne_zero hd_pos
    omega
  have h1 : 1 ∈ c.divisors := Nat.mem_divisors.mpr ⟨one_dvd c, hc_ne_zero⟩
  have hc_mem : c ∈ c.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hc_ne_zero⟩
  have hd_mem : d ∈ c.divisors := Nat.mem_divisors.mpr ⟨hd_dvd, hc_ne_zero⟩
  have h_sub : {1, d, c} ⊆ c.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h1_not_mem : 1 ∉ ({d, c} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by omega, by omega⟩
  have hd_not_mem : d ∉ ({c} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have h_card : ({1, d, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem h1_not_mem]
    rw [Finset.card_insert_of_notMem hd_not_mem]
    rw [Finset.card_singleton]
  have := Finset.card_le_card h_sub
  omega

/-- Proposition 3.7: Prime vs. Composite Totient Gap. -/
theorem prime_vs_composite_totient_gap (c : ℕ) (hc : c ∈ Composites) :
    Nat.totient c < c - 1 := by
  rcases hc with ⟨hc_gt, hc_not_prime⟩
  have h_ne : Nat.totient c ≠ c - 1 := by
    intro h_eq
    have hp : Nat.Prime c := (Nat.totient_eq_iff_prime (by omega)).mp h_eq
    exact hc_not_prime hp
  have h_tot_lt : Nat.totient c ≤ c - 1 := Nat.le_sub_one_of_lt (Nat.totient_lt c hc_gt)
  exact lt_of_le_of_ne h_tot_lt h_ne

/-- Proposition 3.8: The Coprime Composite Lattice. -/
theorem coprime_composite_lattice (u v : ℕ) (hu : u > 1) (hv : v > 1) :
    u * v ∈ Composites := by
  refine ⟨by nlinarith, ?_⟩
  intro hp
  have h_dvd : u ∣ u * v := dvd_mul_right u v
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp u h_dvd) with rfl | hu_eq
  · omega
  · have h_eq : u * v = u * 1 := by rw [mul_one, ← hu_eq]
    have : v = 1 := mul_left_cancel₀ (by omega) h_eq
    omega

/-- **Korselt Criterion Predicate** for composite odd Fermat-type pseudoprimes:
`n > 1`, `¬ Nat.Prime n`, and every prime factor `p ∣ n` satisfies `(p - 1) ∣ (n - 1)`. -/
def SatisfiesKorseltCriterion (n : ℕ) : Prop :=
  1 < n ∧ ¬ Nat.Prime n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1)

private lemma totient_three_distinct_primes (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Nat.totient (p * (q * r)) = (p - 1) * ((q - 1) * (r - 1)) := by
  have hcpq : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun hdvd =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have hcpr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).mpr fun hdvd =>
    hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd)
  have hcqr : Nat.Coprime q r := (hq.coprime_iff_not_dvd).mpr fun hdvd =>
    hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hdvd)
  have hcp_qr : Nat.Coprime p (q * r) := hcpq.mul_right hcpr
  rw [Nat.totient_mul hcp_qr, Nat.totient_mul hcqr,
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr]

private lemma card_divisors_three_distinct_primes (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (p * (q * r)).divisors.card = 8 := by
  have hcpq : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun hdvd =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have hcpr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).mpr fun hdvd =>
    hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd)
  have hcqr : Nat.Coprime q r := (hq.coprime_iff_not_dvd).mpr fun hdvd =>
    hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hdvd)
  have hcp_qr : Nat.Coprime p (q * r) := hcpq.mul_right hcpr
  rw [hcp_qr.card_divisors_mul, hcqr.card_divisors_mul,
    hp.divisors, hq.divisors, hr.divisors,
    Finset.card_pair hp.ne_one.symm, Finset.card_pair hq.ne_one.symm,
    Finset.card_pair hr.ne_one.symm]

private lemma korselt_of_three_primes (n p q r : ℕ) (hn : n = p * (q * r))
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hdp : (p - 1) ∣ (n - 1)) (hdq : (q - 1) ∣ (n - 1)) (hdr : (r - 1) ∣ (n - 1)) :
    ∀ x : ℕ, Nat.Prime x → x ∣ n → (x - 1) ∣ (n - 1) := by
  intro x hx hxd
  rw [hn] at hxd
  rcases hx.dvd_mul.mp hxd with hxp | hxqr
  · rw [(Nat.prime_dvd_prime_iff_eq hx hp).mp hxp]
    exact hdp
  · rcases hx.dvd_mul.mp hxqr with hxq | hxr
    · rw [(Nat.prime_dvd_prime_iff_eq hx hq).mp hxq]
      exact hdq
    · rw [(Nat.prime_dvd_prime_iff_eq hx hr).mp hxr]
      exact hdr

/-- **Korselt–Carmichael & Totient-Unmasking Theorem (`561`, `1105`, `1729`):**
Certifies unconditionally that the first three Carmichael numbers — `561 = 3 * 11 * 17`,
`1105 = 5 * 13 * 17`, and Hardy–Ramanujan's `1729 = 7 * 13 * 19 = 12^3 + 1^3 = 10^3 + 9^3` —
all lie in `Composites` and satisfy Korselt's Criterion `(p - 1) ∣ (n - 1)` for all primes `p ∣ n`,
yet are unmasked from primes by `n - φ(n) ∈ {241, 337, 433} > 1` and `d(n) - 2 = 6 > 0`. -/
theorem carmichael_korselt_and_totient_unmasking :
    (561 = 3 * 11 * 17 ∧ 561 ∈ Composites ∧ SatisfiesKorseltCriterion 561 ∧
      561 - Nat.totient 561 = 241 ∧ 1 < 561 - Nat.totient 561 ∧
      (561 : ℕ).divisors.card - 2 = 6) ∧
    (1105 = 5 * 13 * 17 ∧ 1105 ∈ Composites ∧ SatisfiesKorseltCriterion 1105 ∧
      1105 - Nat.totient 1105 = 337 ∧ 1 < 1105 - Nat.totient 1105 ∧
      (1105 : ℕ).divisors.card - 2 = 6) ∧
    (1729 = 7 * 13 * 19 ∧ 12 ^ 3 + 1 ^ 3 = 1729 ∧ 10 ^ 3 + 9 ^ 3 = 1729 ∧
      1729 ∈ Composites ∧ SatisfiesKorseltCriterion 1729 ∧
      1729 - Nat.totient 1729 = 433 ∧ 1 < 1729 - Nat.totient 1729 ∧
      (1729 : ℕ).divisors.card - 2 = 6) := by
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  have h11 : Nat.Prime 11 := by decide
  have h13 : Nat.Prime 13 := by decide
  have h17 : Nat.Prime 17 := by decide
  have h19 : Nat.Prime 19 := by decide
  have h561_comp : (561 : ℕ) ∈ Composites := by
    rw [show (561 : ℕ) = 3 * 187 by norm_num]
    exact coprime_composite_lattice 3 187 (by omega) (by omega)
  have h1105_comp : (1105 : ℕ) ∈ Composites := by
    rw [show (1105 : ℕ) = 5 * 221 by norm_num]
    exact coprime_composite_lattice 5 221 (by omega) (by omega)
  have h1729_comp : (1729 : ℕ) ∈ Composites := by
    rw [show (1729 : ℕ) = 7 * 247 by norm_num]
    exact coprime_composite_lattice 7 247 (by omega) (by omega)
  have h561_tot : Nat.totient 561 = 320 := by
    rw [show (561 : ℕ) = 3 * (11 * 17) by norm_num,
      totient_three_distinct_primes 3 11 17 h3 h11 h17 (by omega) (by omega) (by omega)]
  have h1105_tot : Nat.totient 1105 = 768 := by
    rw [show (1105 : ℕ) = 5 * (13 * 17) by norm_num,
      totient_three_distinct_primes 5 13 17 h5 h13 h17 (by omega) (by omega) (by omega)]
  have h1729_tot : Nat.totient 1729 = 1296 := by
    rw [show (1729 : ℕ) = 7 * (13 * 19) by norm_num,
      totient_three_distinct_primes 7 13 19 h7 h13 h19 (by omega) (by omega) (by omega)]
  have h561_div : (561 : ℕ).divisors.card = 8 := by
    rw [show (561 : ℕ) = 3 * (11 * 17) by norm_num]
    exact card_divisors_three_distinct_primes 3 11 17 h3 h11 h17 (by omega) (by omega) (by omega)
  have h1105_div : (1105 : ℕ).divisors.card = 8 := by
    rw [show (1105 : ℕ) = 5 * (13 * 17) by norm_num]
    exact card_divisors_three_distinct_primes 5 13 17 h5 h13 h17 (by omega) (by omega) (by omega)
  have h1729_div : (1729 : ℕ).divisors.card = 8 := by
    rw [show (1729 : ℕ) = 7 * (13 * 19) by norm_num]
    exact card_divisors_three_distinct_primes 7 13 19 h7 h13 h19 (by omega) (by omega) (by omega)
  have h561_kor : SatisfiesKorseltCriterion 561 :=
    ⟨by omega, h561_comp.2, korselt_of_three_primes 561 3 11 17 (by norm_num) h3 h11 h17
      ⟨280, by norm_num⟩ ⟨56, by norm_num⟩ ⟨35, by norm_num⟩⟩
  have h1105_kor : SatisfiesKorseltCriterion 1105 :=
    ⟨by omega, h1105_comp.2, korselt_of_three_primes 1105 5 13 17 (by norm_num) h5 h13 h17
      ⟨276, by norm_num⟩ ⟨92, by norm_num⟩ ⟨69, by norm_num⟩⟩
  have h1729_kor : SatisfiesKorseltCriterion 1729 :=
    ⟨by omega, h1729_comp.2, korselt_of_three_primes 1729 7 13 19 (by norm_num) h7 h13 h19
      ⟨288, by norm_num⟩ ⟨144, by norm_num⟩ ⟨96, by norm_num⟩⟩
  refine ⟨⟨by norm_num, h561_comp, h561_kor, ?_, ?_, ?_⟩,
    ⟨by norm_num, h1105_comp, h1105_kor, ?_, ?_, ?_⟩,
    ⟨by norm_num, by norm_num, by norm_num, h1729_comp, h1729_kor, ?_, ?_, ?_⟩⟩ <;> omega

end RiemannBlueprint.Section3_CompositeTaxonomy
