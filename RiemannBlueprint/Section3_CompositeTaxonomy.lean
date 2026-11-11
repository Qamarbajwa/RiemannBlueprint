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

end RiemannBlueprint.Section3_CompositeTaxonomy
