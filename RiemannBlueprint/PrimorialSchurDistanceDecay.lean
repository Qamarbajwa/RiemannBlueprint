/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Primorial Schur Distance Decay & Block-Banachiewicz Identity

`NO_RH_PROOF = TRUE`:
The Clay Riemann Hypothesis remains strictly OPEN. This module proves the exact
finite-dimensional Block-Banachiewicz Schur distance split
`d_N^2 = d_{N,Prime}^2 - Δ_Schur(C | P)` and nonnegativity of `Δ_Schur(C | P)`
strictly within Lean's foundational axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace RiemannBlueprint.PrimorialSchurDistanceDecay

open Matrix

/-- **Block-Banachiewicz Right Inverse:**
For block matrix `Q = fromBlocks Q_PP Q_PC Q_CP Q_CC`, if `Q_PP_inv` is the inverse of `Q_PP`
and `Sigma_inv` is the inverse of the Schur complement `Sigma = Q_CC - Q_CP * Q_PP_inv * Q_PC`,
then the Banachiewicz block matrix is the exact right inverse of `Q`. -/
theorem block_banachiewicz_mul_eq_one {p c : ℕ}
    (Q_PP : Matrix (Fin p) (Fin p) ℝ)
    (Q_PC : Matrix (Fin p) (Fin c) ℝ)
    (Q_CP : Matrix (Fin c) (Fin p) ℝ)
    (Q_CC : Matrix (Fin c) (Fin c) ℝ)
    (Q_PP_inv : Matrix (Fin p) (Fin p) ℝ)
    (Sigma_inv : Matrix (Fin c) (Fin c) ℝ)
    (hPP_r : Q_PP * Q_PP_inv = 1)
    (hS_r : (Q_CC - Q_CP * Q_PP_inv * Q_PC) * Sigma_inv = 1) :
    let Q := fromBlocks Q_PP Q_PC Q_CP Q_CC
    let B11 := Q_PP_inv + Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv
    let B12 := -(Q_PP_inv * Q_PC * Sigma_inv)
    let B21 := -(Sigma_inv * Q_CP * Q_PP_inv)
    let B22 := Sigma_inv
    Q * fromBlocks B11 B12 B21 B22 = 1 := by
  intro Q B11 B12 B21 B22
  dsimp [Q, B11, B12, B21, B22]
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · -- Top-left block:
    have h1 : Q_PP * (Q_PP_inv + Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv) +
        Q_PC * -(Sigma_inv * Q_CP * Q_PP_inv) = 1 := by
      rw [Matrix.mul_add, hPP_r, Matrix.mul_neg]
      have hassoc : Q_PP * (Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv) =
          (Q_PP * Q_PP_inv) * (Q_PC * Sigma_inv * Q_CP * Q_PP_inv) := by
        simp only [Matrix.mul_assoc]
      rw [hassoc, hPP_r, Matrix.one_mul]
      have hneg : Q_PC * (Sigma_inv * Q_CP * Q_PP_inv) =
          Q_PC * Sigma_inv * Q_CP * Q_PP_inv := by
        simp only [Matrix.mul_assoc]
      rw [hneg]
      abel
    exact h1
  · -- Top-right block:
    have h2 : Q_PP * -(Q_PP_inv * Q_PC * Sigma_inv) + Q_PC * Sigma_inv = 0 := by
      rw [Matrix.mul_neg]
      have hassoc : Q_PP * (Q_PP_inv * Q_PC * Sigma_inv) =
          (Q_PP * Q_PP_inv) * (Q_PC * Sigma_inv) := by
        simp only [Matrix.mul_assoc]
      rw [hassoc, hPP_r, Matrix.one_mul, neg_add_cancel]
    exact h2
  · -- Bottom-left block:
    have h3 : Q_CP * (Q_PP_inv + Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv) +
        Q_CC * -(Sigma_inv * Q_CP * Q_PP_inv) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_neg]
      have hassoc1 : Q_CP * (Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv) =
          (Q_CP * Q_PP_inv * Q_PC) * Sigma_inv * (Q_CP * Q_PP_inv) := by
        simp only [Matrix.mul_assoc]
      have hassoc2 : Q_CC * (Sigma_inv * Q_CP * Q_PP_inv) =
          Q_CC * Sigma_inv * (Q_CP * Q_PP_inv) := by
        simp only [Matrix.mul_assoc]
      rw [hassoc1, hassoc2]
      calc
        Q_CP * Q_PP_inv + Q_CP * Q_PP_inv * Q_PC * Sigma_inv * (Q_CP * Q_PP_inv) +
            -(Q_CC * Sigma_inv * (Q_CP * Q_PP_inv))
            = Q_CP * Q_PP_inv -
                ((Q_CC - Q_CP * Q_PP_inv * Q_PC) * Sigma_inv) * (Q_CP * Q_PP_inv) := by
                rw [Matrix.sub_mul, Matrix.sub_mul]
                abel
        _ = Q_CP * Q_PP_inv - (1 : Matrix (Fin c) (Fin c) ℝ) * (Q_CP * Q_PP_inv) := by
                rw [hS_r]
        _ = 0 := by rw [Matrix.one_mul, sub_self]
    exact h3
  · -- Bottom-right block:
    have h4 : Q_CP * -(Q_PP_inv * Q_PC * Sigma_inv) + Q_CC * Sigma_inv = 1 := by
      rw [Matrix.mul_neg]
      have hassoc : Q_CP * (Q_PP_inv * Q_PC * Sigma_inv) =
          (Q_CP * Q_PP_inv * Q_PC) * Sigma_inv := by
        simp only [Matrix.mul_assoc]
      rw [hassoc, neg_add_eq_sub, ← Matrix.sub_mul, hS_r]
    exact h4

/-- **Block-Banachiewicz Schur Distance Identity (`d_N^2 = d_{N,Prime}^2 - Δ_Schur(C | P)`):**
For symmetric `Q_PP_inv`, `Q_PC = Q_CPᵀ`, and partitioned target vector `(ρ_P, ρ_C)`,
the quadratic form of the Banachiewicz inverse block matrix splits `1 - ρᵀ Q⁻¹ ρ` into
`(1 - ρ_Pᵀ Q_PP⁻¹ ρ_P) - (ρ_C - Q_CP Q_PP⁻¹ ρ_P)ᵀ Σ_N⁻¹ (ρ_C - Q_CP Q_PP⁻¹ ρ_P)`. -/
theorem block_banachiewicz_schur_distance_split {p c : ℕ}
    (Q_CP : Matrix (Fin c) (Fin p) ℝ)
    (Q_PP_inv : Matrix (Fin p) (Fin p) ℝ)
    (Sigma_inv : Matrix (Fin c) (Fin c) ℝ)
    (hPP_sym : Q_PP_invᵀ = Q_PP_inv)
    (ρ_P : Fin p → ℝ) (ρ_C : Fin c → ℝ) :
    let Q_PC := Q_CPᵀ
    let B11 := Q_PP_inv + Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv
    let B12 := -(Q_PP_inv * Q_PC * Sigma_inv)
    let B21 := -(Sigma_inv * Q_CP * Q_PP_inv)
    let B22 := Sigma_inv
    let Q_inv := fromBlocks B11 B12 B21 B22
    let ρ : Fin p ⊕ Fin c → ℝ := Sum.elim ρ_P ρ_C
    let δ : Fin c → ℝ := ρ_C - Q_CP.mulVec (Q_PP_inv.mulVec ρ_P)
    1 - dotProduct ρ (Q_inv.mulVec ρ) =
      (1 - dotProduct ρ_P (Q_PP_inv.mulVec ρ_P)) -
        dotProduct δ (Sigma_inv.mulVec δ) := by
  intro Q_PC B11 B12 B21 B22 Q_inv ρ δ
  have hQinv_mul : Q_inv.mulVec ρ =
      Sum.elim (B11.mulVec ρ_P + B12.mulVec ρ_C)
               (B21.mulVec ρ_P + B22.mulVec ρ_C) := by
    ext x
    rcases x with i | j <;>
      simp [Q_inv, ρ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hdot : dotProduct ρ (Q_inv.mulVec ρ) =
      dotProduct ρ_P (B11.mulVec ρ_P + B12.mulVec ρ_C) +
      dotProduct ρ_C (B21.mulVec ρ_P + B22.mulVec ρ_C) := by
    rw [hQinv_mul]
    dsimp [ρ]
    simp [dotProduct, Fintype.sum_sum_type]
  -- Let w = Q_CP *ᵥ (Q_PP_inv *ᵥ ρ_P) and u = Q_PP_inv *ᵥ ρ_P
  set u : Fin p → ℝ := Q_PP_inv.mulVec ρ_P
  set w : Fin c → ℝ := Q_CP.mulVec u
  have hu_dot : ∀ z : Fin c → ℝ,
      dotProduct ρ_P ((Q_PP_inv * Q_PC).mulVec z) = dotProduct w z := by
    intro z
    rw [← Matrix.mulVec_mulVec]
    have : dotProduct ρ_P (Q_PP_inv.mulVec (Q_PC.mulVec z)) =
        dotProduct (Q_PP_invᵀ.mulVec ρ_P) (Q_PC.mulVec z) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [this, hPP_sym]
    change dotProduct u (Q_CPᵀ.mulVec z) = dotProduct (Q_CP.mulVec u) z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      dotProduct_comm]
  -- Expand B11 *ᵥ ρ_P, B12 *ᵥ ρ_C, B21 *ᵥ ρ_P, B22 *ᵥ ρ_C
  have hB11 : B11.mulVec ρ_P =
      u + (Q_PP_inv * Q_PC).mulVec (Sigma_inv.mulVec w) := by
    dsimp [B11]
    rw [Matrix.add_mulVec]
    congr 1
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    rfl
  have hB12 : B12.mulVec ρ_C = -((Q_PP_inv * Q_PC).mulVec (Sigma_inv.mulVec ρ_C)) := by
    dsimp [B12]
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  have hB21 : B21.mulVec ρ_P = -(Sigma_inv.mulVec w) := by
    dsimp [B21]
    rw [Matrix.neg_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hdot, hB11, hB12, hB21]
  dsimp [B22]
  simp only [dotProduct_add, dotProduct_neg, add_assoc]
  rw [hu_dot (Sigma_inv.mulVec w), hu_dot (Sigma_inv.mulVec ρ_C)]
  have hδ : dotProduct δ (Sigma_inv.mulVec δ) =
      dotProduct ρ_C (Sigma_inv.mulVec ρ_C) - dotProduct ρ_C (Sigma_inv.mulVec w) -
      dotProduct w (Sigma_inv.mulVec ρ_C) + dotProduct w (Sigma_inv.mulVec w) := by
    dsimp [δ]
    change dotProduct (ρ_C - w) (Sigma_inv.mulVec (ρ_C - w)) = _
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  rw [hδ]
  ring

/-- **Nonnegativity of the Composite Schur Reduction (`Δ_Schur(C | P) >= 0`) & Prime Baseline Bound:**
Whenever `Σ_N⁻¹` is positive semidefinite, subtracting the Composite Schur reduction
never increases the squared approximation distance: `d_N^2 ≤ d_{N,Prime}^2`. -/
theorem schur_distance_le_prime_baseline {p c : ℕ}
    (Q_CP : Matrix (Fin c) (Fin p) ℝ)
    (Q_PP_inv : Matrix (Fin p) (Fin p) ℝ)
    (Sigma_inv : Matrix (Fin c) (Fin c) ℝ)
    (hPP_sym : Q_PP_invᵀ = Q_PP_inv)
    (hS_psd : ∀ x : Fin c → ℝ, 0 ≤ dotProduct x (Sigma_inv.mulVec x))
    (ρ_P : Fin p → ℝ) (ρ_C : Fin c → ℝ) :
    let Q_PC := Q_CPᵀ
    let B11 := Q_PP_inv + Q_PP_inv * Q_PC * Sigma_inv * Q_CP * Q_PP_inv
    let B12 := -(Q_PP_inv * Q_PC * Sigma_inv)
    let B21 := -(Sigma_inv * Q_CP * Q_PP_inv)
    let Q_inv := fromBlocks B11 B12 B21 Sigma_inv
    let ρ : Fin p ⊕ Fin c → ℝ := Sum.elim ρ_P ρ_C
    let δ : Fin c → ℝ := ρ_C - Q_CP.mulVec (Q_PP_inv.mulVec ρ_P)
    0 ≤ dotProduct δ (Sigma_inv.mulVec δ) ∧
    1 - dotProduct ρ (Q_inv.mulVec ρ) ≤ 1 - dotProduct ρ_P (Q_PP_inv.mulVec ρ_P) := by
  intro Q_PC B11 B12 B21 Q_inv ρ δ
  have hnonneg : 0 ≤ dotProduct δ (Sigma_inv.mulVec δ) := hS_psd δ
  have hsplit :=
    block_banachiewicz_schur_distance_split Q_CP Q_PP_inv Sigma_inv hPP_sym ρ_P ρ_C
  refine ⟨hnonneg, ?_⟩
  linarith

end RiemannBlueprint.PrimorialSchurDistanceDecay
