/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.PartialFractions
public import HigherDyson3.Recurrence.FiniteRecurrence
public import HigherDyson3.Recurrence.FiniteFunctionalEquation
public import HigherDyson3.ThetaCoeff.ThetaLeading

/-!
# The first new case: `m = 2`, level `5`

The explicit forms of the finite recurrence, the defect polynomial, the boundary values and the
partial-fraction coefficients for `m = 2`, `d = 5` [AOS, §8].
-/

public section

namespace HigherDyson3

open Polynomial Finset

/-- **The defect polynomial at `m = 2`, `x = 1`** [AOS, §8]:
`R_{5,1}(u;q) = (q^{-1}u² - u³ - u² - u - 1) X_0 - (u² + u) X_1 - (u³ + u²) X_2 - u³ X_3`. -/
theorem defectPoly_two_one (q : ℂ) :
    defectPoly 2 1 q =
      C (XSeries 2 1 0 q) * (C q⁻¹ * X ^ 2 - X ^ 3 - X ^ 2 - X - 1) -
        C (XSeries 2 1 1 q) * (X ^ 2 + X) - C (XSeries 2 1 2 q) * (X ^ 3 + X ^ 2) -
        C (XSeries 2 1 3 q) * X ^ 3 := by
  simp only [defectPoly, show 2 * 2 + 1 - 3 = 2 by rfl, show 2 * 2 + 1 - 2 = 3 by rfl,
    show 2 * 2 + 1 - 1 = 4 by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Finset.sum_Icc_succ_top, Finset.Icc_self, C_mul]
  ring

/-- **The defect polynomial at `m = 2`** [AOS, §8]:
`R_{5,x}(u;q) = (q^{-1}x^{-2}u² - u³ - u² - u - 1) X_0 + (x^{-1}u³ - xu³ - xu² - xu) X_1
  - x²(u³ + u²) X_2 - x³u³ X_3`. -/
theorem defectPoly_two (x q : ℂ) :
    defectPoly 2 x q =
      C (XSeries 2 x 0 q) * (C (q⁻¹ * (x ^ 2)⁻¹) * X ^ 2 - X ^ 3 - X ^ 2 - X - 1) +
        C (XSeries 2 x 1 q) * (C x⁻¹ * X ^ 3 - C x * X ^ 3 - C x * X ^ 2 - C x * X) -
        C (x ^ 2 * XSeries 2 x 2 q) * (X ^ 3 + X ^ 2) - C (x ^ 3 * XSeries 2 x 3 q) * X ^ 3 := by
  simp only [defectPoly, show 2 * 2 + 1 - 3 = 2 by rfl, show 2 * 2 + 1 - 2 = 3 by rfl,
    show 2 * 2 + 1 - 1 = 4 by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Finset.sum_Icc_succ_top, Finset.Icc_self, C_mul]
  ring

/-- **The recurrence at `m = 2`, `x = 1`** [AOS, §8]:
`X_{j-2} + X_{j-1} + X_j + X_{j+1} + X_{j+2} - q^{j-1} X_j = 5 G_5(1;q)`. -/
theorem recurrence_two_one {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (j : ℤ) :
    XSeries 2 1 (j - 2) q + XSeries 2 1 (j - 1) q + XSeries 2 1 j q + XSeries 2 1 (j + 1) q +
        XSeries 2 1 (j + 2) q - q ^ (j - 1) * XSeries 2 1 j q = 5 * GProduct 2 1 q := by
  have h := cyclotomic_XSeries_recurrence (le_refl 2) 1 hq0 hq1 j
  have hC : Cx 2 1 = 5 := by norm_num [Cx, cyclotomicSum, Finset.sum_range_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, one_mul, hC] at h
  rw [← h]
  push_cast
  ring_nf

/-- **The recurrence at the nontrivial fifth roots of unity** [AOS, §8]: for `x^5 = 1`,
`x ≠ 1`, `X_{j-2} + x X_{j-1} + x² X_j + x³ X_{j+1} + x⁴ X_{j+2} - q^{j-1} X_j = 0`. -/
theorem recurrence_two_of_pow_five {x q : ℂ} (hx : x ≠ 1) (hx5 : x ^ 5 = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    XSeries 2 x (j - 2) q + x * XSeries 2 x (j - 1) q + x ^ 2 * XSeries 2 x j q +
        x ^ 3 * XSeries 2 x (j + 1) q + x ^ 4 * XSeries 2 x (j + 2) q -
        q ^ (j - 1) * XSeries 2 x j q = 0 := by
  have h := cyclotomic_XSeries_recurrence (le_refl 2) x hq0 hq1 j
  have hC : Cx 2 x = 0 := Cx_eq_zero_of_pow_eq_one (le_refl 2) hx hx5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hC, zero_mul] at h
  rw [← h]
  push_cast
  ring_nf

/-- **The boundary values at the nontrivial fifth roots of unity** [AOS, §8]: for `x^5 = 1`,
`x ≠ 1`, `X_{-1} = -x X_0 + (1 - x²) X_1 - x³ X_2 - x⁴ X_3` and
`X_{-2} = q^{-1} X_0 - x X_1 + X_3`. -/
theorem boundary_two_of_pow_five {x q : ℂ} (hx : x ≠ 1) (hx5 : x ^ 5 = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) :
    XSeries 2 x (-1) q = -x * XSeries 2 x 0 q + (1 - x ^ 2) * XSeries 2 x 1 q -
        x ^ 3 * XSeries 2 x 2 q - x ^ 4 * XSeries 2 x 3 q ∧
      XSeries 2 x (-2) q = q⁻¹ * XSeries 2 x 0 q - x * XSeries 2 x 1 q + XSeries 2 x 3 q := by
  have h1 := recurrence_two_of_pow_five hx hx5 hq0 hq1 1
  have h0 := recurrence_two_of_pow_five hx hx5 hq0 hq1 0
  norm_num at h1 h0
  have hm1 : XSeries 2 x (-1) q = -x * XSeries 2 x 0 q + (1 - x ^ 2) * XSeries 2 x 1 q -
      x ^ 3 * XSeries 2 x 2 q - x ^ 4 * XSeries 2 x 3 q := by
    linear_combination h1
  refine ⟨hm1, ?_⟩
  rw [hm1] at h0
  linear_combination h0 + XSeries 2 x 3 q * hx5

/-- **The functional equation at the nontrivial fifth roots of unity** [AOS, §8]: for `x^5 = 1`,
`x ≠ 1`, `𝒢_{5,x}(qu;q) = x² q (u⁵ - 1)/(u²(u - 1)) 𝒢_{5,x}(u;q) + q u^{-2} R_{5,x}(u;q)`. -/
theorem seed_mul_two_of_pow_five {x q u : ℂ} (hx : x ≠ 1) (hx5 : x ^ 5 = 1) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) (hu : u ≠ 0) (hu1 : u ≠ 1) (hxu : ∀ k : ℕ, x * u * q ^ k ≠ 1) :
    seed 2 x (q * u) q =
      x ^ 2 * q * ((u ^ 5 - 1) / (u ^ 2 * (u - 1))) * seed 2 x u q +
        q * u ^ (-2 : ℤ) * (defectPoly 2 x q).eval u := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx5
  have h := seed_mul_eq_defectPoly (le_refl 2) hx0 hq0 hq1 hu hxu
  have hC : Cx 2 x = 0 := Cx_eq_zero_of_pow_eq_one (le_refl 2) hx hx5
  have hsum : ∑ r ∈ range (2 * 2 + 1), u ^ (2 - (r : ℤ)) = (u ^ 5 - 1) / (u ^ 2 * (u - 1)) := by
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    field_simp
    ring
  rw [h, hsum, hC]
  norm_num

/-- **The partial-fraction data at the nontrivial fifth roots of unity** [AOS, §8]: for `x^5 = 1`,
`x ≠ 1`, `Q_{5,x} = (1 - u) R_{5,x}`, `D_{r,x} = (ω^r/5)(1 - ω^{-r}) R_{5,x}(ω^{-r})`, and
`D_{0,x} = 0`. -/
theorem partialFraction_two_of_pow_five {x : ℂ} (hx : x ≠ 1) (hx5 : x ^ 5 = 1) (q : ℂ) :
    rationalDefect 2 x q = (1 - X) * defectPoly 2 x q ∧
      (∀ r : ℕ, pfD 2 x q r = omega 2 ^ r / 5 * (1 - (omega 2 ^ r)⁻¹) *
        (defectPoly 2 x q).eval (omega 2 ^ r)⁻¹) ∧ pfD 2 x q 0 = 0 := by
  have hQ : rationalDefect 2 x q = (1 - X) * defectPoly 2 x q := by
    exact rationalDefect_of_pow_eq_one hx5 hx q
  have hε : defectEps 2 x = 0 := defectEps_eq_zero_of_pow_eq_one hx5
  have hD : ∀ r : ℕ, pfD 2 x q r = omega 2 ^ r / 5 * (1 - (omega 2 ^ r)⁻¹) *
      (defectPoly 2 x q).eval (omega 2 ^ r)⁻¹ := by
    intro r
    rw [pfD_def, hQ, hε]
    simp only [eval_mul, eval_sub, eval_one, eval_X, pow_zero, mul_one]
    norm_num
    ring
  refine ⟨hQ, hD, ?_⟩
  rw [hD 0]
  simp

/-- **The residue function at the nontrivial fifth roots of unity** [AOS, §8]: for `x = e(α)` with
`x^5 = 1`, `ρ_{2,x}(τ) = x^{-2} ∑_{k ≥ 0} x^k q^{3k²} g_{k,x}(q)`. -/
theorem rho_two_of_pow_five {α : ℚ} (hx5 : e α ^ 5 = 1) (τ : ℂ) :
    rho 2 α τ = (e α ^ 2)⁻¹ * ∑' k : ℕ, e α ^ k * e τ ^ (3 * k ^ 2) * gTail 2 (e α) k (e τ) := by
  rw [rho]
  congr 1
  refine tsum_congr fun k => ?_
  have : e (α : ℂ) ^ (2 * (2 + 1) * k) = e α ^ k := by
    rw [show 2 * (2 + 1) * k = 5 * k + k by ring, pow_add, pow_mul, hx5, one_pow, one_mul]
  rw [this]

/-- **The twisted theta coefficients at the nontrivial fifth roots of unity** [AOS, §8]: for
`x = e(α)` with `x^5 = 1`,
`C_{2,ℓ,x}(τ) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{k-s} q^{3k² - 2s² + ℓs}`. -/
theorem coeffC_two_of_pow_five {α : ℚ} (hx5 : e α ^ 5 = 1) (ℓ : ℕ) (τ : ℂ) :
    coeffC 2 ℓ α τ = e α ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, gTail 2 (e α) k (e τ) *
      ∑ s ∈ Icc 1 k, e α ^ ((k : ℤ) - s) * e τ ^ (3 * (k : ℤ) ^ 2 - 2 * (s : ℤ) ^ 2 + ℓ * s) := by
  rw [coeffC]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have hx0 : e (α : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h5 : e (α : ℂ) ^ (5 : ℤ) = 1 := by rw [zpow_ofNat]; exact hx5
  have : e (α : ℂ) ^ (2 * ((2 : ℕ) + 1 : ℤ) * ((k : ℤ) - s)) = e α ^ ((k : ℤ) - s) := by
    rw [show 2 * ((2 : ℕ) + 1 : ℤ) * ((k : ℤ) - s) = 5 * ((k : ℤ) - s) + ((k : ℤ) - s) by
      push_cast; ring, zpow_add₀ hx0, zpow_mul, h5, one_zpow, one_mul]
  push_cast at this ⊢
  rw [this]

/-- **Leading terms of the theta coefficients at level `5`** [AOS, §8]: for `m = 2`,
`x = e(α)` with `α ∈ ℚ ∩ [0,1)` (this covers `x = 1` and `x = ω^a`, `α = a/5`) and `0 ≤ ℓ ≤ 3`,
`h_{2,ℓ,x}(τ) = e(ℓα/2) x^{ℓ-2} q^{1+ℓ-ℓ²/8} (1 + O(q²))`; for `x = 1` the exponents
`1 + ℓ - ℓ²/8` are `1, 15/8, 5/2, 23/8`. -/
theorem thetaCoeffH_two_leading {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 4) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖thetaCoeffH 2 ℓ α τ -
          e (ℓ * α / 2) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / 8) * τ)‖ ≤
        C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / 8 + 2) * τ)‖ := by
  have h := exists_norm_thetaCoeffH_sub_le (le_refl 2) hα0 hα1 (ℓ := ℓ) (by omega)
  obtain ⟨C, T, hC, hT, hb⟩ := h
  refine ⟨C, T, hC, hT, fun τ hτ hTτ => ?_⟩
  have := hb τ hτ hTτ
  norm_num at this
  exact this

end HigherDyson3
