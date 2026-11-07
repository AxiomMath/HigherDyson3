/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3

/-! # Satisfying the formal challenge -/

@[expose] public section

open Complex Finset

namespace HigherDyson3.Challenge

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

/-! ## Higher Dyson ranks -/

/-- **`thm_combinatorial_gen_series` — the generating function of the full rank.** For `m ≥ 1`,
`[z^r] [q^N] R_m(z;q) = N_m(r, N)`. -/
theorem thm_combinatorial_gen_series (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (r : ℤ) :
    zCoeff r (qCoeff N (RSeries m)) = (rankCount m r N : ℤ) :=
  RSeries_zCoeff_qCoeff m hm N r

/-- **`thm_full_rank_symmetry` — symmetry of the full rank.** For `m ≥ 1`,
`N_m(r, N) = N_m(-r, N)`. -/
theorem thm_full_rank_symmetry (m : ℕ) (_hm : 1 ≤ m) (r : ℤ) (N : ℕ) :
    rankCount m r N = rankCount m (-r) N :=
  rankCount_neg m _hm r N

/-! ## The finite recurrence and the defect polynomial

Throughout, `m ≥ 2` and `d = 2m + 1`. -/

/-- **`thm_finite_recurrence` — the finite recurrence.** For `0 < ‖q‖ < 1` and `j ∈ ℤ`,
`∑_{r=0}^{d-1} x^r X_{j+r-2}(x;q) - q^{j-1} X_j(x;q) = C_x G_d(x;q)`. -/
theorem thm_finite_recurrence {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    ∑ r ∈ range (2 * m + 1), x ^ r * XSeries m x (j + r - 2) q - q ^ (j - 1) * XSeries m x j q =
      Cx m x * GProduct m x q :=
  cyclotomic_XSeries_recurrence hm x hq0 hq1 j

/-- **`thm_finite_Cx_vanishes` — `C_x` vanishes at nontrivial `d`-th roots of unity.** -/
theorem thm_finite_Cx_vanishes {m : ℕ} (_hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 1)
    (hxd : x ^ (2 * m + 1) = 1) : Cx m x = 0 :=
  Cx_eq_zero_of_pow_eq_one _hm hx hxd

/-- **`thm_finite_functional_equation` — the functional equation of the seed.** For `x ≠ 0`,
`0 < ‖q‖ < 1` and `u ≠ 0` with `x u q^k ≠ 1` for all `k`,
`𝒢_{d,x}(qu;q) = x² q (∑_{r<d} u^{2-r}) 𝒢_{d,x}(u;q) + q u^{3-d} R_{d,x}(u;q)
  - C_x q u²/(1 - xu) G_d(x;q)`. -/
theorem thm_finite_functional_equation {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hu : u ≠ 0) (hxu : ∀ k : ℕ, x * u * q ^ k ≠ 1) :
    seed m x (q * u) q =
      x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
        q * u ^ (3 - (2 * m + 1 : ℤ)) * (defectPoly m x q).eval u -
        Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q :=
  seed_mul_eq_defectPoly hm hx hq0 hq1 hu hxu

/-- **`thm_finite_defect_unique` — uniqueness of the defect polynomial.** A polynomial `R'` of
degree at most `d - 2` satisfying the functional equation on a nonempty open set `V` of
admissible `u` is `R_{d,x}(U;q)`. -/
theorem thm_finite_defect_unique {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {R' : Polynomial ℂ}
    (_hdeg : R'.degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ)) {V : Set ℂ} (hVo : IsOpen V)
    (hVne : V.Nonempty)
    (hV : ∀ u ∈ V, u ≠ 0 ∧ (∀ k : ℕ, x * u * q ^ k ≠ 1) ∧
      seed m x (q * u) q =
        x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
          q * u ^ (3 - (2 * m + 1 : ℤ)) * R'.eval u -
          Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q) :
    R' = defectPoly m x q :=
  eq_defectPoly_of_functionalEquation hm hx hq0 hq1 _hdeg hVo hVne hV

/-- **`thm_finite_defect_degree` — the degree of the defect polynomial.** `R_{d,x}(U;q)` has
degree at most `d - 2`. -/
theorem thm_finite_defect_degree {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (_hx : x ≠ 0)
    (_hq0 : 0 < ‖q‖) (_hq1 : ‖q‖ < 1) :
    (defectPoly m x q).degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) :=
  defectPoly_degree_le hm _hx _hq0 _hq1

/-- **`thm_finite_defect_constant_term` — the constant term of the defect polynomial.**
`[U^0] R_{d,x}(U;q) = -X₀(x;q)`. -/
theorem thm_finite_defect_constant_term {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (defectPoly m x q).coeff 0 = -XSeries m x 0 q :=
  defectPoly_coeff_zero hm hx hq0 hq1

/-- **`thm_finite_defect_q_pole` — at most a simple pole at `q = 0`.** For `a ≤ d - 2`,
`q [U^a] R_{d,x}(U;q)` extends holomorphically to the open unit disk. -/
theorem thm_finite_defect_q_pole {m : ℕ} (hm : 2 ≤ m) {x : ℂ}
    (hx : x ≠ 0) {a : ℕ} (ha : a ≤ 2 * m + 1 - 2) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * (defectPoly m x q).coeff a :=
  exists_differentiableOn_eq_mul_defectPoly_coeff hm hx ha

/-! ## The elliptic periodization

Throughout, `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, and `x = e(α)`. -/

/-- **`thm_elliptic_normal_convergence` — normal convergence of the periodization.** On every
compact `S ⊆ (ℍ × ℂ) \ 𝒟_x`, the series defining `ℰ_{m,x}` converges normally. -/
theorem thm_elliptic_normal_convergence {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ : ℝ≥0∞) < ∞ :=
  elliptic_normal_convergence hm α hα0 hα1 S hS hSD

/-- **`thm_elliptic_holomorphic_off` — holomorphy off the divisor.** `(ℍ × ℂ) \ 𝒟_x` is open
and `ℰ_{m,x}` is holomorphic on it. -/
theorem thm_elliptic_holomorphic_off {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    IsOpen (halfPlaneProd \ divisor α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => periodization m α p.1 p.2)
        (halfPlaneProd \ divisor α) :=
  periodization_holomorphic_off hm α hα0 hα1

/-- **`thm_elliptic_twisted_law` — the twisted elliptic law.**
`ℰ_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w)`, `q = e(τ)`, `u = e(w)`. -/
theorem thm_elliptic_twisted_law {m : ℕ} (_hm : 2 ≤ m) {α : ℚ} (_hα0 : 0 ≤ α)
    (_hα1 : α < 1) {τ w : ℂ} (_hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    periodization m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        periodization m α τ w :=
  periodization_twisted_law _hm _hα0 _hα1 _hτw a b

/-- **`thm_elliptic_rho_holomorphic` — holomorphy of `ρ_{m,x}`** on the upper half-plane. -/
theorem thm_elliptic_rho_holomorphic {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    DifferentiableOn ℂ (rho m α) upperHalfPlaneSet :=
  rho_holomorphic hm α

/-- **`thm_elliptic_rho_leading` — the leading term of `ρ_{m,x}`.**
`‖ρ_{m,x}(τ) - x⁻²‖ ≤ C ‖e(τ)‖` for `Im τ ≥ T`. -/
theorem thm_elliptic_rho_leading {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ : ℂ, τ ∈ upperHalfPlaneSet → T ≤ τ.im →
      ‖rho m α τ - (e α ^ 2)⁻¹‖ ≤ C * ‖e τ‖ :=
  rho_leading hm α

/-- **`thm_elliptic_simple_poles` — at most simple poles.** `(w + α - aτ - b) ℰ_{m,x}(τ, w)`
extends holomorphically to `Ω_{a,b}`. -/
theorem thm_elliptic_simple_poles (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (a b : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
      ∀ p ∈ halfPlaneProd \ divisor α,
        N p = (p.2 + α - a * p.1 - b) * periodization m α p.1 p.2 :=
  periodization_simple_poles m hm α hα0 hα1 a b

/-- **`thm_elliptic_residue` — the residues.** With `w_{a,b} = -α + aτ + b`,
`ε ℰ_{m,x}(τ, w_{a,b} + ε) → -(ρ_{m,x}(τ)/2πi) x^{2(m+1)a} q^{-ma²}` as `ε → 0`. -/
theorem thm_elliptic_residue {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (a b : ℤ) :
    Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
      (𝓝 (-(rho m α τ / (2 * Real.pi * Complex.I)) * e α ^ (2 * ((m : ℤ) + 1) * a) *
        e τ ^ (-(m : ℤ) * a ^ 2))) :=
  periodization_residue hm hα0 hα1 hτ a b

/-- **`thm_elliptic_pole_genuine` — the poles are genuine where `ρ_{m,x}(τ) ≠ 0`.** -/
theorem thm_elliptic_pole_genuine {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ ≠ 0) (a b : ℤ) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
        (𝓝 L) :=
  periodization_pole_genuine hm hα0 hα1 hτ hρ a b

/-- **`thm_elliptic_pole_removable` — the poles are removable where `ρ_{m,x}(τ) = 0`.** -/
theorem thm_elliptic_pole_removable {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ = 0) (a b : ℤ) :
    ∃ L : ℂ, Tendsto (fun w => periodization m α τ w)
      (𝓝[≠] (-(α : ℂ) + a * τ + b)) (𝓝 L) :=
  periodization_pole_removable hm hα0 hα1 hτ hρ a b

/-- **`thm_elliptic_ne_zero` — the periodization is not identically zero** off `𝒟_x`. -/
theorem thm_elliptic_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, periodization m α p.1 p.2 ≠ 0 :=
  periodization_ne_zero hm hα0 hα1

/-- **`thm_elliptic_untwisted_law` — the untwisted elliptic law.**
`ℰ_{m,x}(τ, w + α/m + aτ + b) = q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w + α/m)`. -/
theorem thm_elliptic_untwisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    periodization m α τ (w + (α : ℂ) / m + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        periodization m α τ (w + (α : ℂ) / m) :=
  periodization_untwisted_law hm hα0 hα1 hτw a b

/-! ## The finite part and its theta decomposition

Throughout, `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, and `x = e(α)`. -/

/-- **`thm_theta_holomorphic` — the finite part is holomorphic.** `ℰ^{fin}_{m,x}` agrees off
`𝒟_x` with a function holomorphic on `ℍ × ℂ`. -/
theorem thm_theta_holomorphic {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ F : ℂ × ℂ → ℂ, DifferentiableOn ℂ F halfPlaneProd ∧
      ∀ p ∈ halfPlaneProd \ divisor α, F p = finitePart m α p.1 p.2 :=
  exists_differentiableOn_eqOn_finitePart hm hα0 hα1

/-- **`thm_theta_twisted_law` — the twisted elliptic law of the finite part.** -/
theorem thm_theta_twisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ w :=
  finitePart_twisted_law hm hα0 hα1 hτw a b

/-- **`thm_theta_untwisted_law` — the untwisted elliptic law of the translated finite part.** -/
theorem thm_theta_untwisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + (α : ℂ) / m + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ (w + (α : ℂ) / m) :=
  finitePart_untwisted_law hm hα0 hα1 hτw a b

/-- **`thm_theta_expansion` — the theta expansion.**
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ, w)` off `𝒟_x`. -/
theorem thm_theta_expansion {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {τ w : ℂ} (hτ : τ ∈ upperHalfPlaneSet)
    (hw : (τ, w + (α : ℂ) / m) ∉ divisor α) :
    finitePart m α τ (w + (α : ℂ) / m) =
      ∑ ℓ ∈ range (2 * m), thetaCoeffH m ℓ α τ * theta m ℓ τ w :=
  finitePart_add_div_eq_sum_theta hm hα0 hα1 hτ hw

/-- **`thm_theta_unique` — uniqueness of the theta coefficients.** Any coefficients `h'_ℓ`
giving the theta expansion are the `h_{m,ℓ,x}`. -/
theorem thm_theta_unique {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h' : ℕ → ℂ → ℂ)
    (hh' : ∀ τ ∈ upperHalfPlaneSet, ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α →
      finitePart m α τ (w + (α : ℂ) / m) = ∑ ℓ ∈ range (2 * m), h' ℓ τ * theta m ℓ τ w) :
    ∀ ℓ < 2 * m, ∀ τ ∈ upperHalfPlaneSet, h' ℓ τ = thetaCoeffH m ℓ α τ :=
  thetaCoeffH_unique hm hα0 hα1 h' hh'

/-- **`thm_theta_coeff_normal` — normal convergence of the series of `h_{m,ℓ,x}`** on every
compact `S ⊆ ℍ`, for `0 ≤ ℓ < 2m`. -/
theorem thm_theta_coeff_normal {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ℓ : ℕ} (hℓ : ℓ < 2 * m) (S : Set ℂ) (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∑' k : ℕ, ⨆ τ ∈ S, (‖e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) *
      e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
      (gTail m (e α) k (e τ) *
        ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))‖₊ : ℝ≥0∞) < ∞ :=
  thetaCoeff_normal hm hα0 hα1 hℓ S hS hSH

/-- **`thm_theta_coeff_holomorphic` — holomorphy of `h_{m,ℓ,x}`** on the upper half-plane,
for `0 ≤ ℓ < 2m`. -/
theorem thm_theta_coeff_holomorphic {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    DifferentiableOn ℂ (thetaCoeffH m ℓ α) upperHalfPlaneSet :=
  differentiableOn_thetaCoeffH hm hα0 hα1 hℓ

/-- **`thm_theta_leading` — the leading term of `h_{m,ℓ,x}`.** With `c_ℓ = 1 + ℓ - ℓ²/(4m)`,
`|h_{m,ℓ,x}(τ) - e(ℓα/m) x^{ℓ-2} e(c_ℓ τ)| ≤ C |e((c_ℓ + 2)τ)|` for `Im τ ≥ T`. -/
theorem thm_theta_leading {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖thetaCoeffH m ℓ α τ -
          e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)) * τ)‖ ≤
        C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m) + 2) * τ)‖ :=
  exists_norm_thetaCoeffH_sub_le hm hα0 hα1 hℓ

/-- **`thm_theta_coeff_ne_zero` — no theta coefficient vanishes identically** on `ℍ`. -/
theorem thm_theta_coeff_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ τ ∈ upperHalfPlaneSet, thetaCoeffH m ℓ α τ ≠ 0 :=
  exists_thetaCoeffH_ne_zero hm hα0 hα1 hℓ

/-- **`thm_theta_finite_ne_zero` — the finite part is not identically zero** off `𝒟_x`. -/
theorem thm_theta_finite_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, finitePart m α p.1 p.2 ≠ 0 :=
  exists_finitePart_ne_zero hm hα0 hα1

/-- **`thm_theta_positive` — positivity at `x = 1`.** For `0 ≤ ℓ < 2m` and real `t > 0`,
`h_{m,ℓ,1}(it)` is a positive real number. -/
theorem thm_theta_positive {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : ℓ < 2 * m) {t : ℝ}
    (ht : 0 < t) :
    0 < thetaCoeffH m ℓ 0 (I * t) :=
  thetaCoeffH_pos hm hℓ ht

/-! ## The recurrence characterizes the Dyson seed -/

section RecurrenceCharacterization

open PowerSeries

/-- **The recurrence characterizes the Dyson seed** [AOS, Theorem 1.4, Theorem 7.1]. -/
theorem recurrence_characterization {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -- (i) the unique solution tending to `1`
    (∀ τ : ℂ, 0 < τ.im →
      ((fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∈
          recurrenceFamily m (e α) (e τ) 1 ∧
        Tendsto (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) atTop (𝓝 1)) ∧
      ∀ (γ : ℂ) (Y : ℕ → ℂ), Y ∈ recurrenceFamily m (e α) (e τ) γ → Tendsto Y atTop (𝓝 1) →
        Y = (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∧
          (Cx m (e α) ≠ 0 → γ = 1)) ∧
    -- (ii) the seed: convergence and meromorphic continuation
    (∀ τ : ℂ, 0 < τ.im → ∀ Y ∈ recurrenceSolutions m (e α) (e τ),
      (∀ u : ℂ, ‖u‖ < 1 → Summable fun j : ℕ => Y j * (e α * u) ^ j) ∧
        ∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
    -- (ii) the periodization: convergence off the orbits, at most simple poles, twisted law
    (∀ τ ∈ upperHalfPlaneSet, ∀ Y ∈ recurrenceSolutions m (e α) (e τ), ∀ Φ : ℂ → ℂ,
      IsSeedContinuation m (e α) (e τ) Y Φ →
      (∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, (τ, w) ∉ solutionDivisor m α) →
        ∑' n : ℤ, ⨆ w ∈ K, (‖e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
          e w ^ (2 * (m : ℤ) * n) * Φ (e τ ^ n * e w)‖₊ : ℝ≥0∞) < ∞) ∧
      (IsOpen {w : ℂ | (τ, w) ∉ solutionDivisor m α} ∧
        DifferentiableOn ℂ (fun w => seedPeriodization m α (fun u _ => Φ u) τ w)
          {w : ℂ | (τ, w) ∉ solutionDivisor m α}) ∧
      (∀ w₀ : ℂ, ∃ N : ℂ → ℂ, AnalyticAt ℂ N w₀ ∧ ∀ᶠ w in 𝓝[≠] w₀,
        N w = (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w) ∧
      ∀ (w : ℂ) (a k : ℤ), seedPeriodization m α (fun u _ => Φ u) τ (w + a * τ + k) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          seedPeriodization m α (fun u _ => Φ u) τ w) ∧
    -- (ii) the exceptional set: discrete, depending only on `m`, disjoint from `0 < |q| ≤ 1/2`
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → ∀ᶠ y in 𝓝[≠] z, y ∉ exceptionalSet m) ∧
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ 1 / 2 → q ∉ exceptionalSet m) ∧
    -- (ii) the location of the poles
    (∀ τ ∈ upperHalfPlaneSet, e τ ∉ exceptionalSet m →
      (∀ Y : ℕ → ℂ, Y ∈ recurrenceSolutions m (e α) (e τ) → ∀ Φ : ℂ → ℂ,
        IsSeedContinuation m (e α) (e τ) Y Φ →
        ((∀ w₀ : ℂ, (τ, w₀) ∉ divisor α → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
          ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) ↔
          ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ))) ∧
      ∀ k ∈ Icc 1 (2 * m), omega m ^ k ≠ e α →
        ∃ Y : ℕ → ℂ, Y ∈ recurrenceFamily m (e α) (e τ) 0 ∧
          (¬ ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ)) ∧
          (∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
          ∀ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ → ∀ w₀ : ℂ,
            ((τ, w₀) ∈ divisor ((k : ℚ) / (2 * m + 1)) → ∃ L : ℂ, L ≠ 0 ∧
              Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
                (𝓝[≠] w₀) (𝓝 L)) ∧
            ((τ, w₀) ∉ divisor ((k : ℚ) / (2 * m + 1)) → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
              ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w)) ∧
    -- (iii) the backward polynomials at `x = 1`
    ∀ (ζ : ℂˣ), IsPrimitiveRoot (ζ : ℂ) (2 * m + 1) → ∀ J : ℕ,
      (X ^ (J + 1) ∣ map (zEval ζ) (RSeries m) -
        map (Int.castRingHom ℂ) (backwardPolynomial m J : PowerSeries ℤ)) ∧
      ∀ N ≤ J, ((backwardPolynomial m J).coeff N : ℂ) = coeff N (map (zEval ζ) (RSeries m)) :=
  ⟨fun _ hτ => dysonSequence_limit_characterization hm α hτ,
    fun _ hτ _ hY => solution_seed_continuation_e hm α hτ hY,
    fun _ hτ _ hY _ hΦ => solution_periodization hm hα0 hα1 hτ hY hΦ,
    (eigenSolution_residues hm α).2.2.2.2.1, (eigenSolution_residues hm α).2.2.2.2.2,
    fun _ hτ hq => solution_pole_characterization hm hα0 hα1 hτ hq,
    fun ζ hζ J => ⟨(backwardPolynomial_congruence m (by omega) ζ hζ J).1,
      (backwardPolynomial_congruence m (by omega) ζ hζ J).2.1⟩⟩

end RecurrenceCharacterization

end HigherDyson3.Challenge
