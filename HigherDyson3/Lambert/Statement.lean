/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.Residue
public import HigherDyson3.Lambert.TwistedLaw

/-!
# Lemma 7.4: the periodization of a Lambert-type seed

The statement of [AOS, Lemma 7.4] in one place, assembled from
`HigherDyson3.Lambert.Convergence`, `HigherDyson3.Lambert.SimplePoles`,
`HigherDyson3.Lambert.Residue` and `HigherDyson3.Lambert.TwistedLaw`.
-/

public section

open Complex Filter Topology
open scoped ENNReal NNReal

namespace HigherDyson3

/-- **The periodization of a Lambert-type seed** [AOS, Lemma 7.4]. Let `m ≥ 2`, `x = e(α)`,
`c = e(β)` with `β ∈ ℚ ∩ [0,1)`, and let `b_i` be holomorphic on `|q| < 1` with
`|b_i(q)| ≤ B_Q |q|^{i²}` for `|q| ≤ Q`, `0 < Q < 1`. Put `Φ(u) = x⁻² ∑_i b_i / (1 - c q^i u)`,
`ℰ_Φ(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} Φ(q^n u)` and
`ρ_Φ(τ) = x⁻² ∑_i x^{2i} c^{2mi} q^{mi²} b_i`.
(a) `ℰ_Φ` converges normally on compact subsets of `(ℍ × ℂ) \ 𝒟_c`, is holomorphic there, has at
most simple poles along each component `L_{a,k}` of `𝒟_c`, and satisfies the twisted law.
(b) The series of `ρ_Φ` converges normally on `|q| ≤ Q < 1`, `ρ_Φ` is holomorphic on `ℍ`, and
the residue of `ℰ_Φ(τ, ·)` at `-β + aτ + k` is `-ρ_Φ(τ)/(2πi) x^{2a} c^{2ma} q^{-ma²}`.
(c) For fixed `τ`, the orbit points are simple poles if `ρ_Φ(τ) ≠ 0` and removable
singularities if `ρ_Φ(τ) = 0`. -/
theorem lambertSeed_periodization {m : ℕ} (hm : 2 ≤ m) (α : ℚ) {β : ℚ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {b : ℕ → ℂ → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2)) :
    -- (a)
    ((∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor β →
      ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (e β) b (e p.1 ^ n * e p.2) (e p.1)‖₊ :
          ℝ≥0∞) < ∞) ∧
      (IsOpen (halfPlaneProd \ divisor β) ∧
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ => seedPeriodization m α (lambertSeed (e α) (e β) b) p.1 p.2)
          (halfPlaneProd \ divisor β)) ∧
      (∀ a k : ℤ, ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd β a k) ∧
        ∀ p ∈ halfPlaneProd \ divisor β, N p = (p.2 + β - a * p.1 - k) *
          seedPeriodization m α (lambertSeed (e α) (e β) b) p.1 p.2) ∧
      (∀ (τ w : ℂ) (a k : ℤ),
        seedPeriodization m α (lambertSeed (e α) (e β) b) τ (w + a * τ + k) =
          e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
            seedPeriodization m α (lambertSeed (e α) (e β) b) τ w)) ∧
    -- (b)
    ((∀ Q : ℝ, 0 ≤ Q → Q < 1 → ∃ M : ℕ → ℝ, Summable M ∧ ∀ i : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q →
        ‖e α ^ (2 * i) * e β ^ (2 * m * i) * q ^ (m * i ^ 2) * b i q‖ ≤ M i) ∧
      DifferentiableOn ℂ (lambertResidue m α (e β) b) upperHalfPlaneSet ∧
      ∀ τ ∈ upperHalfPlaneSet, ∀ a k : ℤ,
        Tendsto (fun ε : ℂ => ε * seedPeriodization m α (lambertSeed (e α) (e β) b) τ
            (-(β : ℂ) + a * τ + k + ε)) (𝓝[≠] 0)
          (𝓝 (-(lambertResidue m α (e β) b τ / (2 * Real.pi * Complex.I)) * e α ^ (2 * a) *
            e β ^ (2 * (m : ℤ) * a) * e τ ^ (-(m : ℤ) * a ^ 2)))) ∧
    -- (c)
    (∀ τ ∈ upperHalfPlaneSet, lambertResidue m α (e β) b τ ≠ 0 → ∀ a k : ℤ,
        ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun ε : ℂ => ε * seedPeriodization m α
          (lambertSeed (e α) (e β) b) τ (-(β : ℂ) + a * τ + k + ε)) (𝓝[≠] 0) (𝓝 L)) ∧
      ∀ τ ∈ upperHalfPlaneSet, lambertResidue m α (e β) b τ = 0 → ∀ a k : ℤ,
        ∃ L : ℂ, Tendsto (fun w => seedPeriodization m α (lambertSeed (e α) (e β) b) τ w)
          (𝓝[≠] (-(β : ℂ) + a * τ + k)) (𝓝 L) := by
  have hm1 : 1 ≤ m := by omega
  exact ⟨⟨fun S hS hSD => seedPeriodization_lambertSeed_normal hm1 α hβ0 hβ1 hB S hS hSD,
      differentiableOn_seedPeriodization_lambertSeed hm1 α hβ0 hβ1 hb hB,
      seedPeriodization_lambertSeed_simple_poles hm1 α hβ0 hβ1 hb hB,
      fun τ w a k => seedPeriodization_twisted_law m α _ τ w a k⟩,
    ⟨fun Q hQ0 hQ1 => exists_majorant_lambertResidue_term m α (norm_e_ratCast β) hB hQ0 hQ1,
      differentiableOn_lambertResidue m α β hb hB,
      fun τ hτ a k => seedPeriodization_lambertSeed_residue hm1 α hβ0 hβ1 hb hB hτ a k⟩,
    fun τ hτ hρ a k => seedPeriodization_lambertSeed_pole_genuine hm1 α hβ0 hβ1 hb hB hτ hρ a k,
    fun τ hτ hρ a k =>
      seedPeriodization_lambertSeed_pole_removable hm1 α hβ0 hβ1 hb hB hτ hρ a k⟩

/-- **Local splitting along a divisor component** [AOS, proof of Lemma 7.4(a),(b)]. Under the
hypotheses of [AOS, Lemma 7.4], for every `a ∈ ℤ`: off `𝒟_c`,
`ℰ_Φ = R_a + N_a / (1 - c u q^{-a})`, where the regular part `R_a` (the double summands with
`n + i ≠ -a`) is holomorphic on the neighbourhood `Ω_{a,k}` of each component `L_{a,k}`, the
singular numerator `N_a = x⁻² ∑_i x^{2(a+i)} q^{m(a+i)²} u^{-2m(a+i)} b_i` is holomorphic on
`ℍ × ℂ`, and `N_a(τ, -β + aτ + k) = x^{2a} c^{2ma} q^{-ma²} ρ_Φ(τ)`. -/
theorem lambertSeed_local_splitting {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {b : ℕ → ℂ → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a : ℤ) :
    (∀ p ∈ halfPlaneProd \ divisor β,
      seedPeriodization m α (lambertSeed (e α) (e β) b) p.1 p.2 =
        lambertRegularPart m α β b a p.1 p.2 +
          lambertSingularNumerator m α b a p.1 p.2 / (1 - e β * e p.2 * e p.1 ^ (-a))) ∧
    (∀ k : ℤ, DifferentiableOn ℂ (fun p : ℂ × ℂ => lambertRegularPart m α β b a p.1 p.2)
      (divisorNbhd β a k)) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => lambertSingularNumerator m α b a p.1 p.2)
      halfPlaneProd ∧
    ∀ (τ : ℂ) (k : ℤ), lambertSingularNumerator m α b a τ (-(β : ℂ) + a * τ + k) =
      e α ^ (2 * a) * e β ^ (2 * (m : ℤ) * a) * e τ ^ (-(m : ℤ) * a ^ 2) *
        lambertResidue m α (e β) b τ :=
  ⟨fun _ hp => seedPeriodization_lambertSeed_eq_regular_add hm α hβ0 hβ1 hB a hp,
    differentiableOn_lambertRegularPart hm α hβ0 hβ1 hb hB a,
    differentiableOn_lambertSingularNumerator α hb hB a,
    fun τ k => lambertSingularNumerator_eq_lambertResidue m α β b τ a k⟩

end HigherDyson3
