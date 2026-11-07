/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.StandingAssumptions
public import HigherDyson3.Characterization.SolutionPeriodization
public import HigherDyson3.Characterization.PoleCharacterization
public import HigherDyson3.Characterization.EigenResidue
public import HigherDyson3.Characterization.Backward

/-!
# The recurrence characterizes the Dyson seed

The introduction's summary [AOS, Theorem 1.4] of [AOS, Theorem 7.1]: for `m ≥ 2`,
`x = e(α)` a root of unity and `q = e(τ)`, (i) `X^{(m)}(x;q)/G_d(x;q)` is the unique solution of
the recurrence tending to `1`; (ii) the seed of every solution has a meromorphic continuation, its
bilateral periodization converges and satisfies the twisted law, and outside a discrete
exceptional set disjoint from `0 < |q| ≤ 1/2` its poles lie in `𝒟_x` if and only if the solution
is a multiple of `X^{(m)}(x;q)`, while non-Dyson solutions can have a single orbit of simple poles;
(iii) at `x = 1` the backward polynomials `P_J ∈ ℤ[q]` satisfy `R_m(ζ_d;q) ≡ P_J (mod q^{J+1})`.
-/

public section

open Complex Finset Filter Topology PowerSeries
open scoped ENNReal NNReal

namespace HigherDyson3

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

end HigherDyson3
