/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.Convergence
public import HigherDyson3.Lambert.TwistedLaw
public import HigherDyson3.Product.GBound
public import HigherDyson3.Product.GHolomorphic

/-!
# Periodizations of the Dyson seed of any index

For any index `M ≥ 1`, the bilateral periodization
`∑_{n ∈ ℤ} x^{-2n} q^{Mn²} u^{2Mn} 𝒢_{d,x}(q^n u; q)` of the fixed Dyson seed converges normally
off `𝒟_x`, is holomorphic there, and satisfies the twisted index-`M` elliptic law
[AOS, §6.3].
-/

public section

open Complex

namespace HigherDyson3

/-- The Dyson seed is the Lambert-type seed with `c = x` and `b_i = q^{i²} g_{i,x}(q)`. -/
theorem seed_eq_lambertSeed (m : ℕ) (x : ℂ) :
    seed m x = lambertSeed x x (fun i q => q ^ (i ^ 2) * gTail m x i q) := by
  funext u q
  simp only [seed, lambertSeed]
  congr 1
  refine tsum_congr fun i => ?_
  ring_nf

/-- **Periodization of any index** [AOS, §6.3]: for `m ≥ 2`, `M ≥ 1` and `x = e(α)`,
`α ∈ ℚ ∩ [0,1)`, the periodization of `𝒢_{d,x}` of index `M` converges normally on compact
subsets of `(ℍ × ℂ) \ 𝒟_x`, is holomorphic there, and satisfies the twisted index-`M` law. -/
theorem seedPeriodization_seed_any_index {m M : ℕ} (hm : 2 ≤ m) (hM : 1 ≤ M) {α : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor α →
      ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((M : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (M : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ :
          ENNReal) < ⊤) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => seedPeriodization M α (seed m (e α)) p.1 p.2)
        (halfPlaneProd \ divisor α) ∧
      ∀ τ w : ℂ, ∀ a b : ℤ, seedPeriodization M α (seed m (e α)) τ (w + a * τ + b) =
        e α ^ (2 * a) * e τ ^ (-(M : ℤ) * a ^ 2) * e w ^ (-2 * (M : ℤ) * a) *
          seedPeriodization M α (seed m (e α)) τ w := by
  set b : ℕ → ℂ → ℂ := fun i q => q ^ (i ^ 2) * gTail m (e α) i q with hb
  have hbd : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1) := fun i =>
    (differentiableOn_id.pow _).mul (differentiableOn_gTail hm _ i)
  have hx1 : ‖e (α : ℂ)‖ ≤ 1 := by rw [e, Complex.norm_exp]; simp
  have hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2) := by
    intro Q hQ0 hQ1
    obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm hQ0.le hQ1 zero_le_one
    refine ⟨C, fun i q hq => ?_⟩
    rw [hb, norm_mul, norm_pow, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC i q hq _ hx1) (by positivity)
  rw [seed_eq_lambertSeed]
  refine ⟨fun S hS hSD => seedPeriodization_lambertSeed_normal hM α hα0 hα1 hB S hS hSD,
    (differentiableOn_seedPeriodization_lambertSeed hM α hα0 hα1 hbd hB).2,
    fun τ w a k => seedPeriodization_twisted_law M α _ τ w a k⟩

end HigherDyson3
