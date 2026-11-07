/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.PeriodizationDecomposition
public import HigherDyson3.Kernel.KernelSimplePole
public import HigherDyson3.Periodization.EllipticRhoHolomorphic
public import HigherDyson3.LocalFacts.ThetaSumHolomorphic

/-!
# The periodization has at most simple poles

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)` and `a, b ∈ ℤ`. There is a
function `N` holomorphic on the neighbourhood `Ω_{a,b}` of the divisor component `L_{a,b}`
with `N(τ, w) = (w + α - aτ - b) ℰ_{m,x}(τ, w)` for every `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`.

By the decomposition `ℰ_{m,x} = ρ_{m,x} 𝒦_{m,x} + ∑_ℓ C_{m,ℓ,x} T^{[x]}_{m,ℓ}` off `𝒟_x`
(`HigherDyson3.periodization_decomposition`), it suffices to take
`N = ρ_{m,x}(τ) N_𝒦 + (w + α - aτ - b) ∑_ℓ C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ, w)`, where `N_𝒦`
is the holomorphic function removing the simple pole of the kernel along `L_{a,b}`
(`HigherDyson3.kernel_simple_pole`). It is holomorphic on `Ω_{a,b} ⊆ ℍ × ℂ` since `ρ_{m,x}`
is holomorphic on `ℍ` (`HigherDyson3.rho_holomorphic`) and the theta sum is holomorphic on
`ℍ × ℂ` (`HigherDyson3.differentiableOn_thetaSum`).

## Main results

* `HigherDyson3.periodization_simple_poles`: the periodization has at most a simple pole
  along each divisor component.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

noncomputable section

namespace HigherDyson3

/-- **The periodization has at most simple poles.** For an integer `m ≥ 2`, `α ∈ ℚ` with
`0 ≤ α < 1`, `x = e(α)` and `a, b ∈ ℤ`, there is a function `N` holomorphic on `Ω_{a,b}` with
`N(τ, w) = (w + α - aτ - b) ℰ_{m,x}(τ, w)` for all `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`. -/
theorem periodization_simple_poles (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (a b : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
      ∀ p ∈ halfPlaneProd \ divisor α,
        N p = (p.2 + α - a * p.1 - b) * periodization m α p.1 p.2 := by
  obtain ⟨NK, hNKd, hNK⟩ := kernel_simple_pole m hm α hα0 hα1 a b
  have hsub : divisorNbhd α a b ⊆ halfPlaneProd := Set.sdiff_subset
  refine ⟨fun p => rho m α p.1 * NK p + (p.2 + α - a * p.1 - b) *
    ∑ ℓ ∈ Finset.range (2 * m), coeffC m ℓ α p.1 * twistedTheta m ℓ α p.1 p.2, ?_,
    fun p hp => ?_⟩
  · refine DifferentiableOn.add (DifferentiableOn.mul ?_ hNKd) (DifferentiableOn.mul ?_
      ((differentiableOn_thetaSum hm hα0 hα1).mono hsub))
    · exact (rho_holomorphic hm α).comp differentiableOn_fst fun p hp => hsub hp
    · exact (by fun_prop : Differentiable ℂ fun p : ℂ × ℂ => p.2 + α - a * p.1 - b)
        |>.differentiableOn
  · simp only
    rw [periodization_decomposition hm hα0 hα1 hp, hNK p hp]
    ring

end HigherDyson3
