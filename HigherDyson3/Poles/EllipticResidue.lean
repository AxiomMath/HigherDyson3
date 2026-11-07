/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.PeriodizationDecomposition
public import HigherDyson3.LocalFacts.PuncturedOffDivisor
public import HigherDyson3.Kernel.KernelResidue
public import HigherDyson3.LocalFacts.ThetaSumHolomorphic

/-!
# Residues of the periodization

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`, `τ ∈ ℍ`, `q = e(τ)` and `a, b ∈ ℤ`, and
put `w_{a,b} = -α + aτ + b`. Then
`ε ℰ_{m,x}(τ, w_{a,b} + ε) → -(ρ_{m,x}(τ) / 2πi) x^{2(m+1)a} q^{-ma²}` as `ε → 0`, `ε ≠ 0`.

For small `ε ≠ 0` the point `(τ, w_{a,b} + ε)` is off the divisor
(`HigherDyson3.punctured_off_divisor`), so the decomposition
`ℰ_{m,x} = ρ_{m,x} 𝒦_{m,x} + S` with `S(w) = ∑_ℓ C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ, w)`
(`HigherDyson3.periodization_decomposition`) applies. The term `ρ_{m,x}(τ) ε 𝒦_{m,x}` converges
by the residue of the kernel (`HigherDyson3.kernel_residue`), and `ε S(w_{a,b} + ε) → 0`
because `S` is continuous (`HigherDyson3.differentiableOn_thetaSum`).

## Main results

* `HigherDyson3.periodization_residue`: the residue of `ℰ_{m,x}(τ, ·)` at `w_{a,b}`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Filter Topology

namespace HigherDyson3

/-- **Residues of the periodization.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`,
`τ ∈ ℍ`, `q = e(τ)`, `a, b ∈ ℤ` and `w_{a,b} = -α + aτ + b`,
`ε ℰ_{m,x}(τ, w_{a,b} + ε) → -(ρ_{m,x}(τ) / 2πi) x^{2(m+1)a} q^{-ma²}` as `ε → 0`,
`ε ≠ 0`. -/
theorem periodization_residue {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (a b : ℤ) :
    Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
      (𝓝 (-(rho m α τ / (2 * Real.pi * Complex.I)) * e α ^ (2 * ((m : ℤ) + 1) * a) *
        e τ ^ (-(m : ℤ) * a ^ 2))) := by
  set w₀ : ℂ := -(α : ℂ) + a * τ + b with hw₀
  set S : ℂ → ℂ := fun w =>
    ∑ ℓ ∈ Finset.range (2 * m), coeffC m ℓ α τ * twistedTheta m ℓ α τ w with hS
  -- the theta sum is continuous along the slice
  have hopen : IsOpen halfPlaneProd :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  have hSc : ContinuousAt (fun ε : ℂ => S (w₀ + ε)) 0 := by
    have hT := ((differentiableOn_thetaSum hm hα0 hα1).differentiableAt
      (hopen.mem_nhds (show (τ, w₀) ∈ halfPlaneProd from hτ))).continuousAt
    have hline : Continuous fun ε : ℂ => (τ, w₀ + ε) := by fun_prop
    have hT' : ContinuousAt ((fun p : ℂ × ℂ => ∑ ℓ ∈ Finset.range (2 * m),
        coeffC m ℓ α p.1 * twistedTheta m ℓ α p.1 p.2) ∘ fun ε : ℂ => (τ, w₀ + ε)) 0 :=
      hT.comp_of_eq hline.continuousAt (by rw [add_zero])
    exact hT'
  have hS0 : Tendsto (fun ε : ℂ => ε * S (w₀ + ε)) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℂ => ε * S (w₀ + ε)) (𝓝 0) (𝓝 (0 * S (w₀ + 0))) :=
      (continuousAt_id.mul hSc).tendsto
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hK := (kernel_residue m hm α hα0 hα1 hτ a b).const_mul (rho m α τ)
  have hsum := hK.add hS0
  -- near `0`, `ε ≠ 0`, the function is given by the decomposition
  obtain ⟨δ, hδ, hoff⟩ := punctured_off_divisor α hα0 hα1 hτ w₀
  have heq : (fun ε : ℂ => rho m α τ * (ε * kernel m α τ (w₀ + ε)) + ε * S (w₀ + ε))
      =ᶠ[𝓝[≠] 0] fun ε => ε * periodization m α τ (w₀ + ε) := by
    have hball : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ‖ε‖ < δ :=
      nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hδ) fun ε hε =>
        mem_ball_zero_iff.mp hε)
    filter_upwards [hball, self_mem_nhdsWithin] with ε hεδ hε0
    have hε0 : ε ≠ 0 := hε0
    rw [periodization_decomposition hm hα0 hα1 (hoff ε (norm_pos_iff.mpr hε0) hεδ)]
    ring
  rw [add_zero] at hsum
  convert hsum.congr' heq using 2
  ring

end HigherDyson3
