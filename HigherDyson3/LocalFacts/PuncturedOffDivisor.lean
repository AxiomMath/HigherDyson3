/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Divisor.DivisorComplOpen
public import HigherDyson3.Divisor.DivisorNbhdOpen

/-!
# Punctured slices avoid the divisor

For `0 ≤ α < 1`, `τ ∈ ℍ` and `w₀ ∈ ℂ`, there is `δ > 0` such that `(τ, w₀ + ε)` lies in
`(ℍ × ℂ) \ D_x` for every `ε` with `0 < |ε| < δ`.

If `(τ, w₀)` is off the divisor, this follows from the openness of `(ℍ × ℂ) \ D_x`. If it lies
on a component `L_{a,b}`, it lies on no other component (the imaginary part of `τ` is positive),
so it belongs to the open set `Ω_{a,b}`; a small punctured slice stays in `Ω_{a,b}` and misses
`L_{a,b}` because it moves `w` off `w₀`.

## Main results

* `HigherDyson3.punctured_off_divisor`: punctured slices avoid the divisor.
-/

public section

noncomputable section

open Complex Metric

namespace HigherDyson3

/-- A point `(τ, w)` of the component `L_{a,b}` lies in `Ω_{a,b}`: since `Im τ > 0`, it lies
on no other component. -/
private lemma puncturedOffDivisor_mem_divisorNbhd {α : ℚ} {a b : ℤ} {p : ℂ × ℂ}
    (hp : p ∈ divisorComponent α a b) : p ∈ divisorNbhd α a b := by
  refine ⟨hp.1, fun hq => ?_⟩
  obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hq
  have h : ((a : ℂ) - c.1) * p.1 = (c.2 : ℂ) - b := by
    linear_combination hp.2.symm.trans hpc.2
  have him : ((a : ℝ) - c.1) * p.1.im = 0 := by
    simpa using congrArg Complex.im h
  have ha : a = c.1 := by
    have := (mul_eq_zero.mp him).resolve_right hp.1.ne'
    exact_mod_cast sub_eq_zero.mp this
  have hb : b = c.2 := by
    subst ha
    have : (c.2 : ℂ) - b = 0 := by simpa using h.symm
    exact_mod_cast (sub_eq_zero.mp this).symm
  exact hc (Prod.ext ha.symm hb.symm)

/-- **Punctured slices avoid the divisor.** For `0 ≤ α < 1`, `τ ∈ ℍ` and `w₀ ∈ ℂ`, there is
`δ > 0` such that `(τ, w₀ + ε) ∈ (ℍ × ℂ) \ D_x` for every `ε ∈ ℂ` with `0 < |ε| < δ`. -/
theorem punctured_off_divisor (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (w₀ : ℂ) :
    ∃ δ > 0, ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → (τ, w₀ + ε) ∈ halfPlaneProd \ divisor α := by
  have hdist (ε : ℂ) : dist ((τ, w₀ + ε) : ℂ × ℂ) (τ, w₀) = ‖ε‖ := by
    simp [dist_eq_norm]
  by_cases hD : (τ, w₀) ∈ divisor α
  · obtain ⟨a, b, hab⟩ := Set.mem_iUnion₂.mp hD
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (divisorNbhd_isOpen α hα0 hα1 a b) _
      (puncturedOffDivisor_mem_divisorNbhd hab)
    refine ⟨δ, hδ, fun ε hε0 hεδ => ?_⟩
    have hmem : (τ, w₀ + ε) ∈ divisorNbhd α a b := hball (by rw [mem_ball, hdist]; exact hεδ)
    refine ⟨hmem.1, fun hq => ?_⟩
    obtain ⟨a', b', hq'⟩ := Set.mem_iUnion₂.mp hq
    by_cases hc : ((a', b') : ℤ × ℤ) = (a, b)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hc
      have : w₀ + ε = w₀ := hq'.2.trans hab.2.symm
      exact hε0.ne' (by simpa using this)
    · exact hmem.2 (Set.mem_iUnion₂.mpr ⟨(a', b'), hc, hq'⟩)
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (divisor_compl_open α hα0 hα1) _
      (⟨hτ, hD⟩ : (τ, w₀) ∈ halfPlaneProd \ divisor α)
    exact ⟨δ, hδ, fun ε _ hεδ => hball (by rw [mem_ball, hdist]; exact hεδ)⟩

end HigherDyson3
