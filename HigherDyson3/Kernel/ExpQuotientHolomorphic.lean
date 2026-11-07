/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Holomorphy of `Φ(z) = z / (1 - e(z))`

The function `Φ(z) = z / (1 - e(z))`, extended by `Φ(0) = -1/(2πi)`, is holomorphic on the
open set `ℂ \ (ℤ \ {0})`. Writing `g(z) = 1 - e(z)`, which vanishes at `0`, one has
`Φ = 1 / dslope g 0` everywhere: the difference quotient `dslope g 0` is entire, equals
`(1 - e(z))/z` away from `0` and `g'(0) = -2πi` at `0`, and it vanishes exactly on the
nonzero integers.

## Main results

* `HigherDyson3.expQuotient_differentiableOn`: the set `ℂ \ (ℤ \ {0})` is open and
  `expQuotient` is complex differentiable on it.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex

namespace HigherDyson3

/-- The function `z ↦ 1 - e(z)`. -/
private noncomputable def g (z : ℂ) : ℂ := 1 - e z

private lemma g_zero : g 0 = 0 := by simp [g, e]

private lemma differentiable_g : Differentiable ℂ g := by
  unfold g e
  fun_prop

private lemma hasDerivAt_g : HasDerivAt g (-(2 * Real.pi * Complex.I)) 0 := by
  unfold g e
  simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp.const_sub 1

private lemma expQuotient_eq_one_div_dslope (z : ℂ) :
    expQuotient z = 1 / dslope g 0 z := by
  unfold expQuotient
  split_ifs with hz
  · subst hz
    rw [dslope_same, hasDerivAt_g.deriv]
    ring
  · rw [dslope_of_ne _ hz, slope_def_field, g_zero]
    simp [g]

private lemma dslope_ne_zero {z : ℂ} (hz : z ∈ (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ) :
    dslope g 0 z ≠ 0 := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  by_cases h0 : z = 0
  · subst h0
    rwa [dslope_same, hasDerivAt_g.deriv, neg_ne_zero]
  · rw [dslope_of_ne _ h0, slope_def_field, g_zero, sub_zero, sub_zero]
    refine div_ne_zero (fun h => hz ⟨?_, h0⟩) h0
    have h1 : Complex.exp (2 * Real.pi * Complex.I * z) = 1 := by
      simp only [g, e] at h
      linear_combination -h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, mul_left_cancel₀ h2 ?_⟩
    rw [hn]
    ring

/-- The set `ℂ \ (ℤ \ {0})` is open. -/
lemma isOpen_compl_range_intCast_sdiff_zero : IsOpen (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ := by
  have hemb : Topology.IsClosedEmbedding ((↑) : ℤ → ℂ) := by
    convert Complex.isometry_ofReal.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
    ext n
    simp
  convert (hemb.isClosedMap _ (isClosed_discrete {n : ℤ | n ≠ 0})).isOpen_compl using 2
  ext z
  simp only [Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨n, rfl⟩, h0⟩
    exact ⟨n, by exact_mod_cast h0, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, by exact_mod_cast hn⟩

/-- The set `ℂ \ (ℤ \ {0})` is open, and `expQuotient` is complex differentiable on it. -/
theorem expQuotient_differentiableOn :
    IsOpen (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ ∧
      DifferentiableOn ℂ expQuotient (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ := by
  refine ⟨isOpen_compl_range_intCast_sdiff_zero, fun z hz => ?_⟩
  have hd : Differentiable ℂ (dslope g 0) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact differentiable_g.differentiableOn
  rw [show expQuotient = fun z => 1 / dslope g 0 z from funext expQuotient_eq_one_div_dslope]
  exact ((differentiableAt_const _).div (hd z) (dslope_ne_zero hz)).differentiableWithinAt

end HigherDyson3
