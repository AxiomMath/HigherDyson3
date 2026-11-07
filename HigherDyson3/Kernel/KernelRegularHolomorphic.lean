/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.DenominatorBoundRestricted
public import HigherDyson3.Bounds.ThetaTermMajorant
public import HigherDyson3.Divisor.DivisorChar
public import HigherDyson3.Divisor.DivisorNbhdOpen
public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic

/-!
# Holomorphy of the regular part of the kernel

Let `m ≥ 2`, `0 ≤ α < 1` rational, `x = e(α)` and `a, b ∈ ℤ`. The regular part
`𝒦^{(a)}_{m,x}` of the kernel is holomorphic on the neighbourhood `Ω_{a,b}` of the divisor
component `L_{a,b}`.

At a point of `Ω_{a,b}` no denominator `1 - x u q^n` with `n ≠ -a` vanishes, since its zeros
are the components `L_{-n,b'}`, all different from `L_{a,b}`. On a compact subset of `Ω_{a,b}`
the reciprocals of these denominators are uniformly bounded, and `|x| = 1`, so the summands are
dominated by the theta-type terms `|q^{mn²} u^{2mn}|`, whose suprema are summable. The series
therefore converges normally on compact subsets of the open set `Ω_{a,b}`.

## Main results

* `HigherDyson3.kernelRegular_differentiableOn`: `𝒦^{(a)}_{m,x}` is holomorphic on `Ω_{a,b}`.
-/

public section

open Complex

namespace HigherDyson3

/-- `‖e(α)‖ = 1` for real `α`. -/
private lemma kernelRegularHolomorphic_norm_e_real (α : ℝ) : ‖e (α : ℂ)‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- On `Ω_{a,b}`, no denominator `1 - x u q^n` with `n ≠ -a` vanishes. -/
private lemma kernelRegularHolomorphic_denom_ne_zero (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {a b : ℤ} {p : ℂ × ℂ} (hp : p ∈ divisorNbhd α a b) {n : ℤ} (hn : n ≠ -a) :
    1 - e α * e p.2 * e p.1 ^ n ≠ 0 := by
  intro h
  obtain ⟨b', hb'⟩ := (divisor_char α hα0 hα1 (τ := p.1) (w := p.2) hp.1 n).mp h
  refine hp.2 (Set.mem_iUnion₂.mpr ⟨(-n, b'), ?_, hb'⟩)
  intro hc
  exact hn (by have := congrArg Prod.fst hc; simp at this; omega)

/-- **Holomorphy of the regular part.** For an integer `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`x = e(α)` and `a, b ∈ ℤ`, the function `𝒦^{(a)}_{m,x}` is holomorphic on `Ω_{a,b}`. -/
theorem kernelRegular_differentiableOn (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (a b : ℤ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => kernelRegular m α a p.1 p.2) (divisorNbhd α a b) := by
  have hcast : ((α : ℝ) : ℂ) = (α : ℂ) := by push_cast; rfl
  have he : Differentiable ℂ e := fun z => by unfold e; fun_prop
  have hne : ∀ z, e z ≠ 0 := fun z => Complex.exp_ne_zero _
  unfold kernelRegular
  refine differentiableOn_tsum_of_normal (divisorNbhd_isOpen α hα0 hα1 a b) ?_ ?_
  · intro n p hp
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [div_eq_mul_inv]
    refine DifferentiableAt.mul ?_ (DifferentiableAt.inv ?_
      (kernelRegularHolomorphic_denom_ne_zero α hα0 hα1 hp n.2))
    · refine (DifferentiableAt.mul (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_)
      · exact ((he _).comp _ differentiableAt_fst).zpow (Or.inl (hne _))
      · exact ((he _).comp _ differentiableAt_snd).zpow (Or.inl (hne _))
    · refine (differentiableAt_const _).sub (DifferentiableAt.mul ?_ ?_)
      · exact (differentiableAt_const _).mul ((he _).comp _ differentiableAt_snd)
      · exact ((he _).comp _ differentiableAt_fst).zpow (Or.inl (hne _))
  · intro K hK hKc
    have hKH : K ⊆ halfPlaneProd := fun p hp => (hK hp).1
    obtain ⟨A, hA0, hA⟩ := denominator_bound_restricted (α : ℝ) K hKc hKH {n | n ≠ -a}
      (fun p hp n hn => by
        rw [hcast]; exact kernelRegularHolomorphic_denom_ne_zero α hα0 hα1 (hK hp) hn)
    obtain ⟨M, hMs, hM0, hM⟩ := thetaTermMajorant_exists (m := (m : ℤ)) (by omega) 0 K hKc hKH
    refine ⟨fun n => A * M n, (hMs.subtype _).mul_left A, fun n p hp => ?_⟩
    have hAn := hA p hp n n.2
    rw [hcast] at hAn
    have hMn := hM n p hp
    simp only [zero_mul, add_zero, zero_add] at hMn
    have hx : ‖e (α : ℂ) ^ (-2 * (n : ℤ))‖ = 1 := by
      rw [norm_zpow, ← hcast, kernelRegularHolomorphic_norm_e_real, one_zpow]
    rw [norm_div, norm_mul, norm_mul, hx, one_mul, div_eq_mul_inv, ← norm_mul]
    change _ ≤ A * M n
    rw [mul_comm A]
    exact mul_le_mul hMn hAn (by positivity) (hM0 _)

end HigherDyson3
