/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.ExpQuotientHolomorphic
public import HigherDyson3.Kernel.KernelRegularHolomorphic
public import HigherDyson3.Kernel.KernelSplit

/-!
# The kernel has at most a simple pole along `L_{a,b}`

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)` and `a, b ∈ ℤ`, and put
`z(τ, w) = w + α - aτ - b`. The product `z · 𝒦_{m,x}` extends holomorphically to the
neighbourhood `Ω_{a,b}` of the component `L_{a,b}`.

Since `x u q^{-a} = e(z)`, splitting off the summand `n = -a` of the kernel gives, off `𝒟_x`,
`z 𝒦_{m,x} = z 𝒦^{(a)}_{m,x} + x^{2a} q^{ma²} u^{-2ma} Φ(z)` with `Φ(z) = z / (1 - e(z))`.
The right-hand side is holomorphic on `Ω_{a,b}`: the regular part is, and `z` maps `Ω_{a,b}`
into `ℂ \ (ℤ \ {0})`, where `Φ` is holomorphic.

## Main results

* `HigherDyson3.kernel_simple_pole`: there is `N` holomorphic on `Ω_{a,b}` with
  `N(τ, w) = (w + α - aτ - b) 𝒦_{m,x}(τ, w)` on `(ℍ × ℂ) \ 𝒟_x`.
-/

public section

open Complex

namespace HigherDyson3

/-- `x u q^{-a} = e(w + α - aτ - b)` for `x = e(α)`, `u = e(w)`, `q = e(τ)`. -/
theorem kernelSimplePole_e_mul (α w τ : ℂ) (a b : ℤ) :
    e α * e w * e τ ^ (-a) = e (w + α - a * τ - b) := by
  simp only [e]
  rw [← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  exact ⟨b, by push_cast; ring⟩

/-- If `w + α - aτ - b = k` is an integer at a point of `ℍ × ℂ`, the point lies on
`L_{a,b+k}`. -/
theorem kernelSimplePole_mem_component (α : ℚ) (a b k : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd) (hk : p.2 + α - a * p.1 - b = k) :
    p ∈ divisorComponent α a (b + k) :=
  ⟨hp, by push_cast; linear_combination hk⟩

/-- On `Ω_{a,b}`, `w + α - aτ - b` is not a nonzero integer. -/
theorem kernelSimplePole_mapsTo (α : ℚ) (a b : ℤ) :
    Set.MapsTo (fun p : ℂ × ℂ => p.2 + α - a * p.1 - b) (divisorNbhd α a b)
      (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ := by
  rintro p hp ⟨⟨k, hk⟩, hk0⟩
  have hk0 : k ≠ 0 := by rintro rfl; exact hk0 (by rw [← hk]; simp)
  refine hp.2 (Set.mem_iUnion₂.mpr ⟨(a, b + k), ?_,
    kernelSimplePole_mem_component α a b k hp.1 hk.symm⟩)
  intro h
  exact hk0 (by have := congrArg Prod.snd h; simpa using this)

/-- Off `𝒟_x`, `w + α - aτ - b` is not an integer. -/
theorem kernelSimplePole_ne_int (α : ℚ) (a b : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ divisor α) (k : ℤ) : p.2 + α - a * p.1 - b ≠ k := fun hk =>
  hp.2 (Set.mem_iUnion₂.mpr ⟨a, b + k, kernelSimplePole_mem_component α a b k hp.1 hk⟩)

/-- `(ℍ × ℂ) \ 𝒟_x ⊆ Ω_{a,b}`. -/
theorem kernelSimplePole_compl_subset (α : ℚ) (a b : ℤ) :
    halfPlaneProd \ divisor α ⊆ divisorNbhd α a b := by
  rintro p ⟨hpH, hpD⟩
  refine ⟨hpH, fun h => hpD ?_⟩
  obtain ⟨c, -, hc⟩ := Set.mem_iUnion₂.mp h
  exact Set.mem_iUnion₂.mpr ⟨c.1, c.2, hc⟩

/-- **The kernel has at most a simple pole along `L_{a,b}`.** For an integer `m ≥ 2`,
`α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)` and `a, b ∈ ℤ`, there is a function `N` holomorphic on
`Ω_{a,b}` with `N(τ, w) = (w + α - aτ - b) 𝒦_{m,x}(τ, w)` for all
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`. -/
theorem kernel_simple_pole (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (a b : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
      ∀ p ∈ halfPlaneProd \ divisor α,
        N p = (p.2 + α - a * p.1 - b) * kernel m α p.1 p.2 := by
  set z : ℂ × ℂ → ℂ := fun p => p.2 + α - a * p.1 - b with hz
  have he : Differentiable ℂ e := fun z => by unfold e; fun_prop
  have hne : ∀ z, e z ≠ 0 := fun z => Complex.exp_ne_zero _
  have hzd : Differentiable ℂ z := by rw [hz]; fun_prop
  refine ⟨fun p => z p * kernelRegular m α a p.1 p.2 +
    e α ^ (2 * a) * e p.1 ^ ((m : ℤ) * a ^ 2) * e p.2 ^ (-2 * (m : ℤ) * a) *
      expQuotient (z p), ?_, fun p hp => ?_⟩
  · refine (hzd.differentiableOn.mul
      (kernelRegular_differentiableOn m hm α hα0 hα1 a b)).add (DifferentiableOn.mul ?_ ?_)
    · refine (Differentiable.mul (Differentiable.mul (differentiable_const _) ?_) ?_)
        |>.differentiableOn
      · exact fun p => ((he _).comp _ differentiableAt_fst).zpow (Or.inl (hne _))
      · exact fun p => ((he _).comp _ differentiableAt_snd).zpow (Or.inl (hne _))
    · exact expQuotient_differentiableOn.2.comp hzd.differentiableOn
        (kernelSimplePole_mapsTo α a b)
  · have hz0 : z p ≠ 0 := by simpa using kernelSimplePole_ne_int α a b hp 0
    have hEq : expQuotient (z p) = z p / (1 - e α * e p.2 * e p.1 ^ (-a)) := by
      rw [kernelSimplePole_e_mul _ _ _ a b, expQuotient,
        ite_eq_right_of_eq_false _ _ (eq_false hz0)]
    simp only
    rw [hEq, kernel_split m hm α hα0 hα1 a hp]
    ring

end HigherDyson3
