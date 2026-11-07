/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Divisor.DivisorChar
public import HigherDyson3.Divisor.DivisorComplOpen
public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic
public import HigherDyson3.Periodization.PeriodizationDouble
public import HigherDyson3.Product.GHolomorphic

/-!
# Holomorphy of the periodization off the divisor

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. The periodization
`ℰ_{m,x}` is holomorphic on the open set `U = (ℍ × ℂ) \ 𝒟_x`.

On `U`, `ℰ_{m,x}` is the sum of the double summands `ℰ^{dbl}_{n,k}` over `ℤ × ℕ`
(`HigherDyson3.periodization_double`). Each summand is holomorphic on `U`: its numerator is
built from `e`, integer powers of the nonvanishing `e(τ)`, `e(w)`, and the tail
`g_{k,x}(e(τ))` (holomorphic since `e` maps `ℍ` into the unit disk), and its denominator
`1 - x e(w) e(τ)^{n+k}` does not vanish off the divisor (`HigherDyson3.divisor_char`). The
series converges normally on compact subsets of `U`
(`HigherDyson3.doubleSeriesNormal_exists_majorant`), so its sum is holomorphic
(`HigherDyson3.differentiableOn_tsum_of_normal`).

## Main results

* `HigherDyson3.periodization_holomorphic_off`: `U` is open and `ℰ_{m,x}` is holomorphic
  on `U`.
-/

public section

open Complex

namespace HigherDyson3

/-- `e` maps the upper half-plane into the open unit disk. -/
lemma ellipticHolomorphicOff_e_mem_ball {τ : ℂ} (hτ : 0 < τ.im) :
    e τ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, e, Complex.norm_exp]
  have : (2 * Real.pi * I * τ).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, ← Real.exp_zero, Real.exp_lt_exp]
  have := Real.pi_pos
  nlinarith

/-- Each double summand `ℰ^{dbl}_{n,k}` is holomorphic on `(ℍ × ℂ) \ 𝒟_x`. -/
lemma ellipticHolomorphicOff_differentiableOn_doubleSummand {m : ℕ} (hm : 2 ≤ m) {α : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℤ) (k : ℕ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => doubleSummand m α n k p.1 p.2)
      (halfPlaneProd \ divisor α) := by
  rintro ⟨τ, w⟩ ⟨hτ, hD⟩
  have hτ' : 0 < τ.im := hτ
  have hq : e τ ≠ 0 := Complex.exp_ne_zero _
  have hu : e w ≠ 0 := Complex.exp_ne_zero _
  have hden : 1 - e α * e w * e τ ^ (n + k) ≠ 0 := by
    intro h
    obtain ⟨b, hb⟩ := (divisor_char α hα0 hα1 (τ := τ) (w := w) hτ (n + k)).mp h
    exact hD (Set.mem_iUnion₂.mpr ⟨_, b, hb⟩)
  have hfst : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.1) (τ, w) := by
    unfold e
    fun_prop
  have hsnd : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.2) (τ, w) := by
    unfold e
    fun_prop
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => gTail m (e α) k (e p.1)) (τ, w) := by
    refine DifferentiableAt.comp (𝕜 := ℂ) (g := gTail m (e α) k) (τ, w) ?_ hfst
    exact (differentiableOn_gTail hm (e α) k).differentiableAt
      (Metric.isOpen_ball.mem_nhds (ellipticHolomorphicOff_e_mem_ball hτ'))
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [doubleSummand]
  have hnum : DifferentiableAt ℂ (fun p : ℂ × ℂ => (e α ^ 2)⁻¹ * e α ^ (-2 * n) *
      e p.1 ^ ((m : ℤ) * n ^ 2 + (k : ℤ) ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
      gTail m (e α) k (e p.1)) (τ, w) :=
    ((((differentiableAt_const _).mul (differentiableAt_const _)).mul
      (hfst.zpow (Or.inl hq))).mul (hsnd.zpow (Or.inl hu))).mul hg
  have hdenD : DifferentiableAt ℂ (fun p : ℂ × ℂ => 1 - e α * e p.2 * e p.1 ^ (n + k))
      (τ, w) :=
    (differentiableAt_const _).sub
      (((differentiableAt_const _).mul hsnd).mul (hfst.zpow (Or.inl hq)))
  simp only [div_eq_mul_inv]
  exact hnum.mul (hdenD.inv hden)

/-- **Holomorphy off the divisor.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`, the
set `(ℍ × ℂ) \ 𝒟_x` is open and the periodization `ℰ_{m,x}` is holomorphic on it. -/
theorem periodization_holomorphic_off {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    IsOpen (halfPlaneProd \ divisor α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => periodization m α p.1 p.2)
        (halfPlaneProd \ divisor α) := by
  have hU := divisor_compl_open α hα0 hα1
  refine ⟨hU, ?_⟩
  have hsum : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∑' i : ℤ × ℕ, doubleSummand m α i.1 i.2 p.1 p.2)
      (halfPlaneProd \ divisor α) :=
    differentiableOn_tsum_of_normal (f := fun (i : ℤ × ℕ) (p : ℂ × ℂ) =>
        doubleSummand m α i.1 i.2 p.1 p.2) hU
      (fun i => ellipticHolomorphicOff_differentiableOn_doubleSummand hm hα0 hα1 i.1 i.2)
      fun K hK hKc => by
        obtain ⟨M, hM, -, hle⟩ := doubleSeriesNormal_exists_majorant hm α hα0 hα1 K hKc hK
        exact ⟨M, hM, hle⟩
  refine hsum.congr fun p hp => ?_
  exact (periodization_double hm hα0 hα1 (τ := p.1) (w := p.2) hp).2

end HigherDyson3
