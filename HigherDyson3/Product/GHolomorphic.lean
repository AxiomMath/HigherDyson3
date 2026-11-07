/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GFactorBound
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Holomorphy of the tails `g_{k,x}`

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. For `x ∈ ℂ` and `k ∈ ℕ` the
tail `g_{k,x}(q) = ∏_{r ≥ 1} P_d(x q^k q^r)` is holomorphic on the open unit disk.

On a disk `|q| < Q` with `Q < 1`, the point `y = x q^k` satisfies `|y| ≤ |x|`, so the
factors are uniformly within a summable bound `M_r` of `1`. By the Weierstrass criterion
for products the partial products, which are polynomials in `q`, converge locally
uniformly to `g_{k,x}`, and a locally uniform limit of holomorphic functions is holomorphic.

## Main results

* `HigherDyson3.differentiableOn_gTail`: `g_{k,x}` is complex differentiable on the open
  unit disk.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset Filter

namespace HigherDyson3

/-- **Holomorphy of the tails.** For `m ≥ 2`, `x ∈ ℂ` and `k ∈ ℕ`, the function
`q ↦ g_{k,x}(q)` is complex differentiable on the open unit disk. -/
theorem differentiableOn_gTail {m : ℕ} (hm : 2 ≤ m) (x : ℂ) (k : ℕ) :
    DifferentiableOn ℂ (gTail m x k) (Metric.ball 0 1) := by
  intro q₀ hq₀
  rw [mem_ball_zero_iff] at hq₀
  set Q : ℝ := (‖q₀‖ + 1) / 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQ1 : Q < 1 := by rw [hQ]; linarith
  have hq₀Q : ‖q₀‖ < Q := by rw [hQ]; linarith
  obtain ⟨M, -, hMs, hMb⟩ :=
    exists_summable_bound_cyclotomicSum_sub_one hm hQ0 hQ1 (norm_nonneg x)
  set f : ℕ → ℂ → ℂ := fun r q => cyclotomicSum m (x * q ^ k * q ^ (r + 1)) - 1 with hf
  have hcont : ∀ r, Continuous (f r) := fun r => by
    simp only [hf, cyclotomicSum]; fun_prop
  have hbound : ∀ᶠ r in atTop, ∀ q ∈ Metric.ball (0 : ℂ) Q, ‖f r q‖ ≤ M r := by
    refine Eventually.of_forall fun r q hq => ?_
    rw [mem_ball_zero_iff] at hq
    refine hMb r q hq.le _ ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg x)
      (pow_le_one₀ (norm_nonneg q) (hq.le.trans hQ1.le))
  have hprod := (hMs.hasProdLocallyUniformlyOn_nat_one_add Metric.isOpen_ball hbound
    fun r => (hcont r).continuousOn).tendstoLocallyUniformlyOn_finsetRange
  have hdiff : DifferentiableOn ℂ (fun q => ∏' r : ℕ, (1 + f r q)) (Metric.ball 0 Q) := by
    refine hprod.differentiableOn (Eventually.of_forall fun N => ?_) Metric.isOpen_ball
    refine Differentiable.differentiableOn ?_
    simp only [hf, cyclotomicSum]
    fun_prop
  have heq : (fun q => ∏' r : ℕ, (1 + f r q)) = gTail m x k := by
    funext q
    simp [hf, gTail, GProduct]
  rw [heq] at hdiff
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr hq₀Q))).differentiableWithinAt

end HigherDyson3

end
