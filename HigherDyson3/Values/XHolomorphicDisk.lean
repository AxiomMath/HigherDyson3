/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GHolomorphic
public import HigherDyson3.Product.GBound

/-!
# Holomorphy of the series `X_j` on the unit disk

Let `m ≥ 2`, `d = 2m + 1`, `x ∈ ℂ` and `j ∈ ℕ`. The series
`X_j^{(m)}(x; q) = ∑_{k ≥ 0} q^{k² + jk} g_{k,x}(q)` agrees, for `0 < |q| < 1`, with a
function holomorphic on the whole open unit disk.

Since `j ≥ 0` the exponents `k² + jk` are natural numbers, so
`f(q) = ∑_k q^{k² + jk} g_{k,x}(q)` makes sense for every `|q| < 1`, including `q = 0`. Each
summand is holomorphic, and on `|q| ≤ Q < 1` the uniform bound `|g_{k,x}(q)| ≤ C` together
with `k² + jk ≥ k` gives `|q^{k² + jk} g_{k,x}(q)| ≤ C Q^k`. The Weierstrass `M`-test then
shows that `f` is holomorphic.

## Main results

* `HigherDyson3.exists_differentiableOn_eq_XSeries`: `X_j` extends holomorphically to the
  open unit disk.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex

namespace HigherDyson3

/-- **Holomorphy of `X_j` on the disk.** For `m ≥ 2`, `x ∈ ℂ` and `j ∈ ℕ` there is a function
`f`, complex differentiable on the open unit disk, with `f q = X_j^{(m)}(x; q)` whenever
`0 < ‖q‖ < 1`. -/
theorem exists_differentiableOn_eq_XSeries {m : ℕ} (hm : 2 ≤ m) (x : ℂ) (j : ℕ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → f q = XSeries m x j q := by
  refine ⟨fun q => ∑' k : ℕ, q ^ (k ^ 2 + j * k) * gTail m x k q, ?_, ?_⟩
  · intro z hz
    rw [mem_ball_zero_iff] at hz
    set Q : ℝ := (‖z‖ + 1) / 2 with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have hQ1 : Q < 1 := by linarith
    have hzQ : ‖z‖ < Q := by linarith
    obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm hQ0 hQ1 (norm_nonneg x)
    have hD : DifferentiableOn ℂ (fun q => ∑' k : ℕ, q ^ (k ^ 2 + j * k) * gTail m x k q)
        (Metric.ball 0 Q) := by
      refine differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => C * Q ^ k)
        ((summable_geometric_of_lt_one hQ0 hQ1).mul_left C) (fun k => ?_) Metric.isOpen_ball
        (fun k w hw => ?_)
      · exact (differentiable_pow _).differentiableOn.mul
          ((differentiableOn_gTail hm x k).mono (Metric.ball_subset_ball hQ1.le))
      · rw [mem_ball_zero_iff] at hw
        rw [norm_mul, norm_pow, mul_comm C]
        refine mul_le_mul ?_ (hC k w hw.le x le_rfl) (norm_nonneg _) (by positivity)
        calc ‖w‖ ^ (k ^ 2 + j * k) ≤ ‖w‖ ^ k :=
              pow_le_pow_of_le_one (norm_nonneg _) (hw.le.trans hQ1.le) (by nlinarith)
          _ ≤ Q ^ k := pow_le_pow_left₀ (norm_nonneg _) hw.le k
    exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hzQ)))
      |>.differentiableWithinAt
  · intro q _ _
    refine tsum_congr fun k => ?_
    rw [← zpow_natCast]
    push_cast
    rfl

end HigherDyson3
