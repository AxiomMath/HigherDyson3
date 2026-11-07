/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Summability of Gaussian-type series

For an integer `m ≥ 1` and reals `0 ≤ Q < 1`, `V ≥ 1`, the series
`∑_{n ∈ ℤ} Q^{m n²} V^{|n|}` converges (with `0⁰ = 1`). The quadratic exponent beats the
linear one: once `Q^{m N₀} V ≤ 1/2`, every term with `|n| ≥ N₀` is at most `2^{-|n|}`.

## Main results

* `HigherDyson3.gaussian_summable`: the series `∑_{n ∈ ℤ} Q^{m n²} V^{|n|}` is summable.

## Implementation notes

Powers are monoid powers with natural exponents `m * |n|²` and `|n|`, so that `0⁰ = 1`.
For nonnegative terms, `Summable` is the statement that the series is finite.
-/

public section

namespace HigherDyson3

/-- The one-sided series `∑_{n ≥ 0} Q^{m n²} V^n` is summable. -/
theorem gaussianSummable_nat {m : ℕ} (hm : 1 ≤ m) {Q V : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (hV : 1 ≤ V) : Summable (fun n : ℕ => Q ^ (m * n ^ 2) * V ^ n) := by
  have hrewrite : ∀ n : ℕ, Q ^ (m * n ^ 2) * V ^ n = (Q ^ (m * n) * V) ^ n := by
    intro n
    rw [mul_pow, ← pow_mul]
    ring_nf
  have htend : Filter.Tendsto (fun n : ℕ => Q ^ (m * n) * V) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Q ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hQ0 hQ1
    have h2 : Filter.Tendsto (fun n : ℕ => m * n) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop' (by omega)
    simpa using (h1.comp h2).mul_const V
  have hev : ∀ᶠ n : ℕ in Filter.atTop, Q ^ (m * n) * V ≤ 1 / 2 :=
    htend.eventually (ge_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => (1 / 2 : ℝ) ^ n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
  filter_upwards [hev] with n hn
  have hnn : 0 ≤ Q ^ (m * n) * V := mul_nonneg (pow_nonneg hQ0 _) (by linarith)
  rw [hrewrite, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnn _)]
  exact pow_le_pow_left₀ hnn hn n

/-- For an integer `m ≥ 1` and reals `0 ≤ Q < 1`, `V ≥ 1`, the series
`∑_{n ∈ ℤ} Q^{m n²} V^{|n|}` converges (with `0⁰ = 1`). -/
theorem gaussian_summable {m : ℕ} (hm : 1 ≤ m) {Q V : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (hV : 1 ≤ V) : Summable (fun n : ℤ => Q ^ (m * n.natAbs ^ 2) * V ^ n.natAbs) := by
  have h := gaussianSummable_nat hm hQ0 hQ1 hV
  exact Summable.of_nat_of_neg (by simpa using h) (by simpa using h)

end HigherDyson3
