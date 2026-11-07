/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Vanishing of `C_x` at nontrivial `d`-th roots of unity

Let `m ≥ 2` and `d = 2m + 1`. The finite constant `C_x = ∑_{r=0}^{d-1} x^r` vanishes
whenever `x` is a `d`-th root of unity other than `1`: multiplying by `1 - x` telescopes the
sum to `1 - x^d = 0`, and `1 - x ≠ 0`.

## Main results

* `HigherDyson3.Cx_eq_zero_of_pow_eq_one`: `C_x = 0` for `x ≠ 1` with `x ^ (2m+1) = 1`.

## Implementation notes

The hypothesis `2 ≤ m` is that of the source and is kept in the statement, although the
geometric-sum argument only uses `x ≠ 1` and `x ^ (2m+1) = 1`.

## References

* [Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*]
-/

public section

namespace HigherDyson3

/-- If `m ≥ 2`, `x ≠ 1` and `x ^ (2m+1) = 1`, then `C_x = 0`. -/
@[nolint unusedArguments]
theorem Cx_eq_zero_of_pow_eq_one {m : ℕ} (_hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 1)
    (hxd : x ^ (2 * m + 1) = 1) : Cx m x = 0 := by
  rw [Cx, cyclotomicSum, geom_sum_eq hx, hxd, sub_self, zero_div]

end HigherDyson3
