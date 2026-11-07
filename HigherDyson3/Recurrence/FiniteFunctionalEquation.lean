/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.RawDefectIdentity
public import HigherDyson3.Recurrence.SeedShiftRaw

/-!
# The functional equation of the seed

Let `m ≥ 2`, `d = 2m + 1`, `x ≠ 0`, `0 < |q| < 1` and `u ≠ 0` with `x u q^k ≠ 1` for all
`k ∈ ℕ`. Writing `S(u) = ∑_{r=0}^{d-1} u^{2-r}`, the seed satisfies
`𝒢_{d,x}(q u; q) = x² q S(u) 𝒢_{d,x}(u; q) + q u^{3-d} R_{d,x}(u; q)
  - C_x q u² / (1 - x u) G_d(x; q)`.

This is the raw shift identity of the seed with its bracket
`ℬ_{d,x}(u; q) - S(u) G_d(x; q) / (1 - x u)` rewritten by the raw defect identity.

## Main results

* `HigherDyson3.seed_mul_eq_defectPoly`: the functional equation of the seed.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- **Functional equation of the seed.** For `m ≥ 2`, `d = 2m + 1`, `x ≠ 0`, `0 < ‖q‖ < 1` and
`u ≠ 0` with `x u q^k ≠ 1` for all `k ∈ ℕ`,
`𝒢_{d,x}(q u; q) = x² q (∑_{r=0}^{d-1} u^{2-r}) 𝒢_{d,x}(u; q) + q u^{3-d} R_{d,x}(u; q)
  - C_x q u² / (1 - x u) G_d(x; q)`. -/
theorem seed_mul_eq_defectPoly {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) (hu : u ≠ 0) (hxu : ∀ k : ℕ, x * u * q ^ k ≠ 1) :
    seed m x (q * u) q =
      x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
        q * u ^ (3 - (2 * m + 1 : ℤ)) * (defectPoly m x q).eval u -
        Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q := by
  have hxu0 : x * u ≠ 1 := by simpa using hxu 0
  have hraw := rawDefect_sub_eq hm hx hq0 hq1 hu hxu0
  rw [seed_mul_eq_rawDefect hm hx (norm_pos_iff.mp hq0) hq1 hu hxu]
  linear_combination q * hraw

end HigherDyson3
