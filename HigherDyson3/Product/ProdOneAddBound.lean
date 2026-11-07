/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Deviation of an absolutely convergent product from `1`

If `∑ ‖a i‖ < ∞` in a complete normed commutative ring with `‖1‖ = 1`, then the product
`∏ (1 + a i)` converges unconditionally and
`‖∏ (1 + a i) - 1‖ ≤ exp (∑ ‖a i‖) - 1`.
The finite version is Mathlib's `Finset.norm_prod_one_add_sub_one_le`; the infinite one
follows by passing to the limit along the finite partial products.

## Main results

* `HigherDyson3.norm_tprod_one_add_sub_one_le`: the bound for the infinite product.

## Implementation notes

The statement is made for an arbitrary index type and an arbitrary complete normed
commutative ring with `‖1‖ = 1`; sequences `(a_r)_{r ≥ 1}` of complex numbers are the
case `ι = ℕ`, `R = ℂ` (after reindexing `r ↦ r + 1`). The product is Mathlib's
unconditional `tprod`, which for `ι = ℕ` is the limit of the partial products
`∏_{r < n} (1 + a r)` by `Multipliable.tendsto_prod_tprod_nat`.
-/

public section

namespace HigherDyson3

/-- An absolutely convergent product `∏ (1 + a i)` lies within `exp (∑ ‖a i‖) - 1` of `1`. -/
theorem norm_tprod_one_add_sub_one_le {ι R : Type*} [NormedCommRing R] [NormOneClass R]
    [CompleteSpace R] {a : ι → R} (ha : Summable fun i => ‖a i‖) :
    ‖∏' i, (1 + a i) - 1‖ ≤ Real.exp (∑' i, ‖a i‖) - 1 := by
  have hm := (multipliable_one_add_of_summable ha).hasProd
  have hlim : Filter.Tendsto (fun s : Finset ι => ‖∏ i ∈ s, (1 + a i) - 1‖) Filter.atTop
      (nhds ‖∏' i, (1 + a i) - 1‖) :=
    ((hm.sub tendsto_const_nhds).norm)
  refine le_of_tendsto' hlim fun s => ?_
  refine (Finset.norm_prod_one_add_sub_one_le s a).trans ?_
  gcongr
  exact ha.sum_le_tsum s fun i _ => norm_nonneg _

end HigherDyson3
