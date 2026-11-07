/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.PartitionSeriesInverse

/-!
# Expanding the terms of the higher rank series

The `n`-th term of `R_m` is a product of partition series:
`𝒯_{m,n} = q^{n²} ∏_{j=1}^m Φ_{z^j,n} Φ_{z^{-j},n}` in `𝒜[[q]]`.

Writing `D = ∏_{j=1}^m (z^j q;q)_n (z^{-j} q;q)_n` and `Φ = ∏_{j=1}^m Φ_{z^j,n} Φ_{z^{-j},n}`,
the identity `(cq;q)_n Φ_{c,n} = 1` gives `D Φ = 1`; since `D` has constant coefficient `1`,
its formal inverse `D⁻¹` satisfies `D⁻¹ D = 1`, whence `D⁻¹ = Φ`.

## Main results

* `HigherDyson3.RTerm_eq`: `𝒯_{m,n} = q^{n²} ∏_{j=1}^m Φ_{z^j,n} Φ_{z^{-j},n}`.

## Implementation notes

The statement holds for every `m : ℕ`, including `m = 0`, where both sides are `q^{n²}`.
-/

public section

open PowerSeries Finset

namespace HigherDyson3

/-- The `q`-Pochhammer symbol `(cq;q)_n` has constant coefficient `1`. -/
private theorem constantCoeff_qPoch (c : LaurentRing) (n : ℕ) :
    constantCoeff (qPoch c n) = 1 := by
  rw [qPoch, map_prod]
  exact Finset.prod_eq_one fun r hr => by simp [Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hr).1]

/-- **Expansion of `𝒯_{m,n}`**: `𝒯_{m,n} = q^{n²} ∏_{j=1}^m Φ_{z^j,n} Φ_{z^{-j},n}`. -/
theorem RTerm_eq (m n : ℕ) :
    RTerm m n = X ^ (n ^ 2) * ∏ j ∈ Icc 1 m,
      partitionSeries (LaurentPolynomial.T (j : ℤ)) n *
        partitionSeries (LaurentPolynomial.T (-(j : ℤ))) n := by
  set D : PowerSeries LaurentRing := ∏ j ∈ Icc 1 m,
    qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n
  set Φ : PowerSeries LaurentRing := ∏ j ∈ Icc 1 m,
    partitionSeries (LaurentPolynomial.T (j : ℤ)) n *
      partitionSeries (LaurentPolynomial.T (-(j : ℤ))) n
  have hDΦ : D * Φ = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [mul_mul_mul_comm, qPoch_mul_partitionSeries, qPoch_mul_partitionSeries, one_mul]
  rw [RTerm]
  congr 1
  calc seriesInv D = seriesInv D * (D * Φ) := by rw [hDΦ, mul_one]
    _ = (D * seriesInv D) * Φ := by ring
    _ = Φ := by rw [seriesInv, mul_invOfUnit D 1 (by simp [D, constantCoeff_qPoch]), one_mul]

end HigherDyson3
