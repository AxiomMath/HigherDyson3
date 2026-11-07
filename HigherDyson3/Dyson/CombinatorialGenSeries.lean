/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.RTermCoeff
public import HigherDyson3.Dyson.RTermOrder

/-!
# The generating function of the full rank

For `m ≥ 1`, `N ∈ ℕ` and `r ∈ ℤ`, the coefficient `[z^r] [q^N] R_m(z;q)` is the number
`N_m(r, N)` of `m`-Dyson symbols of size `N` and full rank `r`.

Only the terms `𝒯_{m,n}` with `n ≤ N` contribute to `[q^N] R_m`, since `[q^N] 𝒯_{m,n} = 0`
for `N < n²`. The coefficient `[z^r] [q^N] 𝒯_{m,n}` counts the symbols with square `n`, size
`N` and full rank `r`, and summing over `n ≤ N` counts all symbols of size `N` and full rank
`r`, each of which has square at most `N`.

## Main results

* `HigherDyson3.RSeries_zCoeff_qCoeff`: `[z^r] [q^N] R_m(z;q) = N_m(r, N)`.
-/

public section

open PowerSeries Finset

namespace HigherDyson3

/-- **Generating function of the full rank**: for `m ≥ 1`, `N ∈ ℕ` and `r ∈ ℤ`,
`[z^r] [q^N] R_m(z;q) = N_m(r, N)`. -/
theorem RSeries_zCoeff_qCoeff (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (r : ℤ) :
    zCoeff r (qCoeff N (RSeries m)) = (rankCount m r N : ℤ) := by
  classical
  have hsupp : (Function.support fun n => coeff N (RTerm m n)) ⊆ (range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hn (RTerm_coeff_eq_zero_of_lt m (by nlinarith))
  have hq : qCoeff N (RSeries m) = ∑ n ∈ range (N + 1), qCoeff N (RTerm m n) := by
    rw [qCoeff, RSeries, coeff_mk, finsum_eq_sum_of_support_subset _ hsupp]
    rfl
  have hfin : {s : DysonSymbol m | s.size = N ∧ s.fullRank = r}.Finite :=
    (DysonSymbol.finite_size_eq m hm N).subset fun s hs => hs.1
  have hcard : ∀ n, Nat.card {s : DysonSymbol m // s.n = n ∧ s.size = N ∧ s.fullRank = r} =
      (hfin.toFinset.filter (·.n = n)).card := by
    intro n
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun s => by simp; tauto)
  have hz : zCoeff r (∑ n ∈ range (N + 1), qCoeff N (RTerm m n)) =
      ∑ n ∈ range (N + 1), zCoeff r (qCoeff N (RTerm m n)) := by
    simp only [zCoeff]
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [hq, hz]
  simp_rw [RTerm_zCoeff_qCoeff m hm, hcard]
  rw [rankCount, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise]
  · rw [← Nat.card_eq_finsetCard]
    exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun s => by simp))
  · intro s hs
    simp only [coe_range, Set.mem_Iio, Set.Finite.coe_toFinset, Set.mem_ofPred_eq,
      DysonSymbol.size] at hs ⊢
    have : s.n ≤ s.n ^ 2 := by nlinarith
    omega

end HigherDyson3
