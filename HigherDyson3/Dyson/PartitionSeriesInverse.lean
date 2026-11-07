/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.PartitionSeriesStep

/-!
# Partition series invert the Pochhammer symbol

`(cq;q)_n Φ_{c,n} = 1` in `𝒜[[q]]`, by induction on `n` from `(1 - c q^n) Φ_{c,n} = Φ_{c,n-1}`.
-/

public section

open PowerSeries

namespace HigherDyson3

/-- `Φ_{c,0} = 1`: the only partition with all parts at most `0` is the empty one. -/
private theorem partitionSeriesInverse_zero (c : LaurentRing) : partitionSeries c 0 = 1 := by
  refine PowerSeries.ext fun N => ?_
  have hset : {p : Partition | p ∈ boundedPartitions 0 ∧ p.size = N} =
      if N = 0 then {0} else ∅ := by
    ext p
    have h0 : p ∈ boundedPartitions 0 ↔ p = 0 := by
      refine ⟨fun h => Multiset.eq_zero_of_forall_notMem fun i hi => ?_, fun h i hi => ?_⟩
      · have := h i hi
        have := i.pos
        omega
      · simp [h] at hi
    split_ifs with hN
    · simp only [Set.mem_ofPred_eq, h0, Set.mem_singleton_iff, and_iff_left_iff_imp]
      rintro rfl
      simp [Partition.size, hN]
    · simp only [Set.mem_ofPred_eq, h0, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      simpa [Partition.size, eq_comm] using hN
  simp only [partitionSeries, coeff_mk, coeff_one]
  change ∑ᶠ p ∈ {p : Partition | p ∈ boundedPartitions 0 ∧ p.size = N}, c ^ p.length = _
  rw [hset]
  split_ifs with hN
  · simp [Partition.length]
  · simp

/-- **Partition series invert the Pochhammer symbol**: `(cq;q)_n Φ_{c,n} = 1` in `𝒜[[q]]`. -/
theorem qPoch_mul_partitionSeries (c : LaurentRing) (n : ℕ) :
    qPoch c n * partitionSeries c n = 1 := by
  induction n with
  | zero => simp [qPoch, partitionSeriesInverse_zero]
  | succ k ih =>
    rw [qPoch, Finset.prod_Icc_succ_top (by omega), mul_assoc,
      partitionSeries_step c (k + 1) (by omega), Nat.add_sub_cancel]
    exact ih

end HigherDyson3
