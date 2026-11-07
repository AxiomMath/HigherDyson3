/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Symmetry of the full rank

Swapping `α_j` and `β_j` in every pair of an uncoupled Dyson symbol is an involution that
preserves the size and negates the full rank, so `N_m(r, N) = N_m(-r, N)`.
-/

public section

namespace HigherDyson3

namespace DysonSymbol

variable {m : ℕ}

/-- The involution `(n; α₁, β₁, …, α_m, β_m) ↦ (n; β₁, α₁, …, β_m, α_m)`. -/
private def swap (s : DysonSymbol m) : DysonSymbol m where
  n := s.n
  α := s.β
  β := s.α
  α_mem := s.β_mem
  β_mem := s.α_mem

@[simp]
private theorem swap_swap (s : DysonSymbol m) : s.swap.swap = s := rfl

@[simp]
private theorem size_swap (s : DysonSymbol m) : s.swap.size = s.size := by
  simp only [size, swap, add_comm ((s.β _).size)]

@[simp]
private theorem fullRank_swap (s : DysonSymbol m) : s.swap.fullRank = -s.fullRank := by
  simp only [fullRank, swap, ← Finset.sum_neg_distrib, ← mul_neg, neg_sub]

end DysonSymbol

/-- **Symmetry of the full rank** (paper Theorem 2.3): `N_m(r, N) = N_m(-r, N)`. -/
theorem rankCount_neg (m : ℕ) (_hm : 1 ≤ m) (r : ℤ) (N : ℕ) :
    rankCount m r N = rankCount m (-r) N :=
  Nat.card_congr
    { toFun := fun s => ⟨s.1.swap, by simp [s.2.1, s.2.2]⟩
      invFun := fun s => ⟨s.1.swap, by simp [s.2.1, s.2.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end HigherDyson3
