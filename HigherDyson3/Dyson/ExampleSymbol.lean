/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# An example of an uncoupled Dyson symbol

The uncoupled `2`-Dyson symbol `Σ = (3; (3,1), (2,2), (1), ∅)` of [AOS, Example 2.2], with
`|α₁| = 4`, `ℓ(α₁) = 2`, `|β₁| = 4`, `ℓ(β₁) = 2`, `|α₂| = 1`, `ℓ(α₂) = 1`, `|β₂| = 0`,
`ℓ(β₂) = 0`, size `|Σ| = 18` and full rank `FR₂(Σ) = 2`.
-/

public section

namespace HigherDyson3

/-- The uncoupled `2`-Dyson symbol `(3; (3,1), (2,2), (1), ∅)` of [AOS, Example 2.2]. -/
def exampleSymbol : DysonSymbol 2 where
  n := 3
  α := ![{3, 1}, {1}]
  β := ![{2, 2}, 0]
  α_mem := by simp only [boundedPartitions, Set.mem_ofPred_eq]; decide
  β_mem := by simp only [boundedPartitions, Set.mem_ofPred_eq]; decide

/-- The sizes and lengths of the partitions of `exampleSymbol` [AOS, Example 2.2]. -/
theorem exampleSymbol_partitions :
    (exampleSymbol.α 0).size = 4 ∧ (exampleSymbol.α 0).length = 2 ∧
    (exampleSymbol.β 0).size = 4 ∧ (exampleSymbol.β 0).length = 2 ∧
    (exampleSymbol.α 1).size = 1 ∧ (exampleSymbol.α 1).length = 1 ∧
    (exampleSymbol.β 1).size = 0 ∧ (exampleSymbol.β 1).length = 0 := by
  decide

/-- **[AOS, Example 2.2]**: `|Σ| = 18` and `FR₂(Σ) = 2` for `Σ = (3; (3,1), (2,2), (1), ∅)`. -/
theorem exampleSymbol_size_fullRank :
    exampleSymbol.size = 18 ∧ exampleSymbol.fullRank = 2 := by
  decide

end HigherDyson3
