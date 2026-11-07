/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.CompactQUBounds
public import HigherDyson3.Bounds.DenominatorBound
public import HigherDyson3.Bounds.GaussianSummable
public import HigherDyson3.Product.GBound

/-!
# Normal convergence of the double series of the periodization

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For every compact
`S ⊆ (ℍ × ℂ) \ 𝒟_x`, the double summands
`ℰ^{dbl}_{n,k}(τ,w) = x⁻² x^{-2n} q^{mn²+k²} u^{2mn} g_{k,x}(q) / (1 - x u q^{n+k})`
satisfy `∑_{(n,k) ∈ ℤ × ℕ} sup_{(τ,w) ∈ S} |ℰ^{dbl}_{n,k}(τ,w)| < ∞`.

On `S` one has `|q| ≤ Q < 1` and `a₀ ≤ |u| ≤ b₀`; with `c = max b₀ a₀⁻¹ ≥ 1` and
`V = c^{2m}`, `|u^{2mn}| ≤ V^{|n|}`. The tails are bounded by a constant `C`
(`HigherDyson3.exists_bound_norm_gTail`) and the reciprocal denominators by `A`
(`HigherDyson3.denominator_bound`), so the `(n,k)`-th summand is at most
`A C Q^{mn²} V^{|n|} Q^{k²}`, a product of summable nonnegative sequences
(`HigherDyson3.gaussian_summable` and `Q^{k²} ≤ Q^k`).

## Main results

* `HigherDyson3.doubleSeriesNormal_exists_majorant`: a summable majorant on `ℤ × ℕ` dominating
  `ℰ^{dbl}_{n,k}` uniformly on `S`, in the form used by
  `HigherDyson3.differentiableOn_tsum_of_normal`.
* `HigherDyson3.double_series_normal`: the sum over `ℤ × ℕ` of the suprema over `S` is finite.

## Implementation notes

As in `HigherDyson3.rho_normal`, the supremum is taken in `ℝ≥0∞`, so the statement is the
literal finiteness of the sum of suprema.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- If `0 < r`, `r ≤ c` and `r⁻¹ ≤ c`, then `r ^ z ≤ c ^ |z|` for every `z ∈ ℤ`. -/
lemma doubleSeriesNormal_zpow_le {r c : ℝ} (hr : 0 < r) (hrc : r ≤ c) (hrc' : r⁻¹ ≤ c)
    (z : ℤ) : r ^ z ≤ c ^ z.natAbs := by
  rcases Int.natAbs_eq z with h | h
  · rw [h, zpow_natCast, Int.natAbs_natCast]
    exact pow_le_pow_left₀ hr.le hrc _
  · rw [h, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hrc' _

/-- A summable majorant on `ℤ × ℕ` for the double summands `ℰ^{dbl}_{n,k}`, uniform over a
compact subset of `(ℍ × ℂ) \ 𝒟_x`. -/
theorem doubleSeriesNormal_exists_majorant {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∃ M : ℤ × ℕ → ℝ, Summable M ∧ (∀ i, 0 ≤ M i) ∧ ∀ i : ℤ × ℕ, ∀ p ∈ S,
      ‖doubleSummand m α i.1 i.2 p.1 p.2‖ ≤ M i := by
  obtain ⟨Q₀, Q, a₀, b₀, -, -, hQ1, ha₀, hab, hb⟩ :=
    compact_q_u_bounds S hS (hSD.trans Set.sdiff_subset)
  obtain ⟨A, hA0, hA⟩ := denominator_bound α hα0 hα1 S hS hSD
  set Q' := max Q 0 with hQ'
  have hQ0 : 0 ≤ Q' := le_max_right _ _
  have hQ1' : Q' < 1 := max_lt hQ1 one_pos
  have hq : ∀ p ∈ S, ‖e p.1‖ ≤ Q' := fun p hp => le_max_of_le_left (hb p hp).2.1
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm hQ0 hQ1' zero_le_one
  set c := max b₀ a₀⁻¹ with hc
  have hc1 : 1 ≤ c := by
    rcases le_or_gt 1 b₀ with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_lt_inv₀ ha₀).mpr (hab.trans_lt h)).le
  set V := c ^ (2 * m) with hV
  have hV1 : 1 ≤ V := one_le_pow₀ hc1
  have hG := gaussian_summable (m := m) (by omega) hQ0 hQ1' hV1
  have hK : Summable fun k : ℕ => Q' ^ (k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => pow_nonneg hQ0 _)
      (fun k => pow_le_pow_of_le_one hQ0 hQ1'.le (Nat.le_self_pow two_ne_zero k))
      (summable_geometric_of_lt_one hQ0 hQ1')
  have hx : ‖e (α : ℂ)‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  refine ⟨fun i => A * C * (Q' ^ (m * i.1.natAbs ^ 2) * V ^ i.1.natAbs * Q' ^ (i.2 ^ 2)),
    ((hG.mul_of_nonneg hK (fun n => by positivity) (fun k => by positivity)).mul_left
      (A * C)).congr fun i => by ring,
    fun i => by positivity, fun ⟨n, k⟩ p hp => ?_⟩
  obtain ⟨ha, hb'⟩ := (hb p hp).2.2
  have hu0 : 0 < ‖e p.2‖ := ha₀.trans_le ha
  have hexp : (m : ℤ) * n ^ 2 + (k : ℤ) ^ 2 = ((m * n.natAbs ^ 2 + k ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs]
  have hu : ‖e p.2‖ ^ (2 * (m : ℤ) * n) ≤ V ^ n.natAbs := by
    refine (doubleSeriesNormal_zpow_le (c := c) hu0 (le_max_of_le_left hb')
      (le_max_of_le_right (inv_anti₀ ha₀ ha)) _).trans_eq ?_
    rw [hV, ← pow_mul]
    congr 1
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp
  have hqp := hq p hp
  have hg := hC k _ (hq p hp) _ hx.le
  have hd := hA p hp (n + k)
  simp only [doubleSummand]
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
    norm_pow, norm_zpow, norm_zpow, norm_zpow, hx, hexp, zpow_natCast]
  simp only [one_pow, inv_one, one_zpow, one_mul]
  calc ‖e p.1‖ ^ (m * n.natAbs ^ 2 + k ^ 2) * ‖e p.2‖ ^ (2 * (m : ℤ) * n) *
        ‖gTail m (e α) k (e p.1)‖ * ‖1 - e α * e p.2 * e p.1 ^ (n + k)‖⁻¹
      ≤ (Q' ^ (m * n.natAbs ^ 2) * Q' ^ (k ^ 2)) * V ^ n.natAbs * C * A := by
        rw [pow_add]
        gcongr
    _ = A * C * (Q' ^ (m * n.natAbs ^ 2) * V ^ n.natAbs * Q' ^ (k ^ 2)) := by ring

/-- **Normal convergence of the double series.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`x = e(α)` and a compact `S ⊆ (ℍ × ℂ) \ 𝒟_x`,
`∑_{(n,k) ∈ ℤ × ℕ} sup_{(τ,w) ∈ S} |ℰ^{dbl}_{n,k}(τ,w)| < ∞`. -/
theorem double_series_normal {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∑' i : ℤ × ℕ, ⨆ p ∈ S, (‖doubleSummand m α i.1 i.2 p.1 p.2‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := doubleSeriesNormal_exists_majorant hm α hα0 hα1 S hS hSD
  calc ∑' i : ℤ × ℕ, ⨆ p ∈ S, (‖doubleSummand m α i.1 i.2 p.1 p.2‖₊ : ℝ≥0∞)
      ≤ ∑' i : ℤ × ℕ, ENNReal.ofReal (M i) := by
        refine ENNReal.tsum_le_tsum fun i => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle i p hp)
    _ = ENNReal.ofReal (∑' i, M i) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
