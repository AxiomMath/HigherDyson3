/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.PeriodizationDouble
public import HigherDyson3.Periodization.LayerIdentity
public import HigherDyson3.Periodization.RhoNormal
public import HigherDyson3.Periodization.CoeffCNormal

/-!
# Decomposition of the periodization

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`,
`ℰ_{m,x}(τ,w) = ρ_{m,x}(τ) 𝒦_{m,x}(τ,w) + ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ,w)`.

The periodization is the sum of the absolutely summable double family `ℰ^{dbl}_{n,k}(τ,w)`
over `ℤ × ℕ` (`HigherDyson3.periodization_double`), so it may be summed first over `n ∈ ℤ`
and then over `k ∈ ℕ`. For fixed `k` the sum over `n` is `x⁻² q^{k²} g_{k,x}(q)` times the
shifted kernel series, which the layer identity (`HigherDyson3.layer_identity`) writes as
`a_k 𝒦_{m,x}(τ,w) + ∑_ℓ c_{ℓ,k} T^{[x]}_{m,ℓ}(τ,w)`. The series `∑_k a_k` and `∑_k c_{ℓ,k}`
converge absolutely (`HigherDyson3.rho_normal`, `HigherDyson3.coeffC_normal` on the
singleton `{τ}`) with sums `ρ_{m,x}(τ)` and `C_{m,ℓ,x}(τ)`; summing the finitely many pieces
separately gives the decomposition.

## Main results

* `HigherDyson3.periodization_decomposition`: the decomposition of `ℰ_{m,x}` into the kernel
  and the twisted theta series.
-/

public section

open Finset
open scoped ENNReal

namespace HigherDyson3

/-- A series whose normal sum over a singleton is finite is summable. -/
private lemma periodizationDecomposition_summable_of_singleton {f : ℕ → ℂ → ℂ} {τ : ℂ}
    (h : ∑' k : ℕ, ⨆ σ ∈ ({τ} : Set ℂ), (‖f k σ‖₊ : ℝ≥0∞) < ∞) :
    Summable (fun k => f k τ) := by
  simp only [_root_.iSup_singleton] at h
  exact Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.mp h.ne)

/-- **Decomposition of the periodization.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, `x = e(α)`,
`ℰ_{m,x}(τ,w) = ρ_{m,x}(τ) 𝒦_{m,x}(τ,w) + ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ,w)`. -/
theorem periodization_decomposition {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) :
    periodization m α τ w = rho m α τ * kernel m α τ w +
      ∑ ℓ ∈ range (2 * m), coeffC m ℓ α τ * twistedTheta m ℓ α τ w := by
  have hx : e α ≠ 0 := Complex.exp_ne_zero _
  have hq : e τ ≠ 0 := Complex.exp_ne_zero _
  have hτ : ({τ} : Set ℂ) ⊆ upperHalfPlaneSet :=
    Set.singleton_subset_iff.mpr hτw.1
  obtain ⟨hsum, hper⟩ := periodization_double hm hα0 hα1 hτw
  -- the iterated sum, first over `n ∈ ℤ`, then over `k ∈ ℕ`
  have hswap : Summable (fun p : ℕ × ℤ => doubleSummand m α p.2 p.1 τ w) :=
    (hsum.of_norm.comp_injective (Equiv.prodComm ℕ ℤ).injective :)
  have hiter : periodization m α τ w = ∑' k : ℕ, ∑' n : ℤ, doubleSummand m α n k τ w := by
    rw [hper, ← (Equiv.prodComm ℕ ℤ).tsum_eq]
    exact hswap.tsum_prod' hswap.prod_factor
  -- the layer identity for each `k`
  have hlayer : ∀ k : ℕ, ∑' n : ℤ, doubleSummand m α n k τ w =
      (e α ^ 2)⁻¹ * (e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
          gTail m (e α) k (e τ)) * kernel m α τ w +
        ∑ ℓ ∈ range (2 * m), e α ^ ((ℓ : ℤ) - 2) * (gTail m (e α) k (e τ) *
          ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
            e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)) *
          twistedTheta m ℓ α τ w := by
    intro k
    have hterm : ∀ n : ℤ, doubleSummand m α n k τ w =
        (e α ^ 2)⁻¹ * e τ ^ (k ^ 2) * gTail m (e α) k (e τ) *
          (e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) /
            (1 - e α * e w * e τ ^ (n + k))) := by
      intro n
      simp only [doubleSummand]
      rw [zpow_add₀ hq, ← zpow_natCast (e τ) (k ^ 2)]
      push_cast
      ring
    rw [tsum_congr hterm, tsum_mul_left,
      (layer_identity (by omega) α hα0 hα1 hτw k).2, mul_add, mul_sum]
    congr 1
    · have h1 : e α ^ (2 * (m + 1) * k) = e α ^ (2 * ((m : ℤ) + 1) * k) := by
        rw [← zpow_natCast]; push_cast; ring_nf
      have h2 : e τ ^ ((m + 1) * k ^ 2) = e τ ^ ((m : ℤ) * k ^ 2) * e τ ^ (k ^ 2) := by
        rw [← zpow_natCast, ← zpow_natCast (e τ) (k ^ 2), ← zpow_add₀ hq]; push_cast; ring_nf
      rw [h1, h2]
      ring
    · refine sum_congr rfl fun ℓ _ => ?_
      simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun s _ => ?_
      rw [show ((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s =
        m * k ^ 2 - m * s ^ 2 + ℓ * s + ((k ^ 2 : ℕ) : ℤ) by push_cast; ring]
      simp only [zpow_add₀ hx, zpow_sub₀ hx, zpow_add₀ hq, zpow_sub₀ hq, zpow_natCast]
      field_simp
  -- absolute convergence of the coefficient series
  have hrho : Summable (fun k : ℕ => e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
      gTail m (e α) k (e τ)) :=
    periodizationDecomposition_summable_of_singleton
      (f := fun k σ => e α ^ (2 * (m + 1) * k) * e σ ^ ((m + 1) * k ^ 2) *
        gTail m (e α) k (e σ))
      (rho_normal hm α {τ} isCompact_singleton hτ)
  have hC : ∀ ℓ ∈ range (2 * m), Summable (fun k : ℕ => e α ^ ((ℓ : ℤ) - 2) *
      (gTail m (e α) k (e τ) * ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)) *
      twistedTheta m ℓ α τ w) := by
    intro ℓ hℓ
    refine ((periodizationDecomposition_summable_of_singleton
      (f := fun k σ => gTail m (e α) k (e σ) *
        ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e σ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))
      (coeffC_normal hm hα0 hα1 (mem_range.mp hℓ) {τ} isCompact_singleton hτ)).mul_left
        _).mul_right _
  rw [hiter, tsum_congr hlayer, ((hrho.mul_left _).mul_right _).tsum_add
      (summable_sum hC), Summable.tsum_finsetSum hC, tsum_mul_right, tsum_mul_left]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  rw [tsum_mul_right, tsum_mul_left]
  rfl

end HigherDyson3
