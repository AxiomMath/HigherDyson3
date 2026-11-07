/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# Uniqueness of the coefficients of a finite almost periodic sequence

If `μ_1, …, μ_n` are distinct complex numbers of modulus `1` and `∑_k s_k μ_k^j → 0` as
`j → ∞`, then all `s_k` vanish. This is the elementary case of the uniqueness theorem for the
Fourier coefficients of almost periodic sequences used in [AOS, proof of Lemma 7.3(b)]: the
Cesàro means `(1/N) ∑_{j<N} μ_{k'}^{-j} ∑_k s_k μ_k^j` tend to `s_{k'}`, because
`(1/N) ∑_{j<N} μ^j → 0` for `|μ| = 1`, `μ ≠ 1`, and they tend to `0` by hypothesis.

## Main results

* `HigherDyson3.tendsto_cesaro_pow`: `(1/N) ∑_{j<N} μ^j → 0` for `|μ| = 1`, `μ ≠ 1`.
* `HigherDyson3.eq_zero_of_tendsto_sum_mul_pow`: the uniqueness statement.
-/

public section

open Finset Filter Topology

namespace HigherDyson3

/-- For `|μ| = 1` and `μ ≠ 1`, the Cesàro means `(1/N) ∑_{j<N} μ^j` tend to `0`. -/
theorem tendsto_cesaro_pow {μ : ℂ} (hμ : ‖μ‖ = 1) (h1 : μ ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, μ ^ j) atTop (𝓝 0) := by
  have hμ1 : 0 < ‖μ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  refine squeeze_zero_norm (a := fun N : ℕ => 2 / ‖μ - 1‖ / (N : ℝ)) (fun N => ?_) ?_
  · have h2 : ‖μ ^ N - 1‖ ≤ 2 := by
      calc ‖μ ^ N - 1‖ ≤ ‖μ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hμ, one_pow, norm_one]; norm_num
    rw [geom_sum_eq h1, norm_mul, norm_div, norm_inv, Complex.norm_natCast, mul_comm,
      ← div_eq_mul_inv]
    gcongr
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- The Cesàro means of the constant sequence `1` tend to `1`. -/
theorem tendsto_cesaro_one :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, (1 : ℂ) ^ j) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  simp [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)]

/-- **Uniqueness of almost periodic coefficients.** If `μ_k` are distinct of modulus `1` and
`∑_k s_k μ_k^j → 0`, then `s = 0` [AOS, proof of Lemma 7.3(b)]. -/
theorem eq_zero_of_tendsto_sum_mul_pow {ι : Type*} [Fintype ι] {μ : ι → ℂ}
    (hμ : Function.Injective μ) (hnorm : ∀ i, ‖μ i‖ = 1) {s : ι → ℂ}
    (h : Tendsto (fun j : ℕ => ∑ i, s i * μ i ^ j) atTop (𝓝 0)) : s = 0 := by
  classical
  funext i₀
  have h0 : μ i₀ ≠ 0 := fun h => by simpa [h] using hnorm i₀
  set v : ℕ → ℂ := fun j => ∑ i, s i * (μ i / μ i₀) ^ j with hv
  have hvj : ∀ j, v j = (μ i₀ ^ j)⁻¹ * ∑ i, s i * μ i ^ j := fun j => by
    rw [hv, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [div_pow]
    ring
  have hv0 : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
    refine h.congr fun j => ?_
    rw [hvj, norm_mul, norm_inv, norm_pow, hnorm, one_pow, inv_one, one_mul]
  have hc := hv0.cesaro_smul
  have hc' : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, v j) atTop (𝓝 0) := by
    refine hc.congr fun N => ?_
    rw [Complex.real_smul]
    push_cast
    rfl
  have hlim : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, v j) atTop (𝓝 (s i₀)) := by
    have hterm : ∀ i, Tendsto (fun N : ℕ => s i * ((N : ℂ)⁻¹ * ∑ j ∈ range N, (μ i / μ i₀) ^ j))
        atTop (𝓝 (if i = i₀ then s i₀ else 0)) := fun i => by
      split_ifs with hi
      · subst hi
        simpa [div_self h0] using tendsto_cesaro_one.const_mul (s i)
      · have hne : μ i / μ i₀ ≠ 1 := fun he => hi (hμ ((div_eq_one_iff_eq h0).mp he))
        have hn : ‖μ i / μ i₀‖ = 1 := by rw [norm_div, hnorm, hnorm, div_one]
        simpa using (tendsto_cesaro_pow hn hne).const_mul (s i)
    have := tendsto_finsetSum (univ : Finset ι) fun i _ => hterm i
    simp only [sum_ite_eq', mem_univ, ↓reduceIte] at this
    refine this.congr fun N => ?_
    rw [hv]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  exact tendsto_nhds_unique hlim hc'

end HigherDyson3
