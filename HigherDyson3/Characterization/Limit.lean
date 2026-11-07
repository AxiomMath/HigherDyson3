/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.SolutionSpace

/-!
# The Dyson sequence is the unique solution tending to `1`

For `m ≥ 2`, `|x| = 1` and `0 < |q| < 1`, the Dyson sequence `X_j(x;q)/G_d(x;q)` lies in `V_1`
and tends to `1`; conversely every `Y ∈ V_γ` with `Y_j → 1` is the Dyson sequence, and `γ = 1`
unless `C_x = 0` [AOS, Theorem 7.1(i)].

## Main results

* `HigherDyson3.norm_dysonSequence_sub_one_le`: `X_j/G_d = 1 + O(|q|^{j+1})`.
* `HigherDyson3.tendsto_dysonSequence`: `X_j/G_d → 1`.
* `HigherDyson3.eq_dysonSequence_of_tendsto`: the converse.
* `HigherDyson3.tendsto_one_iff_eq_dysonSequence`: uniqueness in `V`.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ} {x q : ℂ}

/-- `X_j(x;q)/G_d(x;q) = 1 + O(|q|^{j+1})`: for `0 ≤ Q < 1` and `0 < |q| ≤ Q`,
`|X_j/G_d - 1| ≤ B'_Q/(1-Q) |q|^{j+1}` [AOS, proof of Theorem 7.1(i)]. -/
theorem norm_dysonSequence_sub_one_le (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) {Q : ℝ}
    (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hq : ‖q‖ ≤ Q) (j : ℕ) :
    ‖XSeries m x j q / GProduct m x q - 1‖ ≤ hRatioBound m Q / (1 - Q) * ‖q‖ ^ (j + 1) := by
  have h := norm_lambertSolution_sub_le (m := m) hQ0 hQ1 hx hx hq0 hq j
  rwa [div_self (ne_zero_of_norm_eq_one hx), one_zpow, one_mul,
    lambertSolution_self hm hx (hq.trans_lt hQ1)] at h

/-- **Theorem 7.1(i), first part.** The Dyson sequence tends to `1` [AOS, Theorem 7.1(i)]. -/
theorem tendsto_dysonSequence (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    Tendsto (fun j : ℕ => XSeries m x j q / GProduct m x q) atTop (𝓝 1) := by
  have h := tendsto_lambertSolution_sub_pow (m := m) hx hx hq0 hq1
  simp only [div_self (ne_zero_of_norm_eq_one hx), one_pow, lambertSolution_self hm hx hq1] at h
  simpa using h.add_const 1

/-- **Theorem 7.1(i), membership and limit.** `X(x;q)/G_d(x;q) ∈ V_1` and tends to `1`
[AOS, Theorem 7.1(i)]. -/
theorem dysonSequence_mem_and_tendsto (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) :
    (fun j : ℕ => XSeries m x j q / GProduct m x q) ∈ recurrenceFamily m x q 1 ∧
      Tendsto (fun j : ℕ => XSeries m x j q / GProduct m x q) atTop (𝓝 1) :=
  ⟨dysonSequence_mem hm hx hq0 hq1, tendsto_dysonSequence hm hx hq0 hq1⟩

/-- If `Y ∈ V_γ` and `Y_j → 1`, then `C_x γ = C_x`. -/
theorem Cx_mul_eq_of_tendsto {γ : ℂ} {Y : ℕ → ℂ} (hq1 : ‖q‖ < 1)
    (hY : Y ∈ recurrenceFamily m x q γ) (hlim : Tendsto Y atTop (𝓝 1)) :
    Cx m x * γ = Cx m x := by
  have hshift : ∀ r : ℕ, Tendsto (fun j : ℕ => Y (j + r - 2)) atTop (𝓝 1) := fun r =>
    hlim.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + 2, fun j hj => by omega⟩)
  have hpow : Tendsto (fun j : ℕ => q ^ (j - 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1).comp
      (tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun j hj => by omega⟩)
  have hL : Tendsto (fun j : ℕ => ∑ r ∈ range (2 * m + 1), x ^ r * Y (j + r - 2) -
      q ^ (j - 1) * Y j) atTop (𝓝 (Cx m x)) := by
    have := (tendsto_finsetSum (range (2 * m + 1)) fun r _ => (hshift r).const_mul (x ^ r)).sub
      (hpow.mul hlim)
    simpa [Cx, cyclotomicSum] using this
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hL
  filter_upwards [eventually_ge_atTop 2] with j hj
  exact (hY j hj).symm

/-- **Theorem 7.1(i), converse.** If `Y ∈ V_γ` and `Y_j → 1`, then `Y_j = X_j(x;q)/G_d(x;q)` for
all `j`, and `γ = 1` unless `C_x = 0` [AOS, Theorem 7.1(i)]. -/
theorem eq_dysonSequence_of_tendsto (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {γ : ℂ} {Y : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ) (hlim : Tendsto Y atTop (𝓝 1)) :
    Y = (fun j : ℕ => XSeries m x j q / GProduct m x q) ∧ (Cx m x ≠ 0 → γ = 1) := by
  have hγ : Cx m x ≠ 0 → γ = 1 := fun h =>
    mul_left_cancel₀ h ((Cx_mul_eq_of_tendsto hq1 hY hlim).trans (mul_one _).symm)
  refine ⟨?_, hγ⟩
  have hD := dysonSequence_mem hm hx hq0 hq1
  have hW : Y - (fun j : ℕ => XSeries m x j q / GProduct m x q) ∈ recurrenceFamily m x q 0 := by
    by_cases h : Cx m x = 0
    · rw [recurrenceFamily_eq_of_Cx_eq_zero h] at hY hD
      exact mem_recurrenceKernel.mp (sub_mem_recurrenceKernel hY hD)
    · rw [hγ h] at hY
      exact mem_recurrenceKernel.mp (sub_mem_recurrenceKernel hY hD)
  have hlim' := hlim.sub (tendsto_dysonSequence hm hx hq0 hq1)
  rw [sub_self] at hlim'
  have h0 := eq_zero_of_tendsto_zero hm hx hq0 hq1 hW hlim'
  exact sub_eq_zero.mp h0

/-- **Theorem 7.1(i), uniqueness.** `X(x;q)/G_d(x;q)` is the unique sequence in
`V = ⋃_γ V_γ` tending to `1`; this includes the case `C_x = 0` [AOS, Theorem 7.1(i)]. -/
theorem tendsto_one_iff_eq_dysonSequence (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) :
    Tendsto Y atTop (𝓝 1) ↔ Y = fun j : ℕ => XSeries m x j q / GProduct m x q := by
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hY
  constructor
  · exact fun h => (eq_dysonSequence_of_tendsto hm hx hq0 hq1 hγ h).1
  · rintro rfl
    exact tendsto_dysonSequence hm hx hq0 hq1

end HigherDyson3
