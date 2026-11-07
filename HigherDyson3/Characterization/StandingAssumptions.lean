/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Limit
public import HigherDyson3.Characterization.SeedContinuation

/-!
# Theorem 7.1(i) and (ii)(a) under the standing assumptions of [AOS, §7]

The results of `HigherDyson3.Characterization.Limit` and
`HigherDyson3.Characterization.SeedContinuation` hold for every `|x| = 1` and `0 < |q| < 1`.
Here they are restated for `x = e(α)` with `α ∈ ℚ` and `q = e(τ)` with `τ ∈ ℍ`, as in
[AOS, §7].
-/

public section

noncomputable section

open Filter Topology

namespace HigherDyson3

variable {m : ℕ}

private theorem norm_e_rat (α : ℚ) : ‖e (α : ℂ)‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

private theorem e_ne_zero (τ : ℂ) : e τ ≠ 0 := Complex.exp_ne_zero _

private theorem norm_e_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖e τ‖ < 1 := by
  unfold e
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [Real.pi_pos]

/-- **Theorem 7.1(i)** [AOS, Theorem 7.1(i)]. Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ` and
`q = e(τ)` with `τ ∈ ℍ`. The sequence `Y_j = X_j(x;q)/G_d(x;q)` belongs to `V_1` and tends to
`1`; conversely, if `Y ∈ V_γ` and `Y_j → 1`, then `Y_j = X_j(x;q)/G_d(x;q)` for all `j ≥ 0` and
`γ = 1` unless `C_x = 0`. -/
theorem dysonSequence_limit_characterization (hm : 2 ≤ m) (α : ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    ((fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∈
        recurrenceFamily m (e α) (e τ) 1 ∧
      Tendsto (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) atTop (𝓝 1)) ∧
    ∀ (γ : ℂ) (Y : ℕ → ℂ), Y ∈ recurrenceFamily m (e α) (e τ) γ → Tendsto Y atTop (𝓝 1) →
      Y = (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∧
        (Cx m (e α) ≠ 0 → γ = 1) :=
  ⟨dysonSequence_mem_and_tendsto hm (norm_e_rat α) (e_ne_zero τ) (norm_e_lt_one hτ),
    fun _ _ hY hlim =>
      eq_dysonSequence_of_tendsto hm (norm_e_rat α) (e_ne_zero τ) (norm_e_lt_one hτ) hY hlim⟩

/-- **Theorem 7.1(ii)(a)** [AOS, Theorem 7.1(ii)(a)]. Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ`,
`q = e(τ)` with `τ ∈ ℍ`, and `Y ∈ V`. The seed `𝒢_Y(u)` converges for `|u| < 1` and extends to a
meromorphic function on `ℂ` with at most simple poles, all contained in
`{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d - 1}`. -/
theorem solution_seed_continuation_e (hm : 2 ≤ m) (α : ℚ) {τ : ℂ} (hτ : 0 < τ.im)
    {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m (e α) (e τ)) :
    (∀ u : ℂ, ‖u‖ < 1 → Summable fun j : ℕ => Y j * (e α * u) ^ j) ∧
      ∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ :=
  solution_seed_continuation hm (norm_e_rat α) (e_ne_zero τ) (norm_e_lt_one hτ) hY

end HigherDyson3
