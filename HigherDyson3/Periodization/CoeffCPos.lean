/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCNormal
public import HigherDyson3.Product.GPosReal

/-!
# Positivity of `C_{m,ℓ,1}` on the imaginary axis

Let `m ≥ 2`, `0 ≤ ℓ < 2m` and `t > 0`. Then `C_{m,ℓ,1}(it)` is a positive real number.

At `τ = it` the nome `q = e(it) = exp(-2πt)` is real with `0 < q < 1`, and `x = e(0) = 1`, so
`C_{m,ℓ,1}(it) = ∑_{k ≥ 1} c_k` with `c_k = g_{k,1}(q) ∑_{s=1}^k q^{(m+1)k²-ms²+ℓs}`. Each
`g_{k,1}(q)` is a positive real by `HigherDyson3.gTail_one_pos`, so each `c_k` is a real
number, positive for `k ≥ 1`. The series converges by
`HigherDyson3.coeffCNormal_exists` on the compact set `{it}`, so its sum is real and at
least `c_1 > 0`.

## Main results

* `HigherDyson3.coeffC_pos`: `0 < C_{m,ℓ,1}(it)` for real `t > 0`.

## Implementation notes

Positivity is stated with the partial order on `ℂ`, in which `0 < z` means that `z` is real
and positive.
-/

public section

open Complex Finset

open scoped ComplexOrder

namespace HigherDyson3

/-- On the imaginary axis the nome is real: `e(it) = exp(-2πt)`. -/
private lemma coeffCPos_e_I_mul (t : ℝ) :
    e (I * t) = ((Real.exp (-2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold e
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **Positivity of `C` at `x = 1`.** For `m ≥ 2`, `0 ≤ ℓ < 2m` and real `t > 0`, the
coefficient `C_{m,ℓ,1}(it)` is a positive real number. -/
theorem coeffC_pos {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : ℓ < 2 * m) {t : ℝ} (ht : 0 < t) :
    0 < coeffC m ℓ 0 (I * t) := by
  set q : ℝ := Real.exp (-2 * Real.pi * t) with hq_def
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hx : e ((0 : ℚ) : ℂ) = 1 := by simp [e]
  have heq := coeffCPos_e_I_mul t
  rw [← hq_def] at heq
  -- the `k`-th term, as a real number
  set N : ℕ → ℕ → ℤ := fun k s => ((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s
  set c : ℕ → ℝ := fun k =>
    (gTail m 1 k (q : ℂ)).re * ∑ s ∈ Icc 1 k, q ^ N k s with hc
  have hg : ∀ k, gTail m 1 k (q : ℂ) = (((gTail m 1 k (q : ℂ)).re : ℝ) : ℂ) := fun k => by
    have := (Complex.pos_iff.mp (gTail_one_pos hm k hq0.le hq1))
    exact Complex.ext (by simp) (by simp [this.2])
  have hgre : ∀ k, 0 < (gTail m 1 k (q : ℂ)).re := fun k =>
    (Complex.pos_iff.mp (gTail_one_pos hm k hq0.le hq1)).1
  have hterm : ∀ k : ℕ, gTail m (e ((0 : ℚ) : ℂ)) k (e (I * t)) *
      ∑ s ∈ Icc 1 k, e ((0 : ℚ) : ℂ) ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e (I * t) ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s) = (c k : ℂ) := by
    intro k
    rw [hx, heq, hc]
    push_cast
    rw [← hg k]
    simp [N]
  have hc0 : ∀ k, 0 ≤ c k := fun k =>
    mul_nonneg (hgre k).le (Finset.sum_nonneg fun s _ => zpow_nonneg hq0.le _)
  have hc1 : 0 < c 1 := by
    refine mul_pos (hgre 1) ?_
    simp only [Finset.Icc_self, Finset.sum_singleton]
    exact zpow_pos hq0 _
  -- summability from the normal-convergence majorant on `{it}`
  have hS : ({I * t} : Set ℂ) ⊆ upperHalfPlaneSet := by
    intro τ hτ
    rw [Set.mem_singleton_iff.mp hτ]
    change 0 < (I * (t : ℂ)).im
    simpa using ht
  obtain ⟨u, hu, -, hle⟩ := coeffCNormal_exists hm le_rfl (by norm_num : (0 : ℚ) < 1)
    hℓ {I * t} isCompact_singleton hS
  have hcs : Summable c := by
    refine Summable.of_nonneg_of_le hc0 (fun k => ?_) hu
    have := hle k (I * t) rfl
    rw [hterm k, Complex.norm_real, Real.norm_of_nonneg (hc0 k)] at this
    exact this
  have hC : coeffC m ℓ 0 (I * t) = ((∑' k, c k : ℝ) : ℂ) := by
    unfold coeffC
    simp_rw [hterm]
    rw [hx, one_zpow, one_mul, Complex.ofReal_tsum]
  rw [hC, Complex.zero_lt_real]
  exact hc1.trans_le (hcs.le_tsum 1 fun j _ => hc0 j)

end HigherDyson3
