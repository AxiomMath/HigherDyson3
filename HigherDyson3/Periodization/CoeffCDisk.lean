/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GHolomorphic
public import HigherDyson3.Product.GBound
public import HigherDyson3.Definitions

/-!
# The theta coefficients `C_{m,ℓ,x}` as functions of `q`

The series `C_{m,ℓ,x}(q) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)}
q^{(m+1)k² - ms² + ℓs}` converges normally on compact subsets of the whole disc `|q| < 1`,
including `q = 0`, and defines a holomorphic function there; `C_{m,ℓ,x}(τ)` is its value at
`q = e(τ)` [AOS, Proposition 6.1].
-/

public section

open Complex Finset

namespace HigherDyson3

/-- The `k`-th term `g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k² - ms² + ℓs}` of `C_{m,ℓ,x}`
as a function of `q`; the exponent is a natural number since `s ≤ k`. -/
noncomputable def coeffCqTerm (m ℓ : ℕ) (x : ℂ) (k : ℕ) (q : ℂ) : ℂ :=
  gTail m x k q *
    ∑ s ∈ Icc 1 k, x ^ (2 * (m + 1) * (k - s)) * q ^ ((m + 1) * k ^ 2 + ℓ * s - m * s ^ 2)

/-- `C_{m,ℓ,x}(q) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`,
as a function of `q` [AOS, (6.2)]. -/
noncomputable def coeffCq (m ℓ : ℕ) (x q : ℂ) : ℂ :=
  x ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, coeffCqTerm m ℓ x k q

theorem coeffCq_def (m ℓ : ℕ) (x q : ℂ) :
    coeffCq m ℓ x q = x ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, coeffCqTerm m ℓ x k q := (rfl)

theorem coeffCqTerm_exponent {m ℓ k s : ℕ} (hs : s ∈ Icc 1 k) :
    k ^ 2 ≤ (m + 1) * k ^ 2 + ℓ * s - m * s ^ 2 := by
  have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
  have : m * s ^ 2 ≤ m * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsk 2)
  have h2 : (m + 1) * k ^ 2 = m * k ^ 2 + k ^ 2 := by ring
  omega

/-- **Normal convergence on compact subsets of the disc** [AOS, Proposition 6.1]: for `‖x‖ = 1`
and `‖q‖ ≤ Q < 1`, the `k`-th term of `C_{m,ℓ,x}` is bounded by `B k Q^k`. -/
theorem exists_bound_coeffCqTerm {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {x : ℂ} (hx : ‖x‖ = 1) {Q : ℝ}
    (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ k : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q → ‖coeffCqTerm m ℓ x k q‖ ≤ M k := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm hQ0 hQ1 (B := 1) zero_le_one
  refine ⟨fun k => C * (k * Q ^ k), ?_, fun k q hq => ?_⟩
  · have := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖Q‖ < 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hQ0]; exact hQ1)
    simpa using this.mul_left C
  have hq1 : ‖q‖ ≤ 1 := hq.trans hQ1.le
  rw [coeffCqTerm, norm_mul]
  refine mul_le_mul (hC k q hq x hx.le) ?_ (norm_nonneg _) hC0
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ s ∈ Icc 1 k, ‖x ^ (2 * (m + 1) * (k - s)) *
      q ^ ((m + 1) * k ^ 2 + ℓ * s - m * s ^ 2)‖ ≤ Q ^ k := by
    intro s hs
    rw [norm_mul, norm_pow, norm_pow, hx, one_pow, one_mul]
    calc ‖q‖ ^ ((m + 1) * k ^ 2 + ℓ * s - m * s ^ 2) ≤ ‖q‖ ^ (k ^ 2) :=
          pow_le_pow_of_le_one (norm_nonneg _) hq1 (coeffCqTerm_exponent hs)
      _ ≤ ‖q‖ ^ k := pow_le_pow_of_le_one (norm_nonneg _) hq1 (by nlinarith)
      _ ≤ Q ^ k := pow_le_pow_left₀ (norm_nonneg _) hq _
  refine (Finset.sum_le_sum hterm).trans ?_
  simp

/-- **Holomorphy of `C_{m,ℓ,x}` on the whole disc `|q| < 1`, including `q = 0`**
[AOS, Proposition 6.1]. -/
theorem differentiableOn_coeffCq {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {x : ℂ} (hx : ‖x‖ = 1) :
    DifferentiableOn ℂ (coeffCq m ℓ x) (Metric.ball 0 1) := by
  intro q₀ hq₀
  have hq₀' : ‖q₀‖ < 1 := mem_ball_zero_iff.mp hq₀
  set Q : ℝ := (‖q₀‖ + 1) / 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQ1 : Q < 1 := by rw [hQ]; linarith
  have hq₀Q : ‖q₀‖ < Q := by rw [hQ]; linarith
  obtain ⟨M, hMs, hM⟩ := exists_bound_coeffCqTerm hm ℓ hx hQ0 hQ1
  have hd : DifferentiableOn ℂ (fun q => ∑' k : ℕ, coeffCqTerm m ℓ x k q) (Metric.ball 0 Q) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hMs (fun k => ?_) Metric.isOpen_ball
      (fun k q hq => hM k q (mem_ball_zero_iff.mp hq).le)
    refine ((differentiableOn_gTail hm x k).mono fun q hq => ?_).mul ?_
    · exact mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hq).trans hQ1)
    · exact DifferentiableOn.fun_sum fun s _ => (differentiableOn_const _).mul
        (differentiableOn_id.pow _)
  have hball : Metric.ball (0 : ℂ) Q ∈ nhds q₀ :=
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq₀Q)
  exact (((differentiableOn_const _).mul hd).differentiableAt hball).differentiableWithinAt

/-- `C_{m,ℓ,x}(τ)` is the value of `C_{m,ℓ,x}(q)` at `q = e(τ)`, `x = e(α)`. -/
theorem coeffC_eq_coeffCq (m ℓ : ℕ) (α : ℚ) (τ : ℂ) :
    coeffC m ℓ α τ = coeffCq m ℓ (e α) (e τ) := by
  rw [coeffC, coeffCq]
  congr 1
  refine tsum_congr fun k => ?_
  rw [coeffCqTerm]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
  have h1 : (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) = ((2 * (m + 1) * (k - s) : ℕ) : ℤ) := by
    push_cast [hsk]; ring
  have h2 : (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s) =
      (((m + 1) * k ^ 2 + ℓ * s - m * s ^ 2 : ℕ) : ℤ) := by
    have := coeffCqTerm_exponent (m := m) (ℓ := ℓ) hs
    have h3 : m * s ^ 2 ≤ (m + 1) * k ^ 2 + ℓ * s := by
      have : m * s ^ 2 ≤ m * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsk 2)
      nlinarith
    push_cast [h3]; ring
  rw [h1, h2, zpow_natCast, zpow_natCast]

end HigherDyson3
