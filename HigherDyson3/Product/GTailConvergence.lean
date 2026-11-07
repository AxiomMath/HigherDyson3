/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GLeading

/-!
# Convergence of the tails `g_{k,x} → 1`

For every `x ∈ ℂ`, the tails `g_{k,x}(q) = G_d(x q^k; q)` tend to `1` locally uniformly on
`|q| < 1` as `k → ∞` [AOS, Lemma 5.1].
-/

public section

open Complex Finset Filter Topology

namespace HigherDyson3

/-- `‖g_{k,x}(q) - 1‖ ≤ exp(S Q^{k+1}/(1-Q)) - 1` for `‖q‖ ≤ Q < 1`, where
`S = ∑_{s=1}^{d-1} ‖x‖^s`. -/
theorem norm_gTail_sub_one_le_exp {m : ℕ} (x : ℂ) (k : ℕ) {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    {q : ℂ} (hq : ‖q‖ ≤ Q) :
    ‖gTail m x k q - 1‖ ≤
      Real.exp ((∑ s ∈ range (2 * m), ‖x‖ ^ (s + 1)) * Q ^ (k + 1) / (1 - Q)) - 1 := by
  set S : ℝ := ∑ s ∈ range (2 * m), ‖x‖ ^ (s + 1) with hS
  have hS0 : 0 ≤ S := sum_nonneg fun s _ => by positivity
  set a : ℕ → ℂ := fun r => cyclotomicSum m (x * q ^ k * q ^ (r + 1)) - 1 with ha
  have hq1 : ‖q‖ ≤ 1 := hq.trans hQ1.le
  have hbound : ∀ r, ‖a r‖ ≤ S * Q ^ (k + 1) * Q ^ r := by
    intro r
    have h1 : ‖a r‖ ≤ ∑ s ∈ range (2 * m), ‖x * q ^ k * q ^ (r + 1)‖ ^ (s + 1) := by
      rw [show a r = ∑ s ∈ range (2 * m), (x * q ^ k * q ^ (r + 1)) ^ (s + 1) by
        simp [ha, cyclotomicSum, sum_range_succ']]
      exact (norm_sum_le _ _).trans_eq (by simp [norm_pow])
    refine h1.trans ?_
    rw [hS, sum_mul, sum_mul]
    refine sum_le_sum fun s _ => ?_
    have hy : ‖x * q ^ k * q ^ (r + 1)‖ = ‖x‖ * ‖q‖ ^ (k + 1 + r) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc, ← pow_add]
      ring_nf
    rw [hy, mul_pow]
    have hqp : (‖q‖ ^ (k + 1 + r)) ^ (s + 1) ≤ Q ^ (k + 1) * Q ^ r := by
      calc (‖q‖ ^ (k + 1 + r)) ^ (s + 1) ≤ ‖q‖ ^ (k + 1 + r) :=
            pow_le_of_le_one (by positivity) (pow_le_one₀ (norm_nonneg _) hq1) (by omega)
        _ ≤ Q ^ (k + 1 + r) := pow_le_pow_left₀ (norm_nonneg _) hq _
        _ = Q ^ (k + 1) * Q ^ r := pow_add _ _ _
    calc ‖x‖ ^ (s + 1) * (‖q‖ ^ (k + 1 + r)) ^ (s + 1) ≤ ‖x‖ ^ (s + 1) * (Q ^ (k + 1) * Q ^ r) :=
          mul_le_mul_of_nonneg_left hqp (by positivity)
      _ = ‖x‖ ^ (s + 1) * Q ^ (k + 1) * Q ^ r := by ring
  have hgeom : Summable fun r : ℕ => S * Q ^ (k + 1) * Q ^ r :=
    (summable_geometric_of_lt_one hQ0 hQ1).mul_left _
  have hsum : Summable fun r => ‖a r‖ := hgeom.of_nonneg_of_le (fun r => norm_nonneg _) hbound
  have htsum : ∑' r, ‖a r‖ ≤ S * Q ^ (k + 1) / (1 - Q) := by
    refine (hsum.tsum_le_tsum hbound hgeom).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hQ0 hQ1, div_eq_mul_inv]
  have hg : gTail m x k q = ∏' r, (1 + a r) := by
    simp [gTail, GProduct, ha]
  calc ‖gTail m x k q - 1‖ ≤ Real.exp (∑' r, ‖a r‖) - 1 :=
        hg ▸ norm_tprod_one_add_sub_one_le hsum
    _ ≤ Real.exp (S * Q ^ (k + 1) / (1 - Q)) - 1 := by gcongr

/-- **The tails tend to `1` uniformly on `|q| ≤ Q`** for every `Q < 1`. -/
theorem tendstoUniformlyOn_gTail {m : ℕ} (x : ℂ) {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    TendstoUniformlyOn (fun k => gTail m x k) (fun _ => 1) atTop (Metric.closedBall 0 Q) := by
  set S : ℝ := ∑ s ∈ range (2 * m), ‖x‖ ^ (s + 1)
  have hlim : Tendsto (fun k : ℕ => Real.exp (S * Q ^ (k + 1) / (1 - Q)) - 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => S * Q ^ (k + 1) / (1 - Q)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hQ0 hQ1).comp (tendsto_add_atTop_nat 1))
      simpa using (this.const_mul S).div_const (1 - Q)
    have h2 := (Real.continuous_exp.tendsto 0).comp h1
    simpa using h2.sub_const 1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(hlim.eventually (gt_mem_nhds hε))] with k hk q hq
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (norm_gTail_sub_one_le_exp x k hQ0 hQ1 (mem_closedBall_zero_iff.mp hq)) hk

/-- **The tails tend to `1` locally uniformly** on `|q| < 1` [AOS, Lemma 5.1]. -/
theorem tendstoLocallyUniformlyOn_gTail {m : ℕ} (x : ℂ) :
    TendstoLocallyUniformlyOn (fun k => gTail m x k) (fun _ => 1) atTop (Metric.ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with h | h
  · rw [h]; exact tendstoUniformlyOn_empty
  obtain ⟨z, hz, hmax⟩ := hKc.exists_isMaxOn h continuous_norm.continuousOn
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hK hz)
  refine (tendstoUniformlyOn_gTail x (norm_nonneg z) hz1).mono fun q hq => ?_
  exact mem_closedBall_zero_iff.mpr (hmax hq)

end HigherDyson3
