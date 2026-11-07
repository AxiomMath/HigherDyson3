/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.RatioEstimates
public import HigherDyson3.Characterization.SolutionSpace
public import HigherDyson3.Lambert.DoubleSummand

/-!
# The residue functions of the eigen-solutions

For `1 ≤ k ≤ d - 1`, the seed of the eigen-solution `Z^{(k)}` is the Lambert seed with
`c = ω^k` and coefficients `b_i(ω^k)`, and its residue function is
`ρ^{(k)}(τ) = x⁻² ∑_{i ≥ 0} ω^{ki} q^{(m+1)i²} (ω^k q;q)_i / (q^d;q^d)_i` [AOS, Lemma 7.5].
The function `x² ρ^{(k)}` is holomorphic on `|q| < 1`, independent of `x`, equal to `1` at
`q = 0`, and `|x² ρ^{(k)} - 1| ≤ 3/7` for `|q| ≤ 1/2`. Consequently the exceptional set
`Ξ_m = ⋃_k {0 < |q| < 1 : ρ^{(k)} = 0}` is discrete in the punctured disc and disjoint from
`0 < |q| ≤ 1/2`.

The estimate uses `(m+1)i² ≥ 3i` and `|h_i(ω^k)| ≤ B'_{1/2} < 3`
(`HigherDyson3.norm_hRatio_le_three`), so `|x² ρ^{(k)} - 1| ≤ 3 ∑_{i ≥ 1} |q|^{3i}
= 3|q|³/(1 - |q|³) ≤ 3/7`. Discreteness follows from the identity theorem: each `x² ρ^{(k)}` is
holomorphic on the disc and equals `1` at `0`.

## Main results

* `HigherDyson3.lambertResidue_eigen`: the formula for `ρ^{(k)}`.
* `HigherDyson3.differentiableOn_eigenResidue`: holomorphy on the unit disc.
* `HigherDyson3.eigenResidue_zero`, `HigherDyson3.norm_eigenResidue_sub_one_le`,
  `HigherDyson3.norm_eigenResidue_sub_one_le_three_sevenths`: the leading term and the estimate.
* `HigherDyson3.eventually_not_mem_exceptionalSet`: `Ξ_m` is discrete in the punctured disc.
* `HigherDyson3.not_mem_exceptionalSet_of_norm_le_half`: `Ξ_m` misses `0 < |q| ≤ 1/2`.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

/-- `|ω| = 1`. -/
lemma norm_omega (m : ℕ) : ‖omega m‖ = 1 := by
  unfold omega
  have : (1 / (2 * m + 1 : ℂ)) = ((1 / (2 * m + 1 : ℚ) : ℚ) : ℂ) := by push_cast; ring
  rw [this, norm_e_ratCast]

/-- `ω^d = 1`. -/
lemma omega_pow_two_mul_add_one (m : ℕ) : omega m ^ (2 * m + 1) = 1 := by
  unfold omega
  have h : (2 * (m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m)
  rw [e_pow, show ((2 * m + 1 : ℕ) : ℂ) * (1 / (2 * m + 1 : ℂ)) = ((1 : ℤ) : ℂ) by
    push_cast; field_simp, e_intCast_eq_one]

/-- The terms of `x² ρ^{(k)}` in terms of the ratios `h_i(ω^k)`. -/
lemma eigenResidue_eq_tsum_hRatio (m k : ℕ) (q : ℂ) :
    eigenResidue m k q =
      ∑' i : ℕ, omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) * hRatio m (omega m ^ k) q i := by
  have hω : (omega m ^ k) ^ (2 * m + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, omega_pow_two_mul_add_one, one_pow]
  unfold eigenResidue hRatio
  refine tsum_congr fun i => ?_
  rw [hω, one_mul, mul_div_assoc]

/-- **The formula for `ρ^{(k)}`** [AOS, Lemma 7.5, (7.13)]: the residue function of the Lambert
seed with `c = ω^k` and coefficients `b_i(ω^k)` is `x⁻² ∑_i ω^{ki} q^{(m+1)i²}
(ω^k q;q)_i / (q^d;q^d)_i`, with `x = e(α)` and `q = e(τ)`. In particular `x² ρ^{(k)}` does not
depend on `x`. -/
theorem lambertResidue_eigen (m : ℕ) (α : ℚ) (k : ℕ) (τ : ℂ) :
    lambertResidue m α (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k)) τ =
      (e α ^ 2)⁻¹ * eigenResidue m k (e τ) := by
  have hx : e (α : ℂ) ≠ 0 := e_ne_zero _
  unfold lambertResidue lambertCoeff
  rw [eigenResidue_eq_tsum_hRatio]
  congr 1
  refine tsum_congr fun i => ?_
  have hω : (omega m ^ k) ^ (2 * m * i) * (omega m ^ k) ^ (2 * i) = omega m ^ (k * i) := by
    rw [← pow_add, ← pow_mul, show k * (2 * m * i + 2 * i) = k * i + (2 * m + 1) * (k * i) by
      ring, pow_add, pow_mul (omega m) (2 * m + 1) (k * i), omega_pow_two_mul_add_one, one_pow,
      mul_one]
  rw [div_pow, ← hω, show (m + 1) * i ^ 2 = m * i ^ 2 + i ^ 2 by ring, pow_add]
  field_simp

/-- The terms of `x² ρ^{(k)}` are bounded by `B'_Q Q^i` on `|q| ≤ Q < 1`. -/
lemma norm_eigenResidue_term_le (m k : ℕ) {q : ℂ} {Q : ℝ} (hq : ‖q‖ ≤ Q) (hQ1 : Q < 1)
    (i : ℕ) :
    ‖omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) * hRatio m (omega m ^ k) q i‖ ≤
      hRatioBound m Q * Q ^ i := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hq
  rw [norm_mul, norm_mul, norm_pow, norm_omega, one_pow, one_mul, norm_pow, mul_comm]
  refine mul_le_mul (norm_hRatio_le hQ0 hQ1 (norm_omega_pow m k).le hq i) ?_ (by positivity)
    (hRatioBound_nonneg hQ0 hQ1)
  refine (pow_le_pow_left₀ (norm_nonneg _) hq _).trans
    (pow_le_pow_of_le_one hQ0 hQ1.le ?_)
  nlinarith [Nat.le_self_pow two_ne_zero i]

/-- The series of `x² ρ^{(k)}` converges absolutely on the unit disc. -/
lemma summable_eigenResidue_term (m k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun i : ℕ =>
      omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) * hRatio m (omega m ^ k) q i :=
  Summable.of_norm_bounded (((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left
    (hRatioBound m ‖q‖))) fun i => norm_eigenResidue_term_le m k le_rfl hq i

/-- **Holomorphy of `x² ρ^{(k)}`** on the unit disc [AOS, Lemma 7.5]. -/
theorem differentiableOn_eigenResidue (m k : ℕ) :
    DifferentiableOn ℂ (eigenResidue m k) (Metric.ball 0 1) := by
  intro q₀ hq₀
  rw [mem_ball_zero_iff] at hq₀
  set r : ℝ := (‖q₀‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hq₀r : ‖q₀‖ < r := by rw [hr]; linarith
  have hD : DifferentiableOn ℂ (eigenResidue m k) (Metric.ball 0 r) := by
    rw [show eigenResidue m k = fun q => ∑' i : ℕ, omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) *
      hRatio m (omega m ^ k) q i from funext (eigenResidue_eq_tsum_hRatio m k)]
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one (by positivity) hr1).mul_left
        (hRatioBound m r)) (fun i => ?_) Metric.isOpen_ball
      (fun i q hq => norm_eigenResidue_term_le m k (mem_ball_zero_iff.mp hq).le hr1 i)
    exact ((differentiableOn_const _).mul (differentiableOn_pow _)).mul
      ((differentiableOn_hRatio (m := m) (norm_omega_pow m k).le i).mono
        (Metric.ball_subset_ball hr1.le))
  exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr hq₀r))).differentiableWithinAt

/-- **The leading term** [AOS, Lemma 7.5]: `x² ρ^{(k)} = 1` at `q = 0`. -/
theorem eigenResidue_zero (m k : ℕ) : eigenResidue m k 0 = 1 := by
  rw [eigenResidue_eq_tsum_hRatio, tsum_eq_single 0]
  · simp [hRatio, qPochhammer]
  · intro i hi
    rw [zero_pow (by positivity), mul_zero, zero_mul]

/-- `|x² ρ^{(k)} - 1| ≤ 3|q|³/(1 - |q|³)` for `|q| ≤ 1/2`, `m ≥ 2`. -/
theorem norm_eigenResidue_sub_one_le_cube {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) :
    ‖eigenResidue m k q - 1‖ ≤ 3 * ‖q‖ ^ 3 / (1 - ‖q‖ ^ 3) := by
  set t := ‖q‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t < 1 := by linarith
  have ht3 : t ^ 3 < 1 := pow_lt_one₀ ht0 ht1 (by norm_num)
  set f : ℕ → ℂ := fun i =>
    omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) * hRatio m (omega m ^ k) q i with hf
  have hfs : Summable f := summable_eigenResidue_term m k ht1
  have hf0 : f 0 = 1 := by simp [hf, hRatio, qPochhammer]
  have hle : ∀ i : ℕ, ‖f (i + 1)‖ ≤ 3 * (t ^ 3) ^ (i + 1) := by
    intro i
    simp only [hf]
    rw [norm_mul, norm_mul, norm_pow, norm_omega, one_pow, one_mul, norm_pow, mul_comm]
    refine mul_le_mul (norm_hRatio_le_three hm (norm_omega_pow m k) hq _) ?_
      (pow_nonneg ht0 _) (by norm_num)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ht0 ht1.le (by nlinarith)
  have ht30 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
  have hg : Summable fun i : ℕ => 3 * (t ^ 3) ^ (i + 1) :=
    ((summable_geometric_of_lt_one ht30 ht3).mul_left (3 * t ^ 3)).congr fun i => by ring
  rw [eigenResidue_eq_tsum_hRatio, ← hf, hfs.tsum_eq_zero_add, hf0, add_sub_cancel_left]
  have hn : Summable fun i : ℕ => ‖f (i + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hg
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hle hg).trans_eq ?_)
  rw [tsum_congr (fun i : ℕ => (by ring : 3 * (t ^ 3) ^ (i + 1) = 3 * t ^ 3 * (t ^ 3) ^ i)),
    tsum_mul_left, tsum_geometric_of_lt_one ht30 ht3, div_eq_mul_inv]

/-- **The estimate** `|x² ρ^{(k)}(τ) - 1| ≤ 3/7` for `|q| ≤ 1/2` [AOS, Lemma 7.5]. -/
theorem norm_eigenResidue_sub_one_le_three_sevenths {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) : ‖eigenResidue m k q - 1‖ ≤ 3 / 7 := by
  refine (norm_eigenResidue_sub_one_le_cube hm k hq).trans ?_
  have ht3 : ‖q‖ ^ 3 ≤ 1 / 8 := by
    calc ‖q‖ ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hq 3
      _ = 1 / 8 := by norm_num
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **`x² ρ^{(k)} = 1 + O(q)`** [AOS, Lemma 7.5]: `|x² ρ^{(k)} - 1| ≤ |q|` for `|q| ≤ 1/2`. -/
theorem norm_eigenResidue_sub_one_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) : ‖eigenResidue m k q - 1‖ ≤ ‖q‖ := by
  refine (norm_eigenResidue_sub_one_le_cube hm k hq).trans ?_
  set t := ‖q‖
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht3 : t ^ 3 ≤ 1 / 8 := by
    calc t ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ ht0 hq 3
      _ = 1 / 8 := by norm_num
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg ht0 ht0]

/-- `x² ρ^{(k)}` does not vanish on `|q| ≤ 1/2`. -/
theorem eigenResidue_ne_zero_of_norm_le_half {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) : eigenResidue m k q ≠ 0 := by
  intro h
  have := norm_eigenResidue_sub_one_le_three_sevenths hm k hq
  rw [h, zero_sub, norm_neg, norm_one] at this
  norm_num at this

/-- **`Ξ_m` misses `0 < |q| ≤ 1/2`** [AOS, Lemma 7.5]. -/
theorem not_mem_exceptionalSet_of_norm_le_half {m : ℕ} (hm : 2 ≤ m) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) : q ∉ exceptionalSet m := by
  rintro ⟨-, -, k, -, hk⟩
  exact eigenResidue_ne_zero_of_norm_le_half hm k hq hk

/-- **`Ξ_m` is discrete in the punctured disc** [AOS, Lemma 7.5]: every `z` with
`0 < |z| < 1` has a punctured neighbourhood disjoint from `Ξ_m`. -/
theorem eventually_not_mem_exceptionalSet (m : ℕ) {z : ℂ} (hz1 : ‖z‖ < 1) :
    ∀ᶠ y in 𝓝[≠] z, y ∉ exceptionalSet m := by
  have hball : z ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz1
  have hk : ∀ k ∈ Icc 1 (2 * m), ∀ᶠ y in 𝓝[≠] z, eigenResidue m k y ≠ 0 := by
    intro k _
    have han : AnalyticOnNhd ℂ (eigenResidue m k) (Metric.ball 0 1) :=
      (differentiableOn_eigenResidue m k).analyticOnNhd Metric.isOpen_ball
    rcases (han z hball).eventually_eq_zero_or_eventually_ne_zero with h | h
    · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball (0 : ℂ) 1).isPreconnected hball h (Metric.mem_ball_self one_pos)
      rw [eigenResidue_zero] at this
      exact absurd this one_ne_zero
    · exact h
  filter_upwards [(eventually_all_finset _).mpr hk] with y hy
  rintro ⟨-, -, k, hkI, hk0⟩
  exact hy k hkI hk0

/-- Off `Ξ_m`, the residue functions `ρ^{(k)}`, `1 ≤ k ≤ d - 1`, do not vanish at `q = e(τ)`,
`τ ∈ ℍ`. -/
theorem lambertResidue_eigen_ne_zero (m : ℕ) (α : ℚ) {τ : ℂ} (hτ : 0 < τ.im)
    (hq : e τ ∉ exceptionalSet m) {k : ℕ} (hk : k ∈ Icc 1 (2 * m)) :
    lambertResidue m α (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k)) τ ≠ 0 := by
  rw [lambertResidue_eigen]
  refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (e_ne_zero _))) fun h0 => hq ?_
  exact ⟨norm_pos_iff.mpr (e_ne_zero τ), mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ), k, hk,
    h0⟩

/-- **The residue functions of the eigen-solutions** [AOS, Lemma 7.5]. Let `m ≥ 2` and
`x = e(α)`. The residue function `ρ^{(k)}` of the Lambert seed of `Z^{(k)}` is
`x⁻² ∑_i ω^{ki} q^{(m+1)i²} (ω^k q;q)_i / (q^d;q^d)_i`; `x² ρ^{(k)}` is holomorphic on `|q| < 1`,
independent of `x`, equal to `1` at `q = 0` with `|x² ρ^{(k)} - 1| ≤ |q|` for `|q| ≤ 1/2`, and
`|x² ρ^{(k)} - 1| ≤ 3/7` for `|q| ≤ 1/2`. The exceptional set `Ξ_m` is discrete in the punctured
disc and disjoint from `0 < |q| ≤ 1/2`. -/
theorem eigenSolution_residues {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    (∀ (k : ℕ) (τ : ℂ),
      lambertResidue m α (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k)) τ =
        (e α ^ 2)⁻¹ * eigenResidue m k (e τ)) ∧
    (∀ k : ℕ, DifferentiableOn ℂ (eigenResidue m k) (Metric.ball 0 1)) ∧
    (∀ k : ℕ, eigenResidue m k 0 = 1 ∧
      ∀ q : ℂ, ‖q‖ ≤ 1 / 2 → ‖eigenResidue m k q - 1‖ ≤ ‖q‖) ∧
    (∀ (k : ℕ) (q : ℂ), ‖q‖ ≤ 1 / 2 → ‖eigenResidue m k q - 1‖ ≤ 3 / 7) ∧
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → ∀ᶠ y in 𝓝[≠] z, y ∉ exceptionalSet m) ∧
    ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ 1 / 2 → q ∉ exceptionalSet m :=
  ⟨lambertResidue_eigen m α, differentiableOn_eigenResidue m,
    fun k => ⟨eigenResidue_zero m k, fun _ hq => norm_eigenResidue_sub_one_le hm k hq⟩,
    fun k _ hq => norm_eigenResidue_sub_one_le_three_sevenths hm k hq,
    fun _ _ hz1 => eventually_not_mem_exceptionalSet m hz1,
    fun _ _ hq => not_mem_exceptionalSet_of_norm_le_half hm hq⟩

end HigherDyson3
