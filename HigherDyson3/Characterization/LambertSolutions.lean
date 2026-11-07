/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.HRatio
public import HigherDyson3.Analysis.LambertSeries

/-!
# The Lambert-type solutions `S_j(c)`

For `|c| = |x| = 1`, `λ = c/x` and `0 < |q| < 1`, the series
`S_j(c) = λ^j ∑_{i ≥ 0} λ^{2i} q^{i² + ij} h_i(c)` of [AOS, (7.5)] converges absolutely for all
`j ∈ ℤ`, satisfies `S_j(c) = λ^j (1 + O(|q|^{j+1}))`, solves the recurrence with right-hand side
`λ^{j-2} P_d(c)`, reduces to `X_j(x;q)/G_d(x;q)` for `c = x`, and has the Lambert-type seed
`x^{-2} ∑_i b_i(c) / (1 - c q^i u)` [AOS, Lemma 7.2].

## Main results

* `HigherDyson3.summable_norm_lambertSolution_term`, `HigherDyson3.norm_lambertSolution_sub_le`:
  [AOS, Lemma 7.2(a)].
* `HigherDyson3.lambertSolution_recurrence`: [AOS, Lemma 7.2(b)].
* `HigherDyson3.lambertSolution_self`: [AOS, Lemma 7.2(c)].
* `HigherDyson3.sequenceSeed_lambertSolution`, `HigherDyson3.differentiableAt_lambertSeed`,
  `HigherDyson3.exists_tendsto_sub_mul_lambertSeed`: [AOS, Lemma 7.2(d)].
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ} {x c q : ℂ}

theorem norm_div_eq_one (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) : ‖c / x‖ = 1 := by
  rw [norm_div, hc, hx, div_one]

theorem div_ne_zero_of_norm (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) : c / x ≠ 0 := by
  intro h
  have := norm_div_eq_one hx hc
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- `|q|^{i² + ij} ≤ |q|^{-(j-1)²} |q|^i` for `0 < |q| ≤ 1`. -/
private theorem norm_zpow_quad_le (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (j : ℤ) (i : ℕ) :
    ‖q‖ ^ ((i : ℤ) ^ 2 + i * j) ≤ ‖q‖ ^ (-(j - 1) ^ 2) * ‖q‖ ^ i := by
  have hr0 : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have h1 : ‖q‖ ^ ((i : ℤ) ^ 2 + i * j) ≤ ‖q‖ ^ (-(j - 1) ^ 2 + (i : ℤ)) :=
    zpow_le_zpow_right_of_le_one₀ hr0 hq1.le (by nlinarith [sq_nonneg ((i : ℤ) + (j - 1))])
  rwa [zpow_add₀ hr0.ne' (-(j - 1) ^ 2) (i : ℤ), zpow_natCast] at h1

/-- The summand of `S_j(c)` is bounded by `B'_Q |q|^{i² + ij}`. -/
private theorem norm_lambertSolution_term_le {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hx : ‖x‖ = 1)
    (hc : ‖c‖ = 1) (hq : ‖q‖ ≤ Q) (j : ℤ) (i : ℕ) :
    ‖(c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * j) * hRatio m c q i‖ ≤
      hRatioBound m Q * ‖q‖ ^ ((i : ℤ) ^ 2 + i * j) := by
  rw [norm_mul, norm_mul, norm_pow, norm_div_eq_one hx hc, one_pow, one_mul, norm_zpow, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_hRatio_le hQ0 hQ1 hc.le hq i) (by positivity)

/-- **Lemma 7.2(a), convergence.** The series defining `S_j(c)` converges absolutely for every
`j ∈ ℤ` [AOS, Lemma 7.2(a)]. -/
theorem summable_norm_lambertSolution_term (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    Summable fun i : ℕ => ‖(c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * j) * hRatio m c q i‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => (norm_lambertSolution_term_le (norm_nonneg q) hq1 hx hc le_rfl j i).trans
      (mul_le_mul_of_nonneg_left (norm_zpow_quad_le hq0 hq1 j i)
        (hRatioBound_nonneg (norm_nonneg q) hq1)))
    ((summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left
      (hRatioBound m ‖q‖ * ‖q‖ ^ (-(j - 1) ^ 2)) |>.congr fun i => by ring)

/-- **Lemma 7.2(a), asymptotics.** For `0 ≤ Q < 1`, `0 < |q| ≤ Q` and `j ≥ 0`,
`|λ^{-j} S_j(c) - 1| ≤ B'_Q/(1-Q) |q|^{j+1}` [AOS, (7.6)]. -/
theorem norm_lambertSolution_sub_le {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hx : ‖x‖ = 1)
    (hc : ‖c‖ = 1) (hq0 : q ≠ 0) (hq : ‖q‖ ≤ Q) (j : ℕ) :
    ‖(c / x) ^ (-(j : ℤ)) * lambertSolution m x c q j - 1‖ ≤
      hRatioBound m Q / (1 - Q) * ‖q‖ ^ (j + 1) := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt hQ1
  have hl := div_ne_zero_of_norm hx hc
  set t : ℕ → ℂ := fun i => (c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * (j : ℤ)) * hRatio m c q i
  have hs : Summable fun i => ‖t i‖ := summable_norm_lambertSolution_term hx hc hq0 hq1 j
  have hS : (c / x) ^ (-(j : ℤ)) * lambertSolution m x c q j = ∑' i, t i := by
    rw [lambertSolution, ← mul_assoc, ← zpow_add₀ hl, neg_add_cancel, zpow_zero, one_mul]
  have ht0 : t 0 = 1 := by simp [t]
  rw [hS, hs.of_norm.tsum_eq_zero_add, ht0, add_sub_cancel_left]
  have hs' : Summable fun i => ‖t (i + 1)‖ := hs.comp_injective (add_left_injective 1)
  have hbound : ∀ i, ‖t (i + 1)‖ ≤ hRatioBound m Q * ‖q‖ ^ (j + 1) * Q ^ i := fun i => by
    refine (norm_lambertSolution_term_le hQ0 hQ1 hx hc hq j (i + 1)).trans ?_
    have hexp : ((i + 1 : ℕ) : ℤ) ^ 2 + (i + 1 : ℕ) * (j : ℤ) =
        ((j + 1 + i + (i ^ 2 + i + i * j) : ℕ) : ℤ) := by
      push_cast; ring
    rw [hexp, zpow_natCast, pow_add, pow_add]
    have h1 : ‖q‖ ^ i ≤ Q ^ i := pow_le_pow_left₀ (norm_nonneg _) hq i
    have h2 : ‖q‖ ^ (i ^ 2 + i + i * j) ≤ 1 := pow_le_one₀ (norm_nonneg _) hq1.le
    have hB : 0 ≤ hRatioBound m Q := hRatioBound_nonneg hQ0 hQ1
    calc hRatioBound m Q * (‖q‖ ^ (j + 1) * ‖q‖ ^ i * ‖q‖ ^ (i ^ 2 + i + i * j))
        ≤ hRatioBound m Q * (‖q‖ ^ (j + 1) * Q ^ i * 1) := by gcongr
      _ = _ := by ring
  calc ‖∑' i, t (i + 1)‖ ≤ ∑' i, ‖t (i + 1)‖ := norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' i, hRatioBound m Q * ‖q‖ ^ (j + 1) * Q ^ i :=
        hs'.tsum_le_tsum hbound ((summable_geometric_of_lt_one hQ0 hQ1).mul_left _)
    _ = hRatioBound m Q / (1 - Q) * ‖q‖ ^ (j + 1) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hQ0 hQ1]; ring

theorem ne_zero_of_norm_eq_one {y : ℂ} (hy : ‖y‖ = 1) : y ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [hy]; exact one_ne_zero)

/-- The `r`-th shifted summand of `S_{j+r-2}(c)`, multiplied by `x^r`, is
`λ^{j-2} λ^{2i} q^{i² + i(j-2)} h_i(c) (c q^i)^r`. -/
private theorem lambert_term_shift (hx0 : x ≠ 0) (hc0 : c ≠ 0) (hq0 : q ≠ 0) (j : ℤ) (i r : ℕ) :
    x ^ r * ((c / x) ^ (j + r - 2) *
      ((c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * (j + r - 2)) * hRatio m c q i)) =
    (c / x) ^ (j - 2) * (c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * (j - 2)) * hRatio m c q i *
      (c * q ^ i) ^ r := by
  have hl : c / x ≠ 0 := div_ne_zero hc0 hx0
  rw [show j + r - 2 = (j - 2) + ((r : ℕ) : ℤ) by ring, zpow_add₀ hl, zpow_natCast,
    show (i : ℤ) ^ 2 + i * ((j - 2) + ((r : ℕ) : ℤ)) =
      ((i : ℤ) ^ 2 + i * (j - 2)) + ((i * r : ℕ) : ℤ) by push_cast; ring,
    zpow_add₀ hq0, zpow_natCast, pow_mul]
  have hxr : x ^ r * (c / x) ^ r = c ^ r := by rw [← mul_pow, mul_div_cancel₀ _ hx0]
  rw [mul_pow c, ← hxr]
  ring

/-- **Lemma 7.2(b).** For `|c| = |x| = 1`, `0 < |q| < 1` and every `j ∈ ℤ`,
`∑_{r=0}^{d-1} x^r S_{j+r-2}(c) - q^{j-1} S_j(c) = λ^{j-2} C_c` [AOS, (7.6)]. -/
theorem lambertSolution_recurrence (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    ∑ r ∈ range (2 * m + 1), x ^ r * lambertSolution m x c q (j + r - 2) -
      q ^ (j - 1) * lambertSolution m x c q j = (c / x) ^ (j - 2) * Cx m c := by
  have hx0 := ne_zero_of_norm_eq_one hx
  have hc0 := ne_zero_of_norm_eq_one hc
  have hl : c / x ≠ 0 := div_ne_zero hc0 hx0
  set A : ℕ → ℂ := fun i => (c / x) ^ (j - 2) * (c / x) ^ (2 * i) *
    q ^ ((i : ℤ) ^ 2 + i * (j - 2)) * hRatio m c q i with hA
  set a : ℕ → ℂ := fun i => A i * cyclotomicSum m (c * q ^ i) with ha
  have hterm : ∀ r : ℕ, Summable fun i : ℕ =>
      (c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * (j + r - 2)) * hRatio m c q i :=
    fun r => (summable_norm_lambertSolution_term hx hc hq0 hq1 _).of_norm
  have hexp : ∀ i, a i = ∑ r ∈ range (2 * m + 1), x ^ r * ((c / x) ^ (j + r - 2) *
      ((c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * (j + r - 2)) * hRatio m c q i)) := by
    intro i
    simp only [ha, hA, cyclotomicSum, mul_sum]
    exact sum_congr rfl fun r _ => (lambert_term_shift hx0 hc0 hq0 j i r).symm
  have hsa : Summable a := by
    rw [show a = _ from funext hexp]
    exact summable_sum fun r _ => ((hterm r).mul_left _).mul_left _
  have h1 : ∑ r ∈ range (2 * m + 1), x ^ r * lambertSolution m x c q (j + r - 2) = ∑' i, a i := by
    rw [tsum_congr hexp, Summable.tsum_finsetSum fun r _ => ((hterm r).mul_left _).mul_left _]
    refine sum_congr rfl fun r _ => ?_
    rw [lambertSolution, tsum_mul_left, tsum_mul_left]
  have h2 : q ^ (j - 1) * lambertSolution m x c q j = ∑' i, a (i + 1) := by
    rw [lambertSolution, ← mul_assoc, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    have e1 : (c / x) ^ j = (c / x) ^ (j - 2) * (c / x) ^ 2 := by
      calc (c / x) ^ j = (c / x) ^ ((j - 2) + ((2 : ℕ) : ℤ)) := by congr 1; push_cast; ring
        _ = _ := by rw [zpow_add₀ hl, zpow_natCast]
    have e2 : q ^ (j - 1) * q ^ ((i : ℤ) ^ 2 + i * j) =
        q ^ (((i + 1 : ℕ) : ℤ) ^ 2 + ((i + 1 : ℕ) : ℤ) * (j - 2)) := by
      rw [← zpow_add₀ hq0]; congr 1; push_cast; ring
    rw [ha, hA]
    beta_reduce
    rw [mul_assoc _ (hRatio m c q (i + 1)), hRatio_succ_mul_cyclotomicSum hc.le hq1 i, ← e2, e1,
      show 2 * (i + 1) = 2 * i + 2 by ring, pow_add]
    ring
  rw [h1, h2, hsa.tsum_eq_zero_add, add_sub_cancel_right]
  simp [ha, hA, Cx]

/-- **Lemma 7.2(c).** For `|x| = 1` and `|q| < 1`, `S_j(x) = X_j(x;q) / G_d(x;q)` for all
`j ∈ ℤ` [AOS, Lemma 7.2(c)]. -/
theorem lambertSolution_self (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq1 : ‖q‖ < 1) (j : ℤ) :
    lambertSolution m x x q j = XSeries m x j q / GProduct m x q := by
  rw [lambertSolution, div_self (ne_zero_of_norm_eq_one hx), one_zpow, one_mul, XSeries,
    ← tsum_div_const]
  refine tsum_congr fun i => ?_
  rw [one_pow, one_mul, hRatio_self hm hx.le hq1, gTail_zero, mul_div_assoc, mul_comm (i : ℤ) j]

/-- The coefficients `b_i(c)` are absolutely summable for `|c| = |x| = 1`, `|q| < 1`. -/
theorem summable_norm_lambertCoeff (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq1 : ‖q‖ < 1) :
    Summable fun i : ℕ => ‖lambertCoeff m x c i q‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq1).mul_left (hRatioBound m ‖q‖))
  refine (norm_lambertCoeff_le (norm_nonneg q) hq1 hx hc le_rfl i).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg q) hq1.le (by nlinarith))
    (hRatioBound_nonneg (norm_nonneg q) hq1)

/-- **Lemma 7.2(d), the seed.** For `|c| = |x| = 1`, `0 < |q| < 1` and `|u| < 1`,
`x^{-2} ∑_{j ≥ 0} S_j(c) (xu)^j = x^{-2} ∑_{i ≥ 0} b_i(c) / (1 - c q^i u)` [AOS, (7.7)]. -/
theorem sequenceSeed_lambertSolution (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq1 : ‖q‖ < 1) {u : ℂ}
    (hu : ‖u‖ < 1) :
    sequenceSeed x (fun j : ℕ => lambertSolution m x c q j) u =
      lambertSeed x c (lambertCoeff m x c) u q := by
  have hx0 := ne_zero_of_norm_eq_one hx
  unfold sequenceSeed lambertSeed
  congr 1
  set F : ℕ → ℕ → ℂ := fun i j => lambertCoeff m x c i q * (c * q ^ i * u) ^ j with hF
  have hξ : ∀ i : ℕ, ‖c * q ^ i * u‖ ≤ ‖u‖ := fun i => by
    rw [norm_mul, norm_mul, hc, one_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq1.le)
  have hFle : ∀ i j, ‖F i j‖ ≤ ‖lambertCoeff m x c i q‖ * ‖u‖ ^ j := fun i j => by
    rw [hF, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hξ i) j) (norm_nonneg _)
  have hb := summable_norm_lambertCoeff (m := m) hx hc hq1
  have hg := summable_geometric_of_lt_one (norm_nonneg u) hu
  have hsum : Summable (Function.uncurry F) :=
    Summable.of_norm_bounded (hb.mul_of_nonneg hg (fun _ => norm_nonneg _)
      (fun _ => by positivity)) (fun p => hFle p.1 p.2)
  have hrow : ∀ i, Summable (F i) := fun i =>
    Summable.of_norm_bounded (hg.mul_left _) (hFle i)
  have hcol : ∀ j, Summable fun i => F i j := fun j =>
    Summable.of_norm_bounded (hb.mul_right (‖u‖ ^ j)) (fun i => hFle i j)
  have hj : ∀ j : ℕ, lambertSolution m x c q j * (x * u) ^ j = ∑' i, F i j := by
    intro j
    rw [lambertSolution, zpow_natCast, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [hF]
    beta_reduce
    rw [lambertCoeff, show (i : ℤ) ^ 2 + i * ((j : ℕ) : ℤ) = ((i ^ 2 + i * j : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast, pow_add, pow_mul,
      show c * q ^ i * u = c / x * q ^ i * (x * u) by field_simp]
    ring
  rw [tsum_congr hj, hsum.tsum_comm' hrow hcol]
  refine tsum_congr fun i => ?_
  rw [hF]
  beta_reduce
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one ((hξ i).trans_lt hu), div_eq_mul_inv]

/-- The pole condition `c q^i u = 1` is `u = c^{-1} q^{-i}`. -/
theorem mul_pow_mul_eq_one_iff (hc0 : c ≠ 0) (hq0 : q ≠ 0) (i : ℕ) (u : ℂ) :
    c * q ^ i * u = 1 ↔ u = c⁻¹ * q ^ (-(i : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  constructor
  · intro h
    field_simp
    linear_combination h
  · rintro rfl
    field_simp

private theorem lambertSeed_eq (x c : ℂ) (b : ℕ → ℂ → ℂ) (q : ℂ) :
    (fun u => lambertSeed x c b u q) =
      fun u => (x ^ 2)⁻¹ * ∑' n, b n q / (1 - c * u * q ^ n) := by
  funext u
  simp only [lambertSeed, mul_right_comm c (q ^ _) u]

/-- **Lemma 7.2(d), holomorphy.** A Lambert-type seed `u ↦ x^{-2} ∑_i b_i / (1 - c q^i u)` with
absolutely summable coefficients is holomorphic at every `u₀` off the points `c^{-1} q^{-i}`
[AOS, Lemma 7.2(d)]. -/
theorem differentiableAt_lambertSeed {b : ℕ → ℂ → ℂ} (hb : Summable fun i => ‖b i q‖)
    (hq1 : ‖q‖ < 1) {u₀ : ℂ} (hu₀ : ∀ i : ℕ, c * q ^ i * u₀ ≠ 1) :
    DifferentiableAt ℂ (fun u => lambertSeed x c b u q) u₀ := by
  rw [lambertSeed_eq]
  refine (differentiableAt_lambertSeries hb hq1 fun n _ => ?_).const_mul _
  rw [mul_right_comm]
  exact hu₀ n

/-- **Lemma 7.2(d), simple poles.** For a Lambert-type seed with absolutely summable
coefficients, `c ≠ 0` and `0 < |q| < 1`, `(u - s) Φ(u)` has a limit at every point `s`: the seed
has at most simple poles, at the points `c^{-1} q^{-i}` [AOS, Lemma 7.2(d)]. -/
theorem exists_tendsto_sub_mul_lambertSeed {b : ℕ → ℂ → ℂ} (hb : Summable fun i => ‖b i q‖)
    (hc0 : c ≠ 0) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (s : ℂ) :
    ∃ L : ℂ, Tendsto (fun u => (u - s) * lambertSeed x c b u q) (𝓝[≠] s) (𝓝 L) := by
  by_cases hs : ∃ n₀ : ℕ, s = (c * q ^ n₀)⁻¹
  · obtain ⟨n₀, rfl⟩ := hs
    refine ⟨(x ^ 2)⁻¹ * (-(c * q ^ n₀)⁻¹ * b n₀ q), ?_⟩
    have h := (tendsto_sub_mul_lambertSeries hb hq0 hq1 hc0 n₀).const_mul (x ^ 2)⁻¹
    refine h.congr fun u => ?_
    rw [show lambertSeed x c b u q = (fun u => lambertSeed x c b u q) u from rfl, lambertSeed_eq]
    ring
  · simp only [not_exists] at hs
    have hd : DifferentiableAt ℂ (fun u => lambertSeed x c b u q) s :=
      differentiableAt_lambertSeed hb hq1 fun i h => hs i (by
        rw [(mul_pow_mul_eq_one_iff hc0 hq0 i s).mp h, mul_inv, zpow_neg, zpow_natCast])
    refine ⟨0, ?_⟩
    have hc : ContinuousAt (fun u => (u - s) * lambertSeed x c b u q) s :=
      (continuousAt_id.sub continuousAt_const).mul hd.continuousAt
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- **Lemma 7.2** [AOS, Lemma 7.2]. Let `m ≥ 2`, `|x| = |c| = 1`, `λ = c/x`, `0 < |q| < 1`.
(a) The series `S_j(c)` converges absolutely for every `j ∈ ℤ`, and
`|λ^{-j} S_j(c) - 1| ≤ B'_Q/(1-Q) |q|^{j+1}` for `j ≥ 0`, `|q| ≤ Q < 1`;
(b) `∑_{r<d} x^r S_{j+r-2}(c) - q^{j-1} S_j(c) = λ^{j-2} C_c` for every `j ∈ ℤ`;
(c) `S_j(x) = X_j(x;q)/G_d(x;q)` for every `j ∈ ℤ`;
(d) for `|u| < 1`, `x^{-2} ∑_j S_j(c)(xu)^j = x^{-2} ∑_i b_i(c)/(1 - c q^i u)`, and the right
side is holomorphic off the points `u = c^{-1} q^{-i}`, where `(u - s)Φ(u)` has a limit. -/
theorem lambertSolution_properties (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) :
    (∀ j : ℤ, Summable fun i : ℕ =>
      ‖(c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * j) * hRatio m c q i‖) ∧
    (∀ Q : ℝ, 0 ≤ Q → Q < 1 → ‖q‖ ≤ Q → ∀ j : ℕ,
      ‖(c / x) ^ (-(j : ℤ)) * lambertSolution m x c q j - 1‖ ≤
        hRatioBound m Q / (1 - Q) * ‖q‖ ^ (j + 1)) ∧
    (∀ j : ℤ, ∑ r ∈ range (2 * m + 1), x ^ r * lambertSolution m x c q (j + r - 2) -
      q ^ (j - 1) * lambertSolution m x c q j = (c / x) ^ (j - 2) * Cx m c) ∧
    (∀ j : ℤ, lambertSolution m x x q j = XSeries m x j q / GProduct m x q) ∧
    (∀ u : ℂ, ‖u‖ < 1 → sequenceSeed x (fun j : ℕ => lambertSolution m x c q j) u =
      lambertSeed x c (lambertCoeff m x c) u q) ∧
    (∀ u₀ : ℂ, (∀ i : ℕ, u₀ ≠ c⁻¹ * q ^ (-(i : ℤ))) →
      DifferentiableAt ℂ (fun u => lambertSeed x c (lambertCoeff m x c) u q) u₀) ∧
    (∀ s : ℂ, ∃ L : ℂ,
      Tendsto (fun u => (u - s) * lambertSeed x c (lambertCoeff m x c) u q) (𝓝[≠] s) (𝓝 L)) :=
  ⟨summable_norm_lambertSolution_term hx hc hq0 hq1,
    fun _ hQ0 hQ1 hq j => norm_lambertSolution_sub_le hQ0 hQ1 hx hc hq0 hq j,
    lambertSolution_recurrence hx hc hq0 hq1,
    lambertSolution_self hm hx hq1,
    fun _ hu => sequenceSeed_lambertSolution hx hc hq1 hu,
    fun u₀ hu₀ => differentiableAt_lambertSeed (summable_norm_lambertCoeff hx hc hq1) hq1
      fun i hi => hu₀ i ((mul_pow_mul_eq_one_iff (ne_zero_of_norm_eq_one hc) hq0 i u₀).mp hi),
    exists_tendsto_sub_mul_lambertSeed (summable_norm_lambertCoeff hx hc hq1)
      (ne_zero_of_norm_eq_one hc) hq0 hq1⟩

end HigherDyson3
