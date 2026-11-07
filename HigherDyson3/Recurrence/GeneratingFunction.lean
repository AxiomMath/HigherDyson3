/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.SeedSummable
public import HigherDyson3.Analysis.LambertSeries

/-!
# The generating function of the values `X_j`

For `m ≥ 2`, `d = 2m + 1` and `0 < |q| < 1`, the generating function
`𝓕_{d,x}(t;q) = ∑_{j ≥ 0} X_j^{(m)}(x;q) t^j` satisfies, for `|t| < 1`,
`𝓕_{d,x}(t;q) = ∑_{n ≥ 0} q^{n²} G_d(x q^n; q) / (1 - t q^n)` [AOS, Lemma 3.1]; the right-hand
side is holomorphic off the points `t = q^{-n}` and has at most simple poles there. In particular
the seed `𝒢_{d,x}(u;q)` is `x^{-2} 𝓕_{d,x}(xu;q)` for `|xu| < 1` [AOS, (1.5), (1.6)].

The manuscript assumes `x ∉ q^{-ℤ_{≥1}}` so that `G_d(xq^n;q)` is a quotient of nonvanishing
infinite products; with `G_d` defined by its product form (`HigherDyson3.GProduct`) this
hypothesis is not needed.

## Main results

* `HigherDyson3.summable_genFun`: `𝓕_{d,x}(t;q)` converges for `|t| < 1`.
* `HigherDyson3.genFun_eq_tsum`: the Lambert-type expansion of `𝓕_{d,x}`.
* `HigherDyson3.differentiableAt_genFunExpansion`, `HigherDyson3.tendsto_sub_mul_genFunExpansion`:
  the meromorphic continuation, with at most simple poles at `t = q^{-n}`.
* `HigherDyson3.seed_eq_genFun`: `𝒢_{d,x}(u;q) = x^{-2} 𝓕_{d,x}(xu;q)` for `|xu| < 1`.
-/

public section

namespace HigherDyson3

open Filter Topology

/-- The generating function `𝓕_{d,x}(t;q) = ∑_{j ≥ 0} X_j^{(m)}(x;q) t^j` [AOS, (1.5)]. -/
noncomputable def genFun (m : ℕ) (x q t : ℂ) : ℂ := ∑' j : ℕ, XSeries m x j q * t ^ j

theorem genFun_def (m : ℕ) (x q t : ℂ) : genFun m x q t = ∑' j : ℕ, XSeries m x j q * t ^ j :=
  (rfl)

/-- The Lambert-type expression `∑_{n ≥ 0} q^{n²} g_{n,x}(q) / (1 - t q^n)`, which continues
`𝓕_{d,x}(t;q)` meromorphically to all `t` [AOS, Lemma 3.1]. -/
noncomputable def genFunExpansion (m : ℕ) (x q t : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) * gTail m x n q / (1 - t * q ^ n)

theorem genFunExpansion_def (m : ℕ) (x q t : ℂ) :
    genFunExpansion m x q t = ∑' n : ℕ, q ^ (n ^ 2) * gTail m x n q / (1 - t * q ^ n) := (rfl)

theorem genFunExpansion_eq_lambert (m : ℕ) (x q : ℂ) :
    genFunExpansion m x q =
      fun t => ∑' n : ℕ, q ^ (n ^ 2) * gTail m x n q / (1 - 1 * t * q ^ n) := by
  funext t
  simp [genFunExpansion]

theorem summable_norm_genFun_coeff {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) : Summable (fun n : ℕ => ‖q ^ (n ^ 2) * gTail m x n q‖) := by
  have h := summable_norm_seed_term hm x hq0 hq1 0
  simpa using h

/-- The double series `∑_{j,n} q^{n² + jn} g_{n,x}(q) t^j` converges absolutely for `|q| < 1`
and `|t| < 1`. -/
private theorem summable_genFun_double {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q t : ℂ} (hq1 : ‖q‖ < 1)
    (ht : ‖t‖ < 1) :
    Summable (Function.uncurry fun j n : ℕ => q ^ (n ^ 2 + j * n) * gTail m x n q * t ^ j) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm (norm_nonneg q) hq1 (norm_nonneg x)
  have hbound : ∀ j n : ℕ, ‖q ^ (n ^ 2 + j * n) * gTail m x n q * t ^ j‖ ≤
      C * (‖t‖ ^ j * ‖q‖ ^ n) := by
    intro j n
    simp only [norm_mul, norm_pow]
    have h1 : ‖q‖ ^ (n ^ 2 + j * n) ≤ ‖q‖ ^ n :=
      pow_le_pow_of_le_one (norm_nonneg q) hq1.le (by nlinarith [Nat.zero_le j])
    have h2 := hC n q le_rfl x le_rfl
    calc ‖q‖ ^ (n ^ 2 + j * n) * ‖gTail m x n q‖ * ‖t‖ ^ j ≤ ‖q‖ ^ n * C * ‖t‖ ^ j := by
          gcongr
      _ = C * (‖t‖ ^ j * ‖q‖ ^ n) := by ring
  have hg : Summable (fun p : ℕ × ℕ => ‖t‖ ^ p.1 * ‖q‖ ^ p.2) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_of_nonneg
      (summable_geometric_of_lt_one (norm_nonneg q) hq1) (fun _ => by positivity)
      (fun _ => by positivity)
  exact Summable.of_norm_bounded (hg.mul_left C) (fun p => hbound p.1 p.2)

/-- The `j`-th term of `𝓕_{d,x}(t;q)` is the `j`-th row of the double series. -/
private theorem XSeries_mul_pow_eq_tsum (m : ℕ) (x q t : ℂ) (j : ℕ) :
    XSeries m x j q * t ^ j = ∑' n : ℕ, q ^ (n ^ 2 + j * n) * gTail m x n q * t ^ j := by
  rw [XSeries, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have : ((n : ℤ) ^ 2 + ((j : ℕ) : ℤ) * n) = ((n ^ 2 + j * n : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_natCast]

/-- **Convergence of the generating function** [AOS, (1.5), proof of Lemma 3.1]. For `m ≥ 2`,
`x ∈ ℂ`, `|q| < 1` and `|t| < 1`, the series `𝓕_{d,x}(t;q) = ∑_{j ≥ 0} X_j^{(m)}(x;q) t^j`
converges. -/
theorem summable_genFun {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q t : ℂ} (hq1 : ‖q‖ < 1)
    (ht : ‖t‖ < 1) : Summable fun j : ℕ => XSeries m x j q * t ^ j := by
  exact (summable_genFun_double hm x hq1 ht).prod.congr fun j =>
    (XSeries_mul_pow_eq_tsum m x q t j).symm

/-- **The generating function as a Lambert series** [AOS, Lemma 3.1]. For `m ≥ 2`, `x ∈ ℂ`,
`|q| < 1` and `|t| < 1`, `𝓕_{d,x}(t;q) = ∑_{n ≥ 0} q^{n²} G_d(x q^n; q) / (1 - t q^n)`. -/
theorem genFun_eq_tsum {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q t : ℂ} (hq1 : ‖q‖ < 1) (ht : ‖t‖ < 1) :
    genFun m x q t = genFunExpansion m x q t := by
  have hcol : ∀ n : ℕ, ∑' j : ℕ, q ^ (n ^ 2 + j * n) * gTail m x n q * t ^ j =
      q ^ (n ^ 2) * gTail m x n q / (1 - t * q ^ n) := by
    intro n
    have hlt : ‖q ^ n * t‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖q‖ ^ n * ‖t‖ ≤ 1 * ‖t‖ := by gcongr; exact pow_le_one₀ (norm_nonneg q) hq1.le
        _ < 1 := by simpa using ht
    have : ∀ j : ℕ, q ^ (n ^ 2 + j * n) * gTail m x n q * t ^ j =
        q ^ (n ^ 2) * gTail m x n q * (q ^ n * t) ^ j := by
      intro j
      rw [mul_pow, pow_add, ← pow_mul, mul_comm n j]
      ring
    rw [tsum_congr this, tsum_mul_left, tsum_geometric_of_norm_lt_one hlt, div_eq_mul_inv,
      mul_comm (q ^ n) t]
  rw [genFun, genFunExpansion, tsum_congr (XSeries_mul_pow_eq_tsum m x q t),
    ← (summable_genFun_double hm x hq1 ht).tsum_comm]
  exact tsum_congr hcol

/-- **Meromorphic continuation, holomorphic part** [AOS, Lemma 3.1]. The Lambert-type expression
`∑_n q^{n²} g_{n,x}(q) / (1 - t q^n)` is holomorphic at every `t₀` with `t₀ q^n ≠ 1` for all
`n`, i.e. off the points `t = q^{-n}`. -/
theorem differentiableAt_genFunExpansion {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q t₀ : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (ht₀ : ∀ n : ℕ, t₀ * q ^ n ≠ 1) :
    DifferentiableAt ℂ (genFunExpansion m x q) t₀ := by
  have h := differentiableAt_lambertSeries (c := 1) (summable_norm_genFun_coeff hm x hq0 hq1) hq1
    (t₀ := t₀) (fun n _ => by simpa using ht₀ n)
  rwa [genFunExpansion_eq_lambert]

/-- **Meromorphic continuation, simple poles** [AOS, Lemma 3.1]. At `t = q^{-n₀}` the
Lambert-type expression has at most a simple pole: `(t - q^{-n₀}) 𝓕(t)` tends to
`-q^{-n₀} q^{n₀²} g_{n₀,x}(q)`. -/
theorem tendsto_sub_mul_genFunExpansion {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (n₀ : ℕ) :
    Tendsto (fun t => (t - (q ^ n₀)⁻¹) * genFunExpansion m x q t) (𝓝[≠] (q ^ n₀)⁻¹)
      (𝓝 (-(q ^ n₀)⁻¹ * (q ^ (n₀ ^ 2) * gTail m x n₀ q))) := by
  have h := tendsto_sub_mul_lambertSeries (c := 1) (summable_norm_genFun_coeff hm x hq0 hq1) hq0
    hq1 one_ne_zero n₀
  rw [genFunExpansion_eq_lambert]
  simpa using h

/-- **The seed as a specialization of the generating function** [AOS, (1.5), (1.6)]. For
`|xu| < 1`, `𝒢_{d,x}(u;q) = x^{-2} 𝓕_{d,x}(xu;q)`. -/
theorem seed_eq_genFun {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hq1 : ‖q‖ < 1)
    (hxu : ‖x * u‖ < 1) : seed m x u q = (x ^ 2)⁻¹ * genFun m x q (x * u) := by
  rw [genFun_eq_tsum hm x hq1 hxu, seed, genFunExpansion]

end HigherDyson3
