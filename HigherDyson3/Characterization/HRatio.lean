/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Definitions
public import HigherDyson3.Values.GShift

/-!
# The ratios `h_i(c)`

For `|c| ≤ 1` and `|q| < 1` the ratios `h_i(c) = (cq;q)_i / (c^d q^d; q^d)_i` of [AOS, (7.2)]
satisfy the uniform bound [AOS, (7.3)]
`|h_i(c)| ≤ B'_Q = ∏_{l ≥ 1} (1 + Q^l) / (1 - Q^{dl})` for `|q| ≤ Q < 1`, and the recursion
`h_{i+1}(c) P_d(c q^{i+1}) = h_i(c)`, which comes from `(1 - y) P_d(y) = 1 - y^d`. For `c = x`
the ratios are the normalized tails `h_i(x) = g_{i,x}(q) / g_{0,x}(q)`, and `G_d(x;q) ≠ 0`.

## Main results

* `HigherDyson3.norm_hRatio_le`: the bound `|h_i(c)| ≤ B'_Q` [AOS, (7.3)].
* `HigherDyson3.hRatio_succ_mul_cyclotomicSum`: `h_{i+1}(c) P_d(c q^{i+1}) = h_i(c)`.
* `HigherDyson3.GProduct_ne_zero`: `G_d(y;q) ≠ 0` for `|y| ≤ 1`, `|q| < 1`.
* `HigherDyson3.hRatio_self`: `h_i(x) = g_{i,x}(q) / g_{0,x}(q)`.
* `HigherDyson3.norm_lambertCoeff_le`, `HigherDyson3.differentiableOn_lambertCoeff`: the
  coefficients `b_i(c)` decay like `|q|^{i²}` and are holomorphic on the unit disc.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

/-- The constant `B'_Q = ∏_{l ≥ 1} (1 + Q^l) / (1 - Q^{dl})`, `d = 2m + 1`, of [AOS, (7.2)]. -/
def hRatioBound (m : ℕ) (Q : ℝ) : ℝ :=
  ∏' l : ℕ, (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1)))

theorem qPochhammer_succ (a q : ℂ) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

@[simp] theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

@[simp] theorem hRatio_zero (m : ℕ) (c q : ℂ) : hRatio m c q 0 = 1 := by
  simp [hRatio]

section Bound

variable {m : ℕ} {Q : ℝ}

/-- The factors of `B'_Q` are `1 + a_l` with `0 ≤ a_l ≤ 2 Q^{l+1} / (1 - Q)`. -/
private theorem hRatioBound_factor_eq (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (l : ℕ) :
    (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1))) =
      1 + (Q ^ (l + 1) + Q ^ ((2 * m + 1) * (l + 1))) / (1 - Q ^ ((2 * m + 1) * (l + 1))) := by
  have : Q ^ ((2 * m + 1) * (l + 1)) < 1 := pow_lt_one₀ hQ0 hQ1 (by positivity)
  rw [one_add_div (sub_pos.mpr this).ne']
  congr 1
  ring

private theorem hRatioBound_summand_le (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (l : ℕ) :
    (Q ^ (l + 1) + Q ^ ((2 * m + 1) * (l + 1))) / (1 - Q ^ ((2 * m + 1) * (l + 1))) ≤
      2 / (1 - Q) * Q ^ (l + 1) := by
  have h1 : Q ^ ((2 * m + 1) * (l + 1)) ≤ Q ^ (l + 1) :=
    pow_le_pow_of_le_one hQ0 hQ1.le (by nlinarith)
  have h2 : Q ^ ((2 * m + 1) * (l + 1)) ≤ Q :=
    pow_le_of_le_one hQ0 hQ1.le (by positivity)
  have hQ : 0 < 1 - Q := by linarith
  calc _ ≤ (2 * Q ^ (l + 1)) / (1 - Q) := div_le_div₀ (by positivity) (by linarith) hQ (by linarith)
    _ = _ := by ring

private theorem hRatioBound_summand_nonneg (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (l : ℕ) :
    0 ≤ (Q ^ (l + 1) + Q ^ ((2 * m + 1) * (l + 1))) / (1 - Q ^ ((2 * m + 1) * (l + 1))) := by
  have : Q ^ ((2 * m + 1) * (l + 1)) < 1 := pow_lt_one₀ hQ0 hQ1 (by positivity)
  exact div_nonneg (by positivity) (by linarith)

private theorem hasProd_hRatioBound (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    HasProd (fun l : ℕ => (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1))))
      (hRatioBound m Q) := by
  have hs : Summable fun l : ℕ =>
      ‖(Q ^ (l + 1) + Q ^ ((2 * m + 1) * (l + 1))) / (1 - Q ^ ((2 * m + 1) * (l + 1)))‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      ((summable_geometric_of_lt_one hQ0 hQ1).mul_left (2 / (1 - Q) * Q))
    rw [Real.norm_of_nonneg (hRatioBound_summand_nonneg hQ0 hQ1 l)]
    calc _ ≤ 2 / (1 - Q) * Q ^ (l + 1) := hRatioBound_summand_le hQ0 hQ1 l
      _ = 2 / (1 - Q) * Q * Q ^ l := by ring
  have h := (multipliable_one_add_of_summable hs).hasProd
  simp_rw [← hRatioBound_factor_eq hQ0 hQ1] at h
  exact h

/-- The partial products of `B'_Q` are bounded by `B'_Q`. -/
theorem prod_le_hRatioBound (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (n : ℕ) :
    ∏ l ∈ range n, (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1))) ≤ hRatioBound m Q := by
  have hf : ∀ l : ℕ, 1 ≤ (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1))) := fun l => by
    rw [hRatioBound_factor_eq hQ0 hQ1]
    linarith [hRatioBound_summand_nonneg (m := m) hQ0 hQ1 l]
  refine Monotone.ge_of_tendsto (monotone_nat_of_le_succ fun a => ?_)
    (hasProd_hRatioBound hQ0 hQ1).tendsto_prod_nat n
  rw [prod_range_succ]
  exact le_mul_of_one_le_right (prod_nonneg fun l _ => zero_le_one.trans (hf l)) (hf a)

theorem one_le_hRatioBound (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) : 1 ≤ hRatioBound m Q := by
  simpa using prod_le_hRatioBound (m := m) hQ0 hQ1 0

theorem hRatioBound_nonneg (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) : 0 ≤ hRatioBound m Q :=
  zero_le_one.trans (one_le_hRatioBound hQ0 hQ1)

end Bound

variable {m : ℕ} {c q : ℂ}

/-- The denominator `(c^d q^d; q^d)_i` of `h_i(c)` does not vanish for `|c| ≤ 1`, `|q| < 1`. -/
theorem qPochhammer_denom_ne_zero (hc : ‖c‖ ≤ 1) (hq : ‖q‖ < 1) (i : ℕ) :
    qPochhammer (c ^ (2 * m + 1) * q ^ (2 * m + 1)) (q ^ (2 * m + 1)) i ≠ 0 := by
  rw [qPochhammer, prod_ne_zero_iff]
  intro l _
  rw [sub_ne_zero]
  intro h
  have h1 : ‖c ^ (2 * m + 1) * q ^ (2 * m + 1) * (q ^ (2 * m + 1)) ^ l‖ < 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
    have hq' : ‖q‖ ^ (2 * m + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hq (by omega)
    have hc' : ‖c‖ ^ (2 * m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hc
    have hl : (‖q‖ ^ (2 * m + 1)) ^ l ≤ 1 := pow_le_one₀ (by positivity) hq'.le
    calc ‖c‖ ^ (2 * m + 1) * ‖q‖ ^ (2 * m + 1) * (‖q‖ ^ (2 * m + 1)) ^ l
        ≤ 1 * ‖q‖ ^ (2 * m + 1) * 1 := by gcongr
      _ < 1 := by simpa using hq'
  rw [← h] at h1
  simp at h1

/-- **The bound (7.3).** For `|c| ≤ 1`, `0 ≤ Q < 1` and `|q| ≤ Q`, `|h_i(c)| ≤ B'_Q`
[AOS, (7.3)]. -/
theorem norm_hRatio_le {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hc : ‖c‖ ≤ 1) (hq : ‖q‖ ≤ Q)
    (i : ℕ) : ‖hRatio m c q i‖ ≤ hRatioBound m Q := by
  refine le_trans ?_ (prod_le_hRatioBound hQ0 hQ1 i)
  rw [hRatio, norm_div, qPochhammer, qPochhammer, norm_prod, norm_prod, prod_div_distrib]
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  refine div_le_div₀ (prod_nonneg fun _ _ => by positivity) ?_
    (prod_pos fun l _ => by
      have : Q ^ ((2 * m + 1) * (l + 1)) < 1 := pow_lt_one₀ hQ0 hQ1 (by positivity)
      linarith) ?_
  · refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => ?_
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_mul, norm_pow]
    have : ‖q‖ ^ (l + 1) ≤ Q ^ (l + 1) := pow_le_pow_left₀ hq0 hq _
    calc 1 + ‖c‖ * ‖q‖ * ‖q‖ ^ l = 1 + ‖c‖ * ‖q‖ ^ (l + 1) := by ring
      _ ≤ 1 + 1 * Q ^ (l + 1) := by gcongr
      _ = 1 + Q ^ (l + 1) := by ring
  · refine Finset.prod_le_prod₀ (fun l _ => ?_) fun l _ => ?_
    · have : Q ^ ((2 * m + 1) * (l + 1)) < 1 := pow_lt_one₀ hQ0 hQ1 (by positivity)
      linarith
    · refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [norm_one, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
      have h1 : ‖q‖ ^ ((2 * m + 1) * (l + 1)) ≤ Q ^ ((2 * m + 1) * (l + 1)) :=
        pow_le_pow_left₀ hq0 hq _
      have h2 : ‖c‖ ^ (2 * m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hc
      have h3 : ‖c‖ ^ (2 * m + 1) * ‖q‖ ^ (2 * m + 1) * (‖q‖ ^ (2 * m + 1)) ^ l ≤
          1 * ‖q‖ ^ ((2 * m + 1) * (l + 1)) := by
        rw [← pow_mul, mul_assoc, ← pow_add,
          show 2 * m + 1 + (2 * m + 1) * l = (2 * m + 1) * (l + 1) by ring]
        gcongr
      linarith

/-- The recursion of `h_i(c)` in `i`. -/
theorem hRatio_succ (c q : ℂ) (i : ℕ) :
    hRatio m c q (i + 1) =
      hRatio m c q i * ((1 - c * q ^ (i + 1)) / (1 - (c * q ^ (i + 1)) ^ (2 * m + 1))) := by
  rw [hRatio, hRatio, qPochhammer_succ, qPochhammer_succ, mul_div_mul_comm]
  congr 2 <;> ring

/-- `P_d(y) ≠ 0` for `|y| < 1`, since `(1 - y) P_d(y) = 1 - y^d`. -/
theorem cyclotomicSum_ne_zero_of_norm_lt_one {y : ℂ} (hy : ‖y‖ < 1) : cyclotomicSum m y ≠ 0 := by
  intro h
  have h1 : cyclotomicSum m y * (1 - y) = 1 - y ^ (2 * m + 1) := geom_sum_mul_neg y _
  rw [h, zero_mul, eq_comm, sub_eq_zero] at h1
  have : ‖y ^ (2 * m + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hy (by omega)
  rw [← h1] at this
  simp at this

/-- **The recursion of the ratios.** For `|c| ≤ 1`, `|q| < 1`:
`h_{i+1}(c) P_d(c q^{i+1}) = h_i(c)` [AOS, proof of Lemma 7.2(b)]. -/
theorem hRatio_succ_mul_cyclotomicSum (hc : ‖c‖ ≤ 1) (hq : ‖q‖ < 1) (i : ℕ) :
    hRatio m c q (i + 1) * cyclotomicSum m (c * q ^ (i + 1)) = hRatio m c q i := by
  set y := c * q ^ (i + 1)
  have hy : ‖y‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc ‖c‖ * ‖q‖ ^ (i + 1) ≤ 1 * ‖q‖ ^ (i + 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hyd : 1 - y ^ (2 * m + 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have : ‖y ^ (2 * m + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hy (by omega)
    rw [← h] at this
    simp at this
  have h1 : cyclotomicSum m y * (1 - y) = 1 - y ^ (2 * m + 1) := geom_sum_mul_neg y _
  rw [hRatio_succ, mul_assoc, div_mul_eq_mul_div, mul_comm (1 - y), h1, div_self hyd, mul_one]

/-- **`G_d(y;q) ≠ 0`.** For `m ≥ 2`, `|y| ≤ 1` and `|q| < 1` no factor `P_d(y q^r)`, `r ≥ 1`,
vanishes, and the product converges absolutely, so `G_d(y;q) ≠ 0` [AOS, §7]. -/
theorem GProduct_ne_zero (hm : 2 ≤ m) {y : ℂ} (hy : ‖y‖ ≤ 1) (hq : ‖q‖ < 1) :
    GProduct m y q ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (R := ℂ)
    (f := fun r : ℕ => cyclotomicSum m (y * q ^ (r + 1)) - 1) (fun r => ?_)
    (summable_norm_cyclotomicSum_sub_one hm hq y)
  · simpa [GProduct] using h
  · rw [add_sub_cancel]
    refine cyclotomicSum_ne_zero_of_norm_lt_one ?_
    rw [norm_mul, norm_pow]
    calc ‖y‖ * ‖q‖ ^ (r + 1) ≤ 1 * ‖q‖ ^ (r + 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)

/-- `g_{0,x}(q) = G_d(x;q)`. -/
@[simp] theorem gTail_zero (m : ℕ) (x q : ℂ) : gTail m x 0 q = GProduct m x q := by
  simp [gTail]

/-- `h_i(x) G_d(x;q) = g_{i,x}(q)`, i.e. `h_i(x) = G_d(x q^i; q) / G_d(x; q)` [AOS, §7]. -/
theorem hRatio_mul_GProduct (hm : 2 ≤ m) {x : ℂ} (hx : ‖x‖ ≤ 1) (hq : ‖q‖ < 1) (i : ℕ) :
    hRatio m x q i * GProduct m x q = gTail m x i q := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hy : ‖x * q ^ (i + 1)‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖x‖ * ‖q‖ ^ (i + 1) ≤ 1 * ‖q‖ ^ (i + 1) := by gcongr
        _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    have hC := cyclotomicSum_ne_zero_of_norm_lt_one (m := m) hy
    have hshift : gTail m x i q = cyclotomicSum m (x * q ^ (i + 1)) * gTail m x (i + 1) q := by
      rw [gTail, GProduct_eq_cyclotomicSum_mul_GProduct hm hq, gTail, mul_assoc, ← pow_succ]
    refine mul_left_cancel₀ hC ?_
    rw [← hRatio_succ_mul_cyclotomicSum hx hq i] at ih
    rw [← hshift, ← ih]
    ring

/-- **(7.3), second part.** For `|x| ≤ 1` and `|q| < 1`,
`h_i(x) = g_{i,x}(q) / g_{0,x}(q)` [AOS, §7]. -/
theorem hRatio_self (hm : 2 ≤ m) {x : ℂ} (hx : ‖x‖ ≤ 1) (hq : ‖q‖ < 1) (i : ℕ) :
    hRatio m x q i = gTail m x i q / gTail m x 0 q := by
  rw [gTail_zero, ← hRatio_mul_GProduct hm hx hq i,
    mul_div_cancel_right₀ _ (GProduct_ne_zero hm hx hq)]

/-- **Gaussian decay of `b_i(c)`.** For `|c| = |x| = 1`, `0 ≤ Q < 1` and `|q| ≤ Q`,
`|b_i(c)| ≤ B'_Q |q|^{i²}` [AOS, Lemma 7.2(d) and its proof]. -/
theorem norm_lambertCoeff_le {x : ℂ} {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hx : ‖x‖ = 1)
    (hc : ‖c‖ = 1) (hq : ‖q‖ ≤ Q) (i : ℕ) :
    ‖lambertCoeff m x c i q‖ ≤ hRatioBound m Q * ‖q‖ ^ (i ^ 2) := by
  rw [lambertCoeff, norm_mul, norm_mul, norm_pow, norm_div, hc, hx, div_one, one_pow, one_mul,
    norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_hRatio_le hQ0 hQ1 hc.le hq i) (by positivity)

/-- `q ↦ (cq;q)_i` is entire. -/
private theorem differentiable_qPochhammer_num (c : ℂ) (i : ℕ) :
    Differentiable ℂ fun q : ℂ => qPochhammer (c * q) q i := by
  unfold qPochhammer
  fun_prop

private theorem differentiable_qPochhammer_denom (c : ℂ) (i : ℕ) :
    Differentiable ℂ fun q : ℂ =>
      qPochhammer (c ^ (2 * m + 1) * q ^ (2 * m + 1)) (q ^ (2 * m + 1)) i := by
  unfold qPochhammer
  fun_prop

/-- `q ↦ h_i(c)` is holomorphic on the unit disc for `|c| ≤ 1`. -/
theorem differentiableOn_hRatio (hc : ‖c‖ ≤ 1) (i : ℕ) :
    DifferentiableOn ℂ (fun q => hRatio m c q i) (Metric.ball 0 1) := by
  intro q hq
  rw [mem_ball_zero_iff] at hq
  exact ((differentiable_qPochhammer_num c i q).div (differentiable_qPochhammer_denom c i q)
    (qPochhammer_denom_ne_zero hc hq i)).differentiableWithinAt

/-- **Holomorphy of `b_i(c)`.** For `|c| ≤ 1`, `q ↦ b_i(c)` is holomorphic on the unit disc
[AOS, §7, before Lemma 7.5]. In particular this holds for `c = ω^k`. -/
theorem differentiableOn_lambertCoeff (x : ℂ) (hc : ‖c‖ ≤ 1) (i : ℕ) :
    DifferentiableOn ℂ (lambertCoeff m x c i) (Metric.ball 0 1) := by
  have h := differentiableOn_hRatio (m := m) hc i
  unfold lambertCoeff
  exact (((differentiableOn_const _).mul (differentiableOn_pow _)).mul h)

/-- **(7.3) and the normalized tails** [AOS, §7, (7.2)–(7.3)]. For `m ≥ 2`, `|x| = 1` and
`|q| < 1`: `|h_i(c)| ≤ B'_Q` whenever `|c| = 1`, `0 ≤ Q < 1` and `|q'| ≤ Q`;
`h_i(x) = g_{i,x}(q)/g_{0,x}(q)`; and `G_d(x;q) ≠ 0`. -/
theorem hRatio_bound_and_self (hm : 2 ≤ m) {x : ℂ} (hx : ‖x‖ = 1) (hq : ‖q‖ < 1) :
    (∀ Q : ℝ, 0 ≤ Q → Q < 1 → ∀ c' q' : ℂ, ‖c'‖ = 1 → ‖q'‖ ≤ Q → ∀ i : ℕ,
      ‖hRatio m c' q' i‖ ≤ hRatioBound m Q) ∧
    (∀ i : ℕ, hRatio m x q i = gTail m x i q / gTail m x 0 q) ∧ GProduct m x q ≠ 0 :=
  ⟨fun _ hQ0 hQ1 _ _ hc hq' i => norm_hRatio_le hQ0 hQ1 hc.le hq' i,
    hRatio_self hm hx.le hq, GProduct_ne_zero hm hx.le hq⟩

end HigherDyson3
