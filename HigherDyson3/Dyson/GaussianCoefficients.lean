/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.AnalyticSeries

/-!
# The Laurent expansion of the higher Dyson terms

For `n ≥ 0` the coefficients `C_n(k;q)` are defined by the Laurent expansion
`1/(xq, q/x; q)_n = ∑_{k ∈ ℤ} C_n(k;q) x^k` on `|q| < |x| < |q|^{-1}` [AOS, Theorem 2.5]. For
`n ≥ 1` the finite `q`-binomial theorem expands both factors, and the coefficient of `x^k` in the
product is `C_n(k;q) = ∑_{a - b = k} [n+a-1, a]_q [n+b-1, b]_q q^{a+b}`; this convolution is the
definition used here, and `C_0(k;q) = δ_{k,0}`. The expansion with these coefficients holds on the
whole annulus, and Laurent coefficients on an annulus around the unit circle are unique, so these
are the coefficients of [AOS, Theorem 2.5].

## Main results

* `HigherDyson3.gaussianLaurentCoeff`: `C_n(k;q)`.
* `HigherDyson3.hasSum_gaussianLaurentCoeff`: the Laurent expansion on `|q| < |x| < |q|^{-1}`.
* `HigherDyson3.gaussianLaurentCoeff_unique`: uniqueness of the Laurent coefficients.
* `HigherDyson3.gaussianLaurentCoeff_natCast`:
  `C_n(k;q) = ∑_v [n+k+v-1, k+v]_q [n+v-1, v]_q q^{k+2v}` for `k ≥ 0`.
* `HigherDyson3.gaussianLaurentCoeff_neg`: `C_n(-k;q) = C_n(k;q)`.
* `HigherDyson3.higherDysonSeriesZ_eq_tsum_gaussianLaurentCoeff`: the expansion of `R_m(z;q)` on
  `|q|^{1/m} < |z| < |q|^{-1/m}`.
-/

public section

noncomputable section

open Finset Complex MeasureTheory

namespace HigherDyson3

/-- **Uniqueness of Laurent coefficients on the unit circle.** If `∑_{k ∈ ℤ} c_k x^k = 0` for every
`x` with `|x| = 1`, then every `c_k` vanishes. -/
theorem eq_zero_of_hasSum_zpow {c : ℤ → ℂ}
    (h : ∀ x : ℂ, ‖x‖ = 1 → HasSum (fun k => c k * x ^ k) 0) : c = 0 := by
  have habs : Summable fun k => ‖c k‖ := by
    have := (summable_norm_iff (E := ℂ)).mpr (h 1 (by simp)).summable
    simpa using this
  funext j
  set u : ℝ → ℂ := fun θ => Complex.exp (θ * I)
  have hu : ∀ θ, ‖u θ‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hu0 : ∀ θ, u θ ≠ 0 := fun θ => Complex.exp_ne_zero _
  set F : ℤ → ℝ → ℂ := fun k θ => c k * u θ ^ k * u θ ^ (-j)
  have hF : ∀ k θ, F k θ = c k * Complex.exp ((((k - j : ℤ) : ℂ) * I) * θ) := by
    intro k θ
    simp only [F, u]
    rw [mul_assoc, ← zpow_add₀ (Complex.exp_ne_zero _), ← Complex.exp_int_mul]
    congr 2
    push_cast
    ring
  have hlim : HasSum (fun k => ∫ θ in (0 : ℝ)..2 * Real.pi, F k θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi, (0 : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖c k‖)
      (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      rw [show F k = fun θ : ℝ => c k * Complex.exp ((((k - j : ℤ) : ℂ) * I) * θ) from
        funext (hF k)]
      fun_prop
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      simp [F, norm_zpow, hu]
    · exact Filter.Eventually.of_forall fun θ _ => habs
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      simpa [F] using (h (u θ) (hu θ)).mul_right (u θ ^ (-j))
  have hint : ∀ k, ∫ θ in (0 : ℝ)..2 * Real.pi, F k θ =
      if k = j then (2 * Real.pi : ℂ) * c j else 0 := by
    intro k
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    split_ifs with hk
    · subst hk
      simp [mul_comm]
    · have hne : (((k - j : ℤ) : ℂ) * I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr hk) I_ne_zero
      rw [integral_exp_mul_complex hne]
      have : Complex.exp ((((k - j : ℤ) : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
        rw [show (((k - j : ℤ) : ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ) =
          ((k - j : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I _
      rw [this]
      simp
  simp only [hint, intervalIntegral.integral_zero] at hlim
  have h2 := hlim.unique (hasSum_ite_eq j ((2 * Real.pi : ℂ) * c j))
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  simpa [hpi] using h2.symm

/-- The summand `[n+a-1, a]_q [n+b-1, b]_q q^{a+b}` of `C_n(a - b; q)`. -/
def gaussianPairTerm (n : ℕ) (q : ℂ) (p : ℕ × ℕ) : ℂ :=
  gaussianBinomial (n + p.1 - 1) p.1 q * gaussianBinomial (n + p.2 - 1) p.2 q * q ^ (p.1 + p.2)

/-- The coefficients `C_n(k;q)` of `1/(xq, q/x; q)_n = ∑_{k ∈ ℤ} C_n(k;q) x^k` [AOS, Theorem 2.5]:
`C_0(k;q) = δ_{k,0}`, and for `n ≥ 1` the coefficient of `x^k` in the product of the
`q`-binomial expansions, `C_n(k;q) = ∑_{a - b = k} [n+a-1, a]_q [n+b-1, b]_q q^{a+b}`. That these
are the Laurent coefficients is `hasSum_gaussianLaurentCoeff` with
`gaussianLaurentCoeff_unique`. -/
def gaussianLaurentCoeff (n : ℕ) (k : ℤ) (q : ℂ) : ℂ :=
  if n = 0 then (if k = 0 then 1 else 0) else
    ∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, gaussianPairTerm n q p.1

/-- `|q| < 1` on a nonempty annulus `|q| < |x| < |q|^{-1}`. -/
private theorem norm_lt_one_of_annulus {q x : ℂ} (h1 : ‖q‖ < ‖x‖) (h2 : ‖x‖ < ‖q‖⁻¹) :
    ‖q‖ < 1 := by
  by_contra h
  have : ‖q‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (not_lt.mp h)
  linarith

/-- The product of the two `q`-binomial expansions, as a sum over `(a, b) ∈ ℕ²`. -/
private theorem hasSum_gaussianPairTerm {n : ℕ} (hn : 1 ≤ n) {q x : ℂ} (h1 : ‖q‖ < ‖x‖)
    (h2 : ‖x‖ < ‖q‖⁻¹) :
    HasSum (fun p : ℕ × ℕ => gaussianPairTerm n q p * x ^ ((p.1 : ℤ) - p.2))
      (1 / (qPochhammer (x * q) q n * qPochhammer (q / x) q n)) := by
  have hq := norm_lt_one_of_annulus h1 h2
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg q).trans_lt h1)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at h2
    linarith [norm_nonneg x]
  have hxq : ‖x * q‖ < 1 := by
    have := mul_lt_mul_of_pos_right h2 (norm_pos_iff.mpr hq0)
    rwa [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0), ← norm_mul] at this
  have hxq' : ‖x⁻¹ * q‖ < 1 := by
    rw [norm_mul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.mpr hx0), mul_one]
    exact h1
  have hA := hasSum_qBinomial hn hq hxq
  have hB := hasSum_qBinomial hn hq hxq'
  have hAB := hA.mul hB (summable_mul_of_summable_norm
    ((summable_norm_iff (E := ℂ)).mpr hA.summable) ((summable_norm_iff (E := ℂ)).mpr hB.summable))
  rw [div_eq_inv_mul q x, one_div, mul_inv, ← one_div, ← one_div]
  refine hAB.congr_fun fun p => ?_
  simp only [gaussianPairTerm]
  rw [zpow_sub₀ hx0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv, pow_add]
  ring

/-- **The Laurent expansion** [AOS, Theorem 2.5]: for `n ≥ 0` and `|q| < |x| < |q|^{-1}`,
`1/(xq, q/x; q)_n = ∑_{k ∈ ℤ} C_n(k;q) x^k`, the series converging absolutely. -/
theorem hasSum_gaussianLaurentCoeff (n : ℕ) {q x : ℂ} (h1 : ‖q‖ < ‖x‖) (h2 : ‖x‖ < ‖q‖⁻¹) :
    HasSum (fun k : ℤ => gaussianLaurentCoeff n k q * x ^ k)
      (1 / (qPochhammer (x * q) q n * qPochhammer (q / x) q n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [gaussianLaurentCoeff, ite_true, qPochhammer, range_zero, prod_empty, mul_one,
      div_one, ite_mul, one_mul, zero_mul]
    convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 2 with k
    split_ifs with hk <;> simp [hk]
  have hq := norm_lt_one_of_annulus h1 h2
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at h2
    linarith [norm_nonneg x]
  have hT : Summable (gaussianPairTerm n q) := by
    have := (hasSum_gaussianPairTerm hn (x := 1) (by simpa using hq)
      (by simpa using one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hq0, hq⟩)).summable
    simpa using this
  have h := (Equiv.sigmaFiberEquiv fun p : ℕ × ℕ => (p.1 : ℤ) - p.2).hasSum_iff.mpr
    (hasSum_gaussianPairTerm hn h1 h2)
  refine h.sigma fun k => ?_
  have hk := ((hT.subtype {p : ℕ × ℕ | (p.1 : ℤ) - p.2 = k}).hasSum).mul_right (x ^ k)
  rw [gaussianLaurentCoeff, ite_eq_right (by omega)]
  refine hk.congr_fun fun c => ?_
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
  rw [c.2]

/-- **Uniqueness of the Laurent coefficients**: for `0 < |q| < 1`, any `c : ℤ → ℂ` with
`1/(xq, q/x; q)_n = ∑_k c_k x^k` on `|q| < |x| < |q|^{-1}` is `C_n(·;q)`. -/
theorem gaussianLaurentCoeff_unique (n : ℕ) {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (c : ℤ → ℂ)
    (hc : ∀ x : ℂ, ‖q‖ < ‖x‖ → ‖x‖ < ‖q‖⁻¹ →
      HasSum (fun k => c k * x ^ k) (1 / (qPochhammer (x * q) q n * qPochhammer (q / x) q n))) :
    c = fun k => gaussianLaurentCoeff n k q := by
  have h0 := eq_zero_of_hasSum_zpow (c := fun k => c k - gaussianLaurentCoeff n k q) fun x hx => by
    have h1 : ‖q‖ < ‖x‖ := hx ▸ hq
    have h2 : ‖x‖ < ‖q‖⁻¹ := hx ▸ one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hq0, hq⟩
    simpa [sub_mul] using (hc x h1 h2).sub (hasSum_gaussianLaurentCoeff n h1 h2)
  funext k
  exact sub_eq_zero.mp (congrFun h0 k)

/-- `C_0(0;q) = 1` and `C_0(k;q) = 0` for `k ≠ 0` [AOS, Theorem 2.5]. -/
theorem gaussianLaurentCoeff_zero (k : ℤ) (q : ℂ) :
    gaussianLaurentCoeff 0 k q = if k = 0 then 1 else 0 := by
  rw [gaussianLaurentCoeff, ite_eq_left rfl]

/-- **The coefficient formula** [AOS, Theorem 2.5]: for `n ≥ 1` and `k ≥ 0`,
`C_n(k;q) = ∑_{v ≥ 0} [n+k+v-1, k+v]_q [n+v-1, v]_q q^{k+2v}`. -/
theorem gaussianLaurentCoeff_natCast {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (q : ℂ) :
    gaussianLaurentCoeff n k q = ∑' v : ℕ,
      gaussianBinomial (n + k + v - 1) (k + v) q * gaussianBinomial (n + v - 1) v q *
        q ^ (k + 2 * v) := by
  rw [gaussianLaurentCoeff, ite_eq_right (by omega)]
  let e : ℕ ≃ {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k} :=
    { toFun := fun v => ⟨(k + v, v), by push_cast; ring⟩
      invFun := fun p => p.1.2
      left_inv := fun v => rfl
      right_inv := fun p => by
        obtain ⟨⟨a, b⟩, h⟩ := p
        simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
        omega }
  rw [← e.tsum_eq]
  refine tsum_congr fun v => ?_
  simp only [e, Equiv.coe_fn_mk, gaussianPairTerm]
  rw [show n + (k + v) - 1 = n + k + v - 1 by omega, show k + v + v = k + 2 * v by ring]

/-- **Symmetry** [AOS, Theorem 2.5]: `C_n(-k;q) = C_n(k;q)`. -/
theorem gaussianLaurentCoeff_neg (n : ℕ) (k : ℤ) (q : ℂ) :
    gaussianLaurentCoeff n (-k) q = gaussianLaurentCoeff n k q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gaussianLaurentCoeff_zero]
  rw [gaussianLaurentCoeff, gaussianLaurentCoeff, ite_eq_right (by omega), ite_eq_right (by omega)]
  let e : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k} ≃ {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -k} :=
    { toFun := fun p => ⟨p.1.swap, by simp only [Prod.fst_swap, Prod.snd_swap]; omega⟩
      invFun := fun p => ⟨p.1.swap, by simp only [Prod.fst_swap, Prod.snd_swap]; omega⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [e, Equiv.coe_fn_mk, gaussianPairTerm, Prod.fst_swap, Prod.snd_swap]
  ring

/-- A finite product of absolutely convergent series over `ℤ` is the absolutely convergent series
over `ℤ^m` of the products. -/
theorem hasSum_pi_prod (m : ℕ) (f : Fin m → ℤ → ℂ) (hf : ∀ j, Summable fun t => ‖f j t‖) :
    HasSum (fun k : Fin m → ℤ => ∏ j, f j (k j)) (∏ j, ∑' t, f j t) ∧
      Summable fun k : Fin m → ℤ => ‖∏ j, f j (k j)‖ := by
  induction m with
  | zero =>
    simp only [univ_eq_empty, prod_empty, norm_one]
    exact ⟨by simp,
      Summable.of_finite⟩
  | succ m ih =>
    obtain ⟨ih, ihn⟩ := ih (fun j => f j.succ) fun j => hf j.succ
    have h0 := ((summable_norm_iff (E := ℂ)).mp (hf 0)).hasSum
    have hmul := h0.mul ih (summable_mul_of_summable_norm (f := f 0)
      (g := fun k : Fin m → ℤ => ∏ j : Fin m, f j.succ (k j)) (hf 0) ihn)
    have hnorm : Summable fun p : ℤ × (Fin m → ℤ) =>
        ‖f 0 p.1‖ * ‖∏ j : Fin m, f j.succ (p.2 j)‖ :=
      summable_mul_of_summable_norm (f := fun t => ‖f 0 t‖)
        (g := fun k : Fin m → ℤ => ‖∏ j : Fin m, f j.succ (k j)‖)
        (by simpa using hf 0) (by simpa using ihn)
    set e := Fin.consEquiv fun _ : Fin (m + 1) => ℤ
    have he : ∀ p : ℤ × (Fin m → ℤ),
        ∏ j, f j (e p j) = f 0 p.1 * ∏ j : Fin m, f j.succ (p.2 j) := by
      rintro ⟨t, k⟩
      rw [Fin.prod_univ_succ]
      rfl
    refine ⟨?_, ?_⟩
    · rw [Fin.prod_univ_succ]
      exact e.hasSum_iff.mp (hmul.congr_fun fun p => he p)
    · refine e.summable_iff.mp (hnorm.congr fun p => ?_)
      change ‖f 0 p.1‖ * ‖∏ j : Fin m, f j.succ (p.2 j)‖ = ‖∏ j, f j (e p j)‖
      rw [he p, norm_mul]

/-- `∏_{j} z^{a_j} = z^{∑_j a_j}` for `z ≠ 0`. -/
private theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) {z : ℂ} (hz : z ≠ 0)
    (a : ι → ℤ) : ∏ j ∈ s, z ^ a j = z ^ (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hz]

/-- **The expansion of `R_m(z;q)`** [AOS, Theorem 2.5]: for `m ≥ 1` and
`|q|^{1/m} < |z| < |q|^{-1/m}`,
`R_m(z;q) = ∑_{n ≥ 0} q^{n²} ∑_{𝐤 ∈ ℤ^m} (∏_{j=1}^m C_n(k_j;q)) z^{k_1 + 2k_2 + ⋯ + m k_m}`
(with `k (j : Fin m)` the paper's `k_{j+1}`); each inner series converges absolutely. -/
theorem higherDysonSeriesZ_eq_tsum_gaussianLaurentCoeff {m : ℕ} (hm : 1 ≤ m) {q z : ℂ}
    (h1 : ‖q‖ ^ ((1 : ℝ) / m) < ‖z‖) (h2 : ‖z‖ < ‖q‖ ^ (-(1 : ℝ) / m)) :
    higherDysonSeriesZ m z q = ∑' n : ℕ, q ^ (n ^ 2) *
      ∑' k : Fin m → ℤ, (∏ j, gaussianLaurentCoeff n (k j) q) *
        z ^ (∑ j : Fin m, ((j : ℤ) + 1) * k j) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpow1 : (‖q‖ ^ ((1 : ℝ) / m)) ^ m = ‖q‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hm0,
      Real.rpow_one]
  have hpow2 : (‖q‖ ^ (-(1 : ℝ) / m)) ^ m = ‖q‖⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), div_mul_cancel₀ _ hm0,
      Real.rpow_neg_one]
  have hz1 : ‖q‖ < ‖z‖ ^ m := hpow1 ▸ pow_lt_pow_left₀ h1 (by positivity) (by omega)
  have hz2 : ‖z‖ ^ m < ‖q‖⁻¹ :=
    hpow2 ▸ pow_lt_pow_left₀ h2 (norm_nonneg _) (by omega)
  have hq := norm_lt_one_of_annulus (q := q) (x := z ^ m) (by rwa [norm_pow]) (by rwa [norm_pow])
  have hj : ∀ j : Fin m, ‖q‖ < ‖z ^ ((j : ℕ) + 1)‖ ∧ ‖z ^ ((j : ℕ) + 1)‖ < ‖q‖⁻¹ := by
    intro j
    have hjm : (j : ℕ) + 1 ≤ m := j.2
    have hqi : 1 < ‖q‖⁻¹ := by
      refine one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ?_, hq⟩
      rintro rfl
      simp at hz2
      linarith [pow_nonneg (norm_nonneg z) m]
    rw [norm_pow]
    rcases le_or_gt 1 ‖z‖ with hz | hz
    · exact ⟨hq.trans_le (one_le_pow₀ hz),
        (pow_le_pow_right₀ hz hjm).trans_lt hz2⟩
    · exact ⟨hz1.trans_le (pow_le_pow_of_le_one (norm_nonneg _) hz.le hjm),
        (pow_le_one₀ (norm_nonneg _) hz.le).trans_lt hqi⟩
  rw [higherDysonSeriesZ_def, higherDysonSeries_def]
  refine tsum_congr fun n => ?_
  have hz0 : ∀ j : Fin m, z ^ ((j : ℕ) + 1) ≠ 0 := fun j =>
    norm_pos_iff.mp ((norm_nonneg q).trans_lt (hj j).1)
  have hs := fun j : Fin m => hasSum_gaussianLaurentCoeff n (hj j).1 (hj j).2
  obtain ⟨hP, -⟩ := hasSum_pi_prod m
    (fun j t => gaussianLaurentCoeff n t q * (z ^ ((j : ℕ) + 1)) ^ t)
    fun j => (summable_norm_iff (E := ℂ)).mpr (hs j).summable
  simp only [fun j => (hs j).tsum_eq, one_div] at hP
  rw [div_eq_mul_one_div, one_div, ← prod_inv_distrib, ← hP.tsum_eq]
  congr 1
  refine tsum_congr fun k => ?_
  have hz : z ≠ 0 := by
    rcases m with _ | m
    · omega
    · simpa using hz0 0
  rw [prod_mul_distrib]
  congr 1
  rw [← prod_zpow_eq_zpow_sum _ hz]
  refine prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  push_cast
  ring_nf

/-- **[AOS, Theorem 2.5]**, all claims together: for `0 < |q| < 1`,
* `C_n(·;q)` are the Laurent coefficients of `1/(xq, q/x; q)_n` on `|q| < |x| < |q|^{-1}`: the
  expansion holds there, and any coefficients with this expansion are `C_n(·;q)`;
* `C_0(0;q) = 1` and `C_0(k;q) = 0` for `k ≠ 0`;
* for `n ≥ 1` and `k ≥ 0`, `C_n(k;q) = ∑_{v ≥ 0} [n+k+v-1, k+v]_q [n+v-1, v]_q q^{k+2v}` and
  `C_n(-k;q) = C_n(k;q)`;
* for `m ≥ 1` and `|q|^{1/m} < |z| < |q|^{-1/m}`,
  `R_m(z;q) = ∑_{n ≥ 0} q^{n²} ∑_{𝐤 ∈ ℤ^m} (∏_j C_n(k_j;q)) z^{k_1 + 2k_2 + ⋯ + m k_m}`. -/
theorem gaussianLaurentCoeff_spec {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (∀ n : ℕ, ∀ x : ℂ, ‖q‖ < ‖x‖ → ‖x‖ < ‖q‖⁻¹ →
      HasSum (fun k : ℤ => gaussianLaurentCoeff n k q * x ^ k)
        (1 / (qPochhammer (x * q) q n * qPochhammer (q / x) q n))) ∧
    (∀ n : ℕ, ∀ c : ℤ → ℂ, (∀ x : ℂ, ‖q‖ < ‖x‖ → ‖x‖ < ‖q‖⁻¹ →
      HasSum (fun k => c k * x ^ k) (1 / (qPochhammer (x * q) q n * qPochhammer (q / x) q n))) →
      c = fun k => gaussianLaurentCoeff n k q) ∧
    gaussianLaurentCoeff 0 0 q = 1 ∧ (∀ k : ℤ, k ≠ 0 → gaussianLaurentCoeff 0 k q = 0) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, gaussianLaurentCoeff n k q = ∑' v : ℕ,
      gaussianBinomial (n + k + v - 1) (k + v) q * gaussianBinomial (n + v - 1) v q *
        q ^ (k + 2 * v)) ∧
    (∀ n : ℕ, ∀ k : ℤ, gaussianLaurentCoeff n (-k) q = gaussianLaurentCoeff n k q) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ z : ℂ, ‖q‖ ^ ((1 : ℝ) / m) < ‖z‖ → ‖z‖ < ‖q‖ ^ (-(1 : ℝ) / m) →
      higherDysonSeriesZ m z q = ∑' n : ℕ, q ^ (n ^ 2) *
        ∑' k : Fin m → ℤ, (∏ j, gaussianLaurentCoeff n (k j) q) *
          z ^ (∑ j : Fin m, ((j : ℤ) + 1) * k j)) :=
  ⟨fun n _ h1 h2 => hasSum_gaussianLaurentCoeff n h1 h2,
    fun n c hc => gaussianLaurentCoeff_unique n hq0 hq c hc,
    by simp [gaussianLaurentCoeff_zero], fun k hk => by simp [gaussianLaurentCoeff_zero, hk],
    fun _ hn k => gaussianLaurentCoeff_natCast hn k q, fun n k => gaussianLaurentCoeff_neg n k q,
    fun _ hm _ h1 h2 => higherDysonSeriesZ_eq_tsum_gaussianLaurentCoeff hm h1 h2⟩

end HigherDyson3
