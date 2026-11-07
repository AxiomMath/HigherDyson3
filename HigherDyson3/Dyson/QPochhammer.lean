/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Definitions

/-!
# `q`-Pochhammer symbols and the finite `q`-binomial theorem

For `|q| < 1`, the infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏_{l ≥ 0} (1 - a q^l)` converges,
splits as `(a;q)_∞ = (a;q)_n (aq^n;q)_∞`, and is nonzero when no factor vanishes. The Gaussian
coefficients `[A, B]_q = (q;q)_A / ((q;q)_B (q;q)_{A-B})` (`0 ≤ B ≤ A`, else `0`) give the
finite `q`-binomial theorem `1/(xq;q)_n = ∑_{a ≥ 0} [n+a-1, a]_q x^a q^a` for `n ≥ 1`,
`|q| < 1` and `|xq| < 1` [AOS, §2]. The paper gives no proof; the one here is the classical
induction on `n`: by the `q`-Pascal rule `[n+a, a] = ∑_{b ≤ a} q^b [n-1+b, b]`, and the series
for `n + 1` is the Cauchy product of `1/(1 - t)` with the series for `n` at `qt`.

## Main results

* `HigherDyson3.qPochhammerInf`: `(a;q)_∞`.
* `HigherDyson3.qPochhammer_mul_qPochhammerInf`: `(a;q)_n (aq^n;q)_∞ = (a;q)_∞`.
* `HigherDyson3.qPochhammerInf_ne_zero`: `(a;q)_∞ ≠ 0` when `a q^l ≠ 1` for all `l`.
* `HigherDyson3.gaussianBinomial`: the Gaussian coefficient `[A, B]_q`.
* `HigherDyson3.hasSum_qBinomial`: the finite `q`-binomial theorem.
-/

public section

noncomputable section

open Finset Filter Topology

namespace HigherDyson3

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏_{l ≥ 0} (1 - a q^l)` (Mathlib's
unconditional product; it converges for `|q| < 1`). -/
def qPochhammerInf (a q : ℂ) : ℂ := ∏' l : ℕ, (1 - a * q ^ l)

theorem qPochhammerInf_def (a q : ℂ) : qPochhammerInf a q = ∏' l : ℕ, (1 - a * q ^ l) := (rfl)

/-- The factors of `(a;q)_∞` form a multipliable family for `|q| < 1`. -/
theorem multipliable_qPochhammerInf (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun l : ℕ => 1 - a * q ^ l := by
  have hs : Summable fun l : ℕ => ‖-(a * q ^ l)‖ := by
    simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/-- Splitting off finitely many factors of a multipliable product over `ℕ` in `ℂ`. -/
theorem prod_range_mul_tprod_nat_add {f : ℕ → ℂ} (k : ℕ) (hf : Multipliable f)
    (hf' : Multipliable fun i => f (i + k)) :
    (∏ i ∈ range k, f i) * ∏' i, f (i + k) = ∏' i, f i := by
  have h1 := hf.hasProd.tendsto_prod_nat
  have h2 := (hf'.hasProd.tendsto_prod_nat).const_mul (∏ i ∈ range k, f i)
  have h3 : Tendsto (fun n => ∏ i ∈ range (k + n), f i) atTop (𝓝 (∏' i, f i)) :=
    h1.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  refine tendsto_nhds_unique (h2.congr fun n => ?_) h3
  rw [prod_range_add]
  congr 1
  exact prod_congr rfl fun i _ => by rw [add_comm]

/-- `(a;q)_n (aq^n;q)_∞ = (a;q)_∞` for `|q| < 1`. -/
theorem qPochhammer_mul_qPochhammerInf (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammer a q n * qPochhammerInf (a * q ^ n) q = qPochhammerInf a q := by
  have hshift : (fun i => 1 - a * q ^ (i + n)) = fun l => 1 - a * q ^ n * q ^ l :=
    funext fun i => by ring
  have h := prod_range_mul_tprod_nat_add n (multipliable_qPochhammerInf a hq)
    (by rw [hshift]; exact multipliable_qPochhammerInf (a * q ^ n) hq)
  rw [qPochhammer, qPochhammerInf, qPochhammerInf, ← h]
  congr 1
  exact tprod_congr fun l => by ring

/-- `(a;q)_∞ = (1 - a)(aq;q)_∞` for `|q| < 1`. -/
theorem qPochhammerInf_eq_one_sub_mul (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = (1 - a) * qPochhammerInf (a * q) q := by
  rw [← qPochhammer_mul_qPochhammerInf a hq 1]
  simp [qPochhammer]

/-- `(a;q)_∞ ≠ 0` for `|q| < 1` when no factor vanishes. -/
theorem qPochhammerInf_ne_zero {a q : ℂ} (hq : ‖q‖ < 1) (ha : ∀ l : ℕ, a * q ^ l ≠ 1) :
    qPochhammerInf a q ≠ 0 := by
  have hs : Summable fun l : ℕ => -(a * q ^ l) := by
    refine (summable_norm_iff (E := ℂ)).mp ?_
    simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  have hne : ∀ l : ℕ, 1 - a * q ^ l ≠ 0 := fun l h => ha l (sub_eq_zero.mp h).symm
  have h := Complex.cexp_tsum_eq_tprod hne
    (by simpa [sub_eq_add_neg] using Complex.summable_log_one_add_of_summable hs)
  rw [qPochhammerInf, ← h]
  exact Complex.exp_ne_zero _

/-- `(a;q)_n ≠ 0` when no factor vanishes. -/
theorem qPochhammer_ne_zero {a q : ℂ} {n : ℕ} (ha : ∀ l < n, a * q ^ l ≠ 1) :
    qPochhammer a q n ≠ 0 :=
  prod_ne_zero_iff.mpr fun l hl h => ha l (mem_range.mp hl) (sub_eq_zero.mp h).symm

/-- `(q;q)_n ≠ 0` for `|q| < 1`. -/
theorem qPochhammer_self_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : qPochhammer q q n ≠ 0 :=
  qPochhammer_ne_zero fun l _ h => by
    have : ‖q * q ^ l‖ < 1 := by
      rw [norm_mul, norm_pow, ← pow_succ']; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    simp [h] at this

/-- The Gaussian coefficient `[A, B]_q = (q;q)_A / ((q;q)_B (q;q)_{A-B})` for `B ≤ A`, and `0`
otherwise [AOS, §2], for natural numbers `A`, `B`. -/
def gaussianBinomial (A B : ℕ) (q : ℂ) : ℂ :=
  if B ≤ A then qPochhammer q q A / (qPochhammer q q B * qPochhammer q q (A - B)) else 0

/-- `(q;q)_{k+1} = (q;q)_k (1 - q^{k+1})`. -/
private theorem qPochhammer_self_succ (q : ℂ) (k : ℕ) :
    qPochhammer q q (k + 1) = qPochhammer q q k * (1 - q ^ (k + 1)) := by
  rw [qPochhammer, prod_range_succ, pow_succ']
  rfl

/-- `[n + a, a]_q` in terms of `q`-Pochhammer symbols. -/
private theorem gaussianBinomial_add_left (n a : ℕ) (q : ℂ) :
    gaussianBinomial (n + a) a q =
      qPochhammer q q (n + a) / (qPochhammer q q a * qPochhammer q q n) := by
  rw [gaussianBinomial, ite_eq_left (by omega), Nat.add_sub_cancel]

private theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := by simp [qPochhammer]

/-- `[a, a]_q = 1` for `|q| < 1`. -/
private theorem gaussianBinomial_self {q : ℂ} (hq : ‖q‖ < 1) (a : ℕ) :
    gaussianBinomial a a q = 1 := by
  rw [gaussianBinomial, ite_eq_left le_rfl, Nat.sub_self, qPochhammer_zero, mul_one,
    div_self (qPochhammer_self_ne_zero hq a)]

/-- `[a, 0]_q = 1` for `|q| < 1`. -/
private theorem gaussianBinomial_zero_right {q : ℂ} (hq : ‖q‖ < 1) (a : ℕ) :
    gaussianBinomial a 0 q = 1 := by
  rw [gaussianBinomial, ite_eq_left (Nat.zero_le a), Nat.sub_zero, qPochhammer_zero, one_mul,
    div_self (qPochhammer_self_ne_zero hq a)]

/-- The `q`-Pascal rule: `[n+1+a, a]_q = ∑_{b ≤ a} q^b [n+b, b]_q` for `|q| < 1`. -/
private theorem gaussianBinomial_succ_eq_sum {q : ℂ} (hq : ‖q‖ < 1) (n a : ℕ) :
    gaussianBinomial (n + 1 + a) a q =
      ∑ b ∈ range (a + 1), q ^ b * gaussianBinomial (n + b) b q := by
  have hP := qPochhammer_self_ne_zero hq
  induction a with
  | zero =>
    simp only [add_zero, zero_add, range_one, sum_singleton, pow_zero, one_mul,
      gaussianBinomial_zero_right hq]
  | succ a ih =>
    rw [sum_range_succ, ← ih]
    simp only [gaussianBinomial_add_left]
    rw [show n + 1 + (a + 1) = n + a + 1 + 1 by ring, show n + 1 + a = n + a + 1 by ring,
      show n + (a + 1) = n + a + 1 by ring]
    rw [qPochhammer_self_succ q (n + a + 1), qPochhammer_self_succ q a, qPochhammer_self_succ q n]
    have h1 : (1 - q ^ (a + 1)) ≠ 0 := fun h => by
      have := qPochhammer_self_succ q a ▸ hP (a + 1); simp [h] at this
    have h2 : (1 - q ^ (n + 1)) ≠ 0 := fun h => by
      have := qPochhammer_self_succ q n ▸ hP (n + 1); simp [h] at this
    have h3 := hP a
    have h4 := hP n
    field_simp
    ring

/-- `1/(t;q)_{n+1} = ∑_{a ≥ 0} [n+a, a]_q t^a` for `|q| < 1` and `|t| < 1`. -/
private theorem hasSum_gaussianBinomial_mul_pow {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    ∀ t : ℂ, ‖t‖ < 1 →
      HasSum (fun a => gaussianBinomial (n + a) a q * t ^ a) (qPochhammer t q (n + 1))⁻¹ := by
  induction n with
  | zero =>
    intro t ht
    simpa [gaussianBinomial_self hq, qPochhammer] using hasSum_geometric_of_norm_lt_one ht
  | succ n ih =>
    intro t ht
    have hqt : ‖q * t‖ < 1 := by
      rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg t]
    have hg := ih (q * t) hqt
    have hf := hasSum_geometric_of_norm_lt_one ht
    have hfn : Summable fun a => ‖t ^ a‖ := (summable_norm_iff (E := ℂ)).mpr hf.summable
    have hgn : Summable fun b => ‖gaussianBinomial (n + b) b q * (q * t) ^ b‖ :=
      (summable_norm_iff (E := ℂ)).mpr hg.summable
    have hcp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
    have hcs := (summable_norm_iff (E := ℂ)).mp
      (summable_norm_sum_mul_range_of_summable_norm hfn hgn)
    rw [hf.tsum_eq, hg.tsum_eq] at hcp
    have hterm : ∀ a, ∑ k ∈ range (a + 1),
        t ^ k * (gaussianBinomial (n + (a - k)) (a - k) q * (q * t) ^ (a - k)) =
        gaussianBinomial (n + 1 + a) a q * t ^ a := by
      intro a
      rw [gaussianBinomial_succ_eq_sum hq n a, sum_mul,
        ← sum_range_reflect (fun b => q ^ b * gaussianBinomial (n + b) b q * t ^ a)]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [show a + 1 - 1 - k = a - k by omega, mul_pow]
      calc t ^ k * (gaussianBinomial (n + (a - k)) (a - k) q * (q ^ (a - k) * t ^ (a - k)))
          = q ^ (a - k) * gaussianBinomial (n + (a - k)) (a - k) q * (t ^ k * t ^ (a - k)) := by
            ring
        _ = _ := by rw [← pow_add, Nat.add_sub_cancel' hk']
    have hprod : qPochhammer t q (n + 1 + 1) = (1 - t) * qPochhammer (q * t) q (n + 1) := by
      rw [qPochhammer, prod_range_succ', qPochhammer, mul_comm]
      simp only [pow_zero, mul_one]
      congr 1
      exact prod_congr rfl fun l _ => by ring
    have : HasSum (fun a => gaussianBinomial (n + 1 + a) a q * t ^ a)
        ((1 - t)⁻¹ * (qPochhammer (q * t) q (n + 1))⁻¹) := by
      rw [hcp]
      simpa only [hterm] using hcs.hasSum
    rwa [hprod, mul_inv]

/-- **The finite `q`-binomial theorem** [AOS, §2]: for `n ≥ 1`, `|q| < 1` and `|xq| < 1`,
`1/(xq;q)_n = ∑_{a ≥ 0} [n+a-1, a]_q x^a q^a`, the series converging absolutely. -/
theorem hasSum_qBinomial {n : ℕ} (hn : 1 ≤ n) {q x : ℂ} (hq : ‖q‖ < 1) (hxq : ‖x * q‖ < 1) :
    HasSum (fun a => gaussianBinomial (n + a - 1) a q * x ^ a * q ^ a)
      (1 / qPochhammer (x * q) q n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := hasSum_gaussianBinomial_mul_pow hq n (x * q) hxq
  rw [one_div]
  refine h.congr_fun fun a => ?_
  rw [show n + 1 + a - 1 = n + a by omega, mul_pow, mul_assoc]

end HigherDyson3
