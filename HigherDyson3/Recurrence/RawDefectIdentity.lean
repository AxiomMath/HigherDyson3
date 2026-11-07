/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.FiniteRecurrence

/-!
# The raw defect identity

Let `m ≥ 2`, `d = 2m + 1`, `x ≠ 0`, `0 < ‖q‖ < 1` and `u ≠ 0` with `x u ≠ 1`. Write
`X_i = X_i^{(m)}(x; q)`, `g = G_d(x; q)` and `S = ∑_{r=0}^{d-1} u^{2-r}`. The raw defect
`ℬ_{d,x}(u; q)` satisfies
`ℬ_{d,x}(u; q) - S g / (1 - x u) = u^{3-d} R_{d,x}(u; q) - C_x u² g / (1 - x u)`.

The finite recurrence with `j = 1` and `j = 0` expresses `X_{-1}` and `X_{-2}` through
`X_0, …, X_{d-2}` and `g`. Substituting these into the raw defect leaves a multiple of `g` and a
linear combination of `X_0, …, X_{d-2}`. The coefficient of `x^k X_k` is compared with that in
`u^{3-d} R_{d,x}(u; q)` by reflecting the summation index, and the coefficient of `g` is compared
with `-C_x u² / (1 - x u)` through the geometric sums
`(1 - x u) ∑_{i=0}^{r-3} x^i u^{i+2-r} = u^{2-r} - x^{r-2}`.

## Main results

* `HigherDyson3.rawDefect_sub_eq`: the raw defect identity.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- Splitting off the first three terms of a sum over `range (M + 4)`. -/
private lemma rawDefectIdentity_split {f : ℕ → ℂ} (M : ℕ) :
    ∑ r ∈ range (M + 4), f r = f 0 + f 1 + f 2 + ∑ r ∈ Icc 3 (M + 3), f r := by
  induction M with
  | zero => simp [sum_range_succ]
  | succ M ih =>
    rw [show M + 1 + 4 = (M + 4) + 1 by ring, sum_range_succ, ih,
      show M + 1 + 3 = (M + 3) + 1 by ring, sum_Icc_succ_top (a := 3) (b := M + 3) (by omega)]
    ring

/-- Exchanging the order of the double sum in the raw defect. -/
private lemma rawDefectIdentity_swap (M : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), F r i =
      ∑ i ∈ range (M + 1), ∑ r ∈ Icc (i + 3) (M + 3), F r i :=
  Finset.sum_comm' (by intro r i; simp only [mem_Icc, mem_range]; omega)

/-- `u^{3-d} u^a = u^{a+3-d}` with `d = M + 4`. -/
private lemma rawDefectIdentity_pow {u : ℂ} (hu : u ≠ 0) (M a : ℕ) :
    u ^ (3 - ((M : ℤ) + 4)) * u ^ a = u ^ ((a : ℤ) - (M + 1)) := by
  rw [← zpow_natCast, ← zpow_add₀ hu]
  congr 1

/-- The inner coefficient of `x^k X_k` for `k ≤ d - 4`. -/
private lemma rawDefectIdentity_inner {u : ℂ} (hu : u ≠ 0) {M k : ℕ} (hk : k ≤ M) :
    u ^ (3 - ((M : ℤ) + 4)) * ∑ a ∈ Icc k (M + 2), u ^ a =
      1 + u + ∑ r ∈ Icc (k + 3) (M + 3), u ^ ((k : ℤ) + 2 - r) := by
  rw [mul_sum]
  simp_rw [rawDefectIdentity_pow hu]
  rw [show M + 2 = (M + 1) + 1 by ring, sum_Icc_succ_top (by omega),
    sum_Icc_succ_top (by omega)]
  have hb : ∑ a ∈ Icc k M, u ^ ((a : ℤ) - (M + 1)) =
      ∑ r ∈ Icc (k + 3) (M + 3), u ^ ((k : ℤ) + 2 - r) := by
    refine Finset.sum_nbij' (fun a => M + k + 3 - a) (fun r => M + k + 3 - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha; omega
    · intro a ha; simp only [mem_Icc] at ha; omega
    · intro a ha
      simp only [mem_Icc] at ha
      congr 1
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
  rw [hb]
  have h1 : u ^ (((M + 1 : ℕ) : ℤ) - (M + 1)) = 1 := by simp
  have h2 : u ^ (((M + 1 + 1 : ℕ) : ℤ) - (M + 1)) = u := by
    rw [show ((M + 1 + 1 : ℕ) : ℤ) - (M + 1) = 1 by push_cast; ring, zpow_one]
  rw [h1, h2]
  ring

/-- The `X`-part of `u^{3-d} R_{d,x}(u; q)`. -/
private lemma rawDefectIdentity_XPart {u : ℂ} (hu : u ≠ 0) (M : ℕ) (Y : ℕ → ℂ) :
    u ^ (3 - ((M : ℤ) + 4)) * ∑ k ∈ range (M + 3), Y k * ∑ a ∈ Icc k (M + 2), u ^ a =
      ∑ k ∈ range (M + 2), Y k + u * ∑ k ∈ range (M + 3), Y k +
        ∑ k ∈ range (M + 1), Y k * ∑ r ∈ Icc (k + 3) (M + 3), u ^ ((k : ℤ) + 2 - r) := by
  rw [mul_sum, show M + 3 = (M + 1) + 1 + 1 by ring, show M + 2 = (M + 1) + 1 by ring,
    sum_range_succ _ (M + 1 + 1), sum_range_succ _ (M + 1), sum_range_succ _ (M + 1),
    sum_range_succ Y (M + 1 + 1), sum_range_succ Y (M + 1)]
  have hmain : ∑ k ∈ range (M + 1), u ^ (3 - ((M : ℤ) + 4)) *
      (Y k * ∑ a ∈ Icc k (M + 1 + 1), u ^ a) =
      ∑ k ∈ range (M + 1), (Y k + u * Y k +
        Y k * ∑ r ∈ Icc (k + 3) (M + 1 + 1 + 1), u ^ ((k : ℤ) + 2 - r)) := by
    refine sum_congr rfl fun k hk => ?_
    rw [mul_left_comm, rawDefectIdentity_inner hu (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    ring
  rw [hmain, sum_add_distrib, sum_add_distrib, ← mul_sum]
  have e1 : u ^ (3 - ((M : ℤ) + 4)) * ∑ a ∈ Icc (M + 1) (M + 1 + 1), u ^ a = 1 + u := by
    rw [mul_sum, sum_Icc_succ_top (by omega), Icc_self, sum_singleton,
      rawDefectIdentity_pow hu, rawDefectIdentity_pow hu]
    have h1 : u ^ (((M + 1 : ℕ) : ℤ) - (M + 1)) = 1 := by simp
    have h2 : u ^ (((M + 1 + 1 : ℕ) : ℤ) - (M + 1)) = u := by
      rw [show ((M + 1 + 1 : ℕ) : ℤ) - (M + 1) = 1 by push_cast; ring, zpow_one]
    rw [h1, h2]
  have e2 : u ^ (3 - ((M : ℤ) + 4)) * ∑ a ∈ Icc (M + 1 + 1) (M + 1 + 1), u ^ a = u := by
    rw [Icc_self, sum_singleton, rawDefectIdentity_pow hu,
      show ((M + 1 + 1 : ℕ) : ℤ) - (M + 1) = 1 by push_cast; ring, zpow_one]
  linear_combination Y (M + 1) * e1 + Y (M + 1 + 1) * e2

/-- The geometric sums giving the `g`-part of the raw defect. -/
private lemma rawDefectIdentity_gPart {x u : ℂ} (hu : u ≠ 0) (M : ℕ) :
    (1 - x * u) * ∑ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) =
      ∑ r ∈ Icc 3 (M + 3), u ^ (2 - (r : ℤ)) - ∑ r ∈ Icc 3 (M + 3), x ^ (r - 2) := by
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun r hr => ?_
  have hr3 : 3 ≤ r := (mem_Icc.mp hr).1
  have hterm : ∀ i : ℕ, x ^ i * u ^ ((i : ℤ) + 2 - r) = (x * u) ^ i * u ^ (2 - (r : ℤ)) := by
    intro i
    rw [mul_pow, mul_assoc, ← zpow_natCast u i, ← zpow_add₀ hu]
    congr 2
    ring
  simp_rw [hterm]
  rw [← sum_mul, ← mul_assoc, mul_neg_geom_sum, sub_mul, one_mul, mul_pow, mul_assoc,
    ← zpow_natCast u, ← zpow_add₀ hu, Nat.cast_sub (by omega)]
  simp

/-- The raw defect identity for an abstract family `X` satisfying the boundary recurrences,
with `d = M + 4`. -/
private lemma rawDefectIdentity_core (M : ℕ) {x u q g : ℂ} (X : ℤ → ℂ) (hx : x ≠ 0)
    (hu : u ≠ 0) (hxu : x * u ≠ 1)
    (h1 : ∑ r ∈ range (M + 4), x ^ r * X (1 + r - 2) - q ^ ((1 : ℤ) - 1) * X 1 =
      (∑ s ∈ range (M + 4), x ^ s) * g)
    (h0 : ∑ r ∈ range (M + 4), x ^ r * X (0 + r - 2) - q ^ ((0 : ℤ) - 1) * X 0 =
      (∑ s ∈ range (M + 4), x ^ s) * g) :
    (x ^ 2)⁻¹ * (X (-2) - g) + x⁻¹ * (1 + u) * (X (-1) - g) -
        ∑ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * (X i - g) -
        (∑ r ∈ range (M + 4), u ^ (2 - (r : ℤ))) * g / (1 - x * u) =
      u ^ (3 - ((M : ℤ) + 4)) * (q⁻¹ * (x ^ 2)⁻¹ * X 0 * u ^ (M + 1) +
          x⁻¹ * X 1 * u ^ (M + 2) -
          ∑ k ∈ range (M + 3), x ^ k * X k * ∑ a ∈ Icc k (M + 2), u ^ a) -
        (∑ s ∈ range (M + 4), x ^ s) * (u ^ 2 / (1 - x * u)) * g := by
  set C := ∑ s ∈ range (M + 4), x ^ s with hC
  set Eb := ∑ k ∈ range (M + 2), x ^ k * X k with hEb
  set Ec := ∑ k ∈ range (M + 3), x ^ k * X k with hEc
  set Ea := ∑ k ∈ range (M + 1), x ^ k * X k * ∑ r ∈ Icc (k + 3) (M + 3), u ^ ((k : ℤ) + 2 - r)
    with hEa
  set Sg := ∑ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) with hSg
  set SU := ∑ r ∈ Icc 3 (M + 3), u ^ (2 - (r : ℤ)) with hSU
  set P := ∑ r ∈ Icc 3 (M + 3), x ^ (r - 2) with hP
  -- the boundary recurrences
  have h1' : X (-1) + x * Ec - X 1 = C * g := by
    rw [← h1, show M + 4 = (M + 3) + 1 by ring, sum_range_succ', hEc, mul_sum]
    have : ∀ k ∈ range (M + 3), x ^ (k + 1) * X (1 + ((k + 1 : ℕ) : ℤ) - 2) = x * (x ^ k * X k) :=
      fun k _ => by rw [pow_succ]; push_cast; ring_nf
    rw [sum_congr rfl this]
    norm_num
    ring
  have h0' : X (-2) + x * X (-1) + x ^ 2 * Eb - q⁻¹ * X 0 = C * g := by
    rw [← h0, show M + 4 = (M + 2) + 1 + 1 by ring, sum_range_succ', sum_range_succ', hEb,
      mul_sum]
    have : ∀ k ∈ range (M + 2), x ^ (k + 1 + 1) * X (0 + ((k + 1 + 1 : ℕ) : ℤ) - 2) =
        x ^ 2 * (x ^ k * X k) :=
      fun k _ => by push_cast; ring_nf
    rw [sum_congr rfl this]
    norm_num
    ring
  -- the double sum
  have hD : ∑ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * (X i - g) =
      Ea - g * Sg := by
    have : ∀ r ∈ Icc 3 (M + 3), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * (X i - g) =
        ∑ i ∈ range (r - 2), x ^ i * X i * u ^ ((i : ℤ) + 2 - r) -
          g * ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) := fun r _ => by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [sum_congr rfl this, sum_sub_distrib, rawDefectIdentity_swap, hEa, hSg]
    simp only [mul_sum]
  -- the polynomial part
  have hR := rawDefectIdentity_XPart hu M (fun k => x ^ k * X k)
  have hc0 : u ^ (3 - ((M : ℤ) + 4)) * u ^ (M + 1) = 1 := by
    rw [rawDefectIdentity_pow hu]; push_cast; simp
  have hc1 : u ^ (3 - ((M : ℤ) + 4)) * u ^ (M + 2) = u := by
    rw [rawDefectIdentity_pow hu, show (((M + 2 : ℕ)) : ℤ) - (M + 1) = 1 by push_cast; ring,
      zpow_one]
  -- the `g`-part
  have gA := rawDefectIdentity_gPart (x := x) hu M
  have gS : ∑ r ∈ range (M + 4), u ^ (2 - (r : ℤ)) = u ^ 2 + u + 1 + SU := by
    rw [rawDefectIdentity_split, hSU]; norm_num
  have gC : C = 1 + x + x ^ 2 + x ^ 2 * P := by
    rw [hC, rawDefectIdentity_split, hP, mul_sum]
    have : ∀ r ∈ Icc 3 (M + 3), x ^ r = x ^ 2 * x ^ (r - 2) := fun r hr => by
      rw [← pow_add]; congr 1; have := (mem_Icc.mp hr).1; omega
    rw [sum_congr rfl this]
    ring
  have hxu' : 1 - x * u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxu)
  have hg : (x ^ 2)⁻¹ * C + x⁻¹ * u * C - (x ^ 2)⁻¹ - x⁻¹ - x⁻¹ * u + Sg +
      (C * u ^ 2 - (u ^ 2 + u + 1 + SU)) / (1 - x * u) = 0 := by
    rw [← hSg, ← hSU, ← hP] at gA
    field_simp
    linear_combination x ^ 2 * gA + gC
  have hR' : u ^ (3 - ((M : ℤ) + 4)) * (q⁻¹ * (x ^ 2)⁻¹ * X 0 * u ^ (M + 1) +
      x⁻¹ * X 1 * u ^ (M + 2) -
      ∑ k ∈ range (M + 3), x ^ k * X k * ∑ a ∈ Icc k (M + 2), u ^ a) =
      q⁻¹ * (x ^ 2)⁻¹ * X 0 + x⁻¹ * u * X 1 - (Eb + u * Ec + Ea) := by
    rw [mul_sub, hR]
    linear_combination q⁻¹ * (x ^ 2)⁻¹ * X 0 * hc0 + x⁻¹ * X 1 * hc1
  rw [hD, gS, hR']
  linear_combination (norm := skip) (x ^ 2)⁻¹ * h0' + x⁻¹ * u * h1' + g * hg
  field_simp
  ring

/-- **The raw defect identity.** For `m ≥ 2`, `d = 2m + 1`, `x ≠ 0`, `0 < ‖q‖ < 1`, `u ≠ 0` and
`x u ≠ 1`,
`ℬ_{d,x}(u; q) - (∑_{r=0}^{d-1} u^{2-r}) G_d(x; q) / (1 - x u)
  = u^{3-d} R_{d,x}(u; q) - C_x u² / (1 - x u) G_d(x; q)`. -/
theorem rawDefect_sub_eq {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) (hu : u ≠ 0) (hxu : x * u ≠ 1) :
    rawDefect m x u q -
        (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * GProduct m x q / (1 - x * u) =
      u ^ (3 - (2 * m + 1 : ℤ)) * (defectPoly m x q).eval u -
        Cx m x * (u ^ 2 / (1 - x * u)) * GProduct m x q := by
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  have h1 := cyclotomic_XSeries_recurrence hm x hq hq1 1
  have h0 := cyclotomic_XSeries_recurrence hm x hq hq1 0
  obtain ⟨M, hM⟩ : ∃ M, 2 * m + 1 = M + 4 := ⟨2 * m - 3, by omega⟩
  have hMz : (2 * (m : ℤ) + 1) = (M : ℤ) + 4 := by exact_mod_cast hM
  simp only [Cx, cyclotomicSum, hM] at h1 h0
  simp only [rawDefect, defectPoly, Cx, cyclotomicSum, hM, hMz, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum]
  exact rawDefectIdentity_core M (fun j => XSeries m x j q) hx hu hxu h1 h0

end HigherDyson3
