/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Values.GShift
public import HigherDyson3.Recurrence.SeedSummable

/-!
# The shift of the seed, raw form

Let `m ≥ 2`, `d = 2m + 1`, `S(u) = ∑_{r=0}^{d-1} u^{2-r}` and let `ℬ_{d,x}(u; q)` be the raw
defect. For `x ≠ 0`, `0 < |q| < 1`, `u ≠ 0` and `x u q^k ≠ 1` for all `k`, the seed satisfies
`𝒢_{d,x}(q u; q) = x² q S(u) 𝒢_{d,x}(u; q) + q ℬ_{d,x}(u; q) - q S(u) G_d(x; q) / (1 - x u)`.

Write `a_N = q^{N²} g_N` and `w_N = x u q^N`. The product shift gives
`a_{N-1} = q ∑_r x^r q^{(r-2)N} a_N`, and for `w ≠ 0, 1` each `x^r q^{(r-2)N} / (1 - w_N)`
splits as `x² u^{2-r} / (1 - w_N)` plus a Laurent polynomial in `q^N` (a geometric sum for
`r ≥ 3`). Summing over `N ≥ 1` the first parts give the seed at `u` without its `N = 0` term,
and the second parts give the raw defect, the series `X_i` without their `N = 0` terms.

## Main results

* `HigherDyson3.seed_mul_eq_rawDefect`: the raw shift identity for the seed.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- For `r ≥ 2`, `x^r Q^{r-2} - x² u^{2-r} = -(1 - x u Q) x² ∑_{i<r-2} x^i u^{i+2-r} Q^i`. -/
private lemma seedShiftRaw_geom {x u Q : ℂ} (hu : u ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    x ^ r * Q ^ ((r : ℤ) - 2) - x ^ 2 * u ^ (2 - (r : ℤ)) =
      -((1 - x * u * Q) * x ^ 2 *
        ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * Q ^ (i : ℤ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have hterm : ∀ i : ℕ, x ^ i * u ^ ((i : ℤ) + 2 - ((n + 2 : ℕ) : ℤ)) * Q ^ (i : ℤ) =
      (u ^ n)⁻¹ * (x * u * Q) ^ i := by
    intro i
    rw [show (i : ℤ) + 2 - ((n + 2 : ℕ) : ℤ) = (i : ℤ) + -(n : ℤ) by push_cast; ring,
      zpow_add₀ hu, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Nat.add_sub_cancel]
  rw [show ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) by push_cast; ring,
    show 2 - ((n + 2 : ℕ) : ℤ) = -(n : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, zpow_natCast]
  have hun : u ^ n ≠ 0 := pow_ne_zero n hu
  calc x ^ (n + 2) * Q ^ n - x ^ 2 * (u ^ n)⁻¹
      = -(x ^ 2 * (u ^ n)⁻¹ * (1 - (x * u * Q) ^ n)) := by
        field_simp
        ring
    _ = _ := by
      rw [← mul_neg_geom_sum (x * u * Q) n]
      ring

/-- The algebraic core of the termwise identity: with `Q = q^N` and `w = x u Q`,
`∑_r x^r Q^{r-2} = x² S(u) + (1 - w) x² (x⁻² Q⁻² + x⁻¹ (1+u) Q⁻¹ - ∑_{r,i} x^i u^{i+2-r} Q^i)`. -/
private lemma seedShiftRaw_core {m : ℕ} (hm : 2 ≤ m) {x u Q : ℂ} (hx : x ≠ 0) (hu : u ≠ 0)
    (hQ : Q ≠ 0) :
    ∑ r ∈ range (2 * m + 1), x ^ r * Q ^ ((r : ℤ) - 2) =
      x ^ 2 * ∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ)) +
        (1 - x * u * Q) * x ^ 2 * ((x ^ 2)⁻¹ * Q ^ (-2 : ℤ) + x⁻¹ * (1 + u) * Q ^ (-1 : ℤ) -
          ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
            x ^ i * u ^ ((i : ℤ) + 2 - r) * Q ^ (i : ℤ)) := by
  have hIcc : Icc 3 (2 * m + 1 - 1) = Ico 3 (2 * m + 1) := by
    ext r
    simp only [mem_Icc, mem_Ico]
    omega
  have hsplit : ∀ f : ℕ → ℂ, ∑ r ∈ range (2 * m + 1), f r =
      ∑ r ∈ range 3, f r + ∑ r ∈ Ico 3 (2 * m + 1), f r := fun f =>
    (Finset.sum_range_add_sum_Ico f (by omega)).symm
  have hIco : ∑ r ∈ Ico 3 (2 * m + 1),
      (x ^ r * Q ^ ((r : ℤ) - 2) - x ^ 2 * u ^ (2 - (r : ℤ))) =
      -((1 - x * u * Q) * x ^ 2 * ∑ r ∈ Ico 3 (2 * m + 1), ∑ i ∈ range (r - 2),
        x ^ i * u ^ ((i : ℤ) + 2 - r) * Q ^ (i : ℤ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r hr =>
      seedShiftRaw_geom hu (by simp only [mem_Ico] at hr; omega)
  rw [hIcc, Finset.mul_sum, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, hsplit, hIco]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  field_simp
  ring

/-- The termwise identity: with `N = k + 1`, `a_N = q^{N²} g_N` and `w_N = x u q^N`,
`a_{N-1} / (1 - w_N) = q x² S(u) a_N / (1 - w_N) + q x² D_N`, where `D_N` is the summand at `N`
of the raw defect's series. -/
private lemma seedShiftRaw_term {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) {q : ℂ}
    (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {u : ℂ} (hu : u ≠ 0) (k : ℕ)
    (hk : x * u * q ^ (k + 1) ≠ 1) :
    q ^ (k ^ 2) * gTail m x k q / (1 - x * (q * u) * q ^ k) =
      q * x ^ 2 * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) *
          (q ^ ((k + 1) ^ 2) * gTail m x (k + 1) q / (1 - x * u * q ^ (k + 1))) +
        q * x ^ 2 * ((x ^ 2)⁻¹ * (q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + (-2) * ((k + 1 : ℕ) : ℤ)) *
            gTail m x (k + 1) q) +
          x⁻¹ * (1 + u) * (q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + (-1) * ((k + 1 : ℕ) : ℤ)) *
            gTail m x (k + 1) q) -
          ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) *
            (q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + (i : ℤ) * ((k + 1 : ℕ) : ℤ)) *
              gTail m x (k + 1) q)) := by
  set Q : ℂ := q ^ (k + 1) with hQdef
  set P : ℂ := q ^ ((k + 1) ^ 2) * gTail m x (k + 1) q with hPdef
  have hQ : Q ≠ 0 := pow_ne_zero _ hq0
  have hw : 1 - x * u * Q ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  have hT : ∀ i : ℤ, q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + i * ((k + 1 : ℕ) : ℤ)) *
      gTail m x (k + 1) q = P * Q ^ i := by
    intro i
    rw [zpow_add₀ hq0, hPdef, hQdef, ← zpow_natCast q (k + 1), ← zpow_mul, mul_comm i]
    push_cast
    rw [← zpow_natCast q ((k + 1) ^ 2)]
    push_cast
    ring
  have hg : gTail m x k q = (∑ r ∈ range (2 * m + 1), x ^ r * Q ^ r) * gTail m x (k + 1) q := by
    unfold gTail
    rw [GProduct_eq_cyclotomicSum_mul_GProduct hm hq1, mul_assoc, ← pow_succ, cyclotomicSum]
    simp_rw [mul_pow]
    rfl
  have hk2 : q ^ (k ^ 2) = q * q ^ ((k + 1) ^ 2) * Q ^ (-2 : ℤ) := by
    rw [hQdef, ← zpow_natCast q (k + 1), ← zpow_mul, ← zpow_natCast q (k ^ 2),
      ← zpow_natCast q ((k + 1) ^ 2), ← zpow_one_add₀ hq0, ← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  have hden : x * (q * u) * q ^ k = x * u * Q := by
    rw [hQdef, pow_succ]
    ring
  have hsumQ : Q ^ (-2 : ℤ) * ∑ r ∈ range (2 * m + 1), x ^ r * Q ^ r =
      ∑ r ∈ range (2 * m + 1), x ^ r * Q ^ ((r : ℤ) - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sub_eq_add_neg, zpow_add₀ hQ, zpow_natCast]
    ring
  have hdouble : ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
      x ^ i * u ^ ((i : ℤ) + 2 - r) * (P * Q ^ (i : ℤ)) =
      P * ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
        x ^ i * u ^ ((i : ℤ) + 2 - r) * Q ^ (i : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hT]
  rw [hdouble, hden, hg, hk2]
  have hL : q * q ^ ((k + 1) ^ 2) * Q ^ (-2 : ℤ) *
      ((∑ r ∈ range (2 * m + 1), x ^ r * Q ^ r) * gTail m x (k + 1) q) =
      q * P * (Q ^ (-2 : ℤ) * ∑ r ∈ range (2 * m + 1), x ^ r * Q ^ r) := by
    rw [hPdef]
    ring
  rw [hL, hsumQ, seedShiftRaw_core hm hx hu hQ]
  field_simp

/-- **Shift of the seed, raw form.** For `m ≥ 2`, `d = 2m + 1`, `x ≠ 0`, `0 < ‖q‖ < 1` and
`u ≠ 0` with `x u q^k ≠ 1` for all `k ∈ ℕ`,
`𝒢_{d,x}(q u; q) = x² q S(u) 𝒢_{d,x}(u; q) + q ℬ_{d,x}(u; q) - q S(u) G_d(x; q) / (1 - x u)`,
where `S(u) = ∑_{r=0}^{d-1} u^{2-r}`. -/
theorem seed_mul_eq_rawDefect {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) {u : ℂ} (hu : u ≠ 0) (hxu : ∀ k : ℕ, x * u * q ^ k ≠ 1) :
    seed m x (q * u) q =
      x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
        q * rawDefect m x u q -
        q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * GProduct m x q / (1 - x * u) := by
  set S : ℂ := ∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ)) with hS
  set T : ℤ → ℕ → ℂ := fun i k => q ^ ((k : ℤ) ^ 2 + i * k) * gTail m x k q with hT
  set b : ℕ → ℂ := fun k => q ^ (k ^ 2) * gTail m x k q / (1 - x * u * q ^ k) with hb
  set D : ℕ → ℂ := fun N => (x ^ 2)⁻¹ * T (-2) N + x⁻¹ * (1 + u) * T (-1) N -
    ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) *
      T i N with hD
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hTsum : ∀ i, Summable (fun k => T i (k + 1)) := fun i =>
    (summable_nat_add_iff 1).mpr (summable_norm_XSeries_term hm x i hq0 hq1).of_norm
  have hTshift : ∀ i, ∑' k, T i (k + 1) = XSeries m x i q - GProduct m x q := fun i => by
    have h0 : T i 0 = GProduct m x q := by simp [hT, gTail]
    rw [XSeries, (summable_norm_XSeries_term hm x i hq0 hq1).of_norm.tsum_eq_zero_add]
    simp only [hT] at h0 ⊢
    rw [h0]
    ring
  have hbsum : Summable (fun k => b (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_norm_seed_term hm x hq0 hq1 u).of_norm
  have hbshift : ∑' k, b (k + 1) = x ^ 2 * seed m x u q - GProduct m x q / (1 - x * u) := by
    have h0 : b 0 = GProduct m x q / (1 - x * u) := by simp [hb, gTail]
    rw [seed, ← mul_assoc, mul_inv_cancel₀ hx2, one_mul,
      (summable_norm_seed_term hm x hq0 hq1 u).of_norm.tsum_eq_zero_add]
    simp only [hb] at h0 ⊢
    rw [h0]
    ring
  have hDD : Summable (fun k => ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
      x ^ i * u ^ ((i : ℤ) + 2 - r) * T i (k + 1)) :=
    summable_sum fun r _ => summable_sum fun (i : ℕ) _ => (hTsum (i : ℤ)).mul_left _
  have hDsum : Summable (fun k => D (k + 1)) :=
    (((hTsum (-2)).mul_left _).add ((hTsum (-1)).mul_left _)).sub hDD
  have hDshift : ∑' k, D (k + 1) = rawDefect m x u q := by
    simp only [hD]
    rw [(((hTsum (-2)).mul_left _).add ((hTsum (-1)).mul_left _)).tsum_sub hDD,
      ((hTsum (-2)).mul_left _).tsum_add ((hTsum (-1)).mul_left _),
      tsum_mul_left, tsum_mul_left,
      Summable.tsum_finsetSum fun r _ => summable_sum fun (i : ℕ) _ =>
        (hTsum (i : ℤ)).mul_left _]
    have hin : ∀ r : ℕ, ∑' k, ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * T i (k + 1) =
        ∑ i ∈ range (r - 2), x ^ i * u ^ ((i : ℤ) + 2 - r) * (XSeries m x i q - GProduct m x q) :=
      fun r => by
        rw [Summable.tsum_finsetSum fun (i : ℕ) _ => (hTsum (i : ℤ)).mul_left _]
        simp_rw [tsum_mul_left, hTshift]
    simp_rw [hin]
    simp only [hTshift, rawDefect]
  have hterm : ∀ k : ℕ, q ^ (k ^ 2) * gTail m x k q / (1 - x * (q * u) * q ^ k) =
      q * x ^ 2 * S * b (k + 1) + q * x ^ 2 * D (k + 1) := fun k => by
    simpa [hb, hD, hT, hS] using
      seedShiftRaw_term hm hx hq0 hq1 hu k (hxu (k + 1))
  rw [seed, tsum_congr hterm, ((hbsum.mul_left _).tsum_add (hDsum.mul_left _)),
    tsum_mul_left, tsum_mul_left, hbshift, hDshift]
  field_simp
  ring

end HigherDyson3
