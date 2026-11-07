/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Divisor.DivisorChar
public import HigherDyson3.Kernel.KernelNormal
public import HigherDyson3.Theta.TwistedThetaNormal

/-!
# The layer identity

Let `m ≥ 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x` and
`k ∈ ℕ`, with `q = e(τ)` and `u = e(w)`, the shifted kernel series
`∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u q^{n+k})` converges absolutely and equals
`x^{2(m+1)k} q^{mk²} 𝒦_{m,x}(τ,w) + ∑_{ℓ=0}^{2m-1} (∑_{s=1}^{k} x^{2(m+1)(k-s)+ℓ}
q^{mk²-ms²+ℓs}) T^{[x]}_{m,ℓ}(τ,w)`.

Put `v_r = x q^r u`, which is neither `0` nor `1` off the divisor
(`HigherDyson3.divisor_char`). After the substitution `n = r - k`, the `r`-th summand is
`x^{2(m+1)k} q^{mk²} x^{-2r} q^{mr²} u^{2mr} v_r^{-2mk} / (1 - v_r)`. The finite geometric
identity `v^{-L} / (1 - v) = 1 / (1 - v) + ∑_{j=1}^{L} v^{-j}` with `L = 2mk` splits it into
the `r`-th summand of the kernel and `2mk` monomials; writing `j = 2ms - ℓ` with
`1 ≤ s ≤ k`, `0 ≤ ℓ < 2m`, the monomial indexed by `j` is a multiple of the `(r - s)`-th
summand of the twisted theta series `T^{[x]}_{m,ℓ}`. All the series involved converge
absolutely (`HigherDyson3.kernelNormal_exists`, `HigherDyson3.twistedThetaNormal_exists`
on a singleton), so the identity may be summed over `r`.

## Main results

* `HigherDyson3.layer_identity`: absolute convergence of the shifted kernel series and its
  decomposition into the kernel and the twisted theta series.

## Implementation notes

The source assumes `m ≥ 2`; the argument only uses `m ≥ 1`.
-/

public section

open Finset

namespace HigherDyson3

/-- `e(z)^n = e(nz)`. -/
private lemma layerIdentity_e_zpow (z : ℂ) (n : ℤ) : e z ^ n = e (n * z) := by
  simp only [e]
  rw [← Complex.exp_int_mul]
  ring_nf

/-- `e(a) e(b) = e(a + b)`. -/
private lemma layerIdentity_e_mul (a b : ℂ) : e a * e b = e (a + b) := by
  simp only [e]
  rw [← Complex.exp_add]
  ring_nf

private lemma layerIdentity_e_ne_zero (z : ℂ) : e z ≠ 0 := Complex.exp_ne_zero _

/-- The finite geometric identity `v^{-L} / (1 - v) = 1 / (1 - v) + ∑_{j=1}^{L} v^{-j}`. -/
private lemma layerIdentity_geom {v : ℂ} (hv : v ≠ 0) (hv1 : 1 - v ≠ 0) (L : ℕ) :
    v ^ (-(L : ℤ)) / (1 - v) = 1 / (1 - v) + ∑ j ∈ Icc 1 L, v ^ (-(j : ℤ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    have h : v ^ (-(L : ℤ)) = v ^ (-((L + 1 : ℕ) : ℤ)) * v := by
      rw [← zpow_add_one₀ hv]
      congr 1
      push_cast
      ring
    rw [h]
    field_simp
    ring

/-- Splitting `{1, …, a + b}` into `{1, …, a}` and a top block of length `b`, read downwards. -/
private lemma layerIdentity_sum_block (F : ℤ → ℂ) (a b : ℕ) :
    ∑ j ∈ Icc 1 (a + b), F j = ∑ j ∈ Icc 1 a, F j + ∑ ℓ ∈ range b, F ((a : ℤ) + b - ℓ) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ', add_assoc]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    congr 1
    push_cast
    ring

/-- Sorting `j ∈ {1, …, 2mk}` as `j = 2ms - ℓ` with `1 ≤ s ≤ k` and `0 ≤ ℓ < 2m`. -/
private lemma layerIdentity_sum_sort (F : ℤ → ℂ) (m k : ℕ) :
    ∑ j ∈ Icc 1 (2 * m * k), F j =
      ∑ ℓ ∈ range (2 * m), ∑ s ∈ Icc 1 k, F (2 * (m : ℤ) * s - ℓ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * m * (k + 1) = 2 * m * k + 2 * m by ring, layerIdentity_sum_block, ih,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_Icc_succ_top (by omega)]
    congr 2

/-- The termwise layer identity, for the summand of index `n = r - k`. -/
private lemma layerIdentity_term (m : ℕ) (α τ w : ℂ) (k : ℕ) (r : ℤ)
    (hr : 1 - e α * e w * e τ ^ r ≠ 0) :
    e α ^ (-2 * (r - k)) * e τ ^ ((m : ℤ) * (r - k) ^ 2) * e w ^ (2 * (m : ℤ) * (r - k)) /
        (1 - e α * e w * e τ ^ (r - k + k)) =
      e α ^ (2 * ((m : ℤ) + 1) * k) * e τ ^ ((m : ℤ) * k ^ 2) *
          (e α ^ (-2 * r) * e τ ^ ((m : ℤ) * r ^ 2) * e w ^ (2 * (m : ℤ) * r) /
            (1 - e α * e w * e τ ^ r)) +
        ∑ ℓ ∈ range (2 * m), ∑ s ∈ Icc 1 k,
          e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s) + ℓ) *
              e τ ^ ((m : ℤ) * k ^ 2 - m * s ^ 2 + ℓ * s) *
            (e α ^ (-2 * (r - s)) * e τ ^ ((m : ℤ) * (r - s) ^ 2 + ℓ * (r - s)) *
              e w ^ ((ℓ : ℤ) + 2 * m * (r - s))) := by
  have hv0 : e α * e w * e τ ^ r ≠ 0 := by
    simp [layerIdentity_e_ne_zero, zpow_ne_zero]
  have h1 : e α ^ (-2 * (r - k)) * e τ ^ ((m : ℤ) * (r - k) ^ 2) *
      e w ^ (2 * (m : ℤ) * (r - k)) =
      e α ^ (2 * ((m : ℤ) + 1) * k) * e τ ^ ((m : ℤ) * k ^ 2) *
        (e α ^ (-2 * r) * e τ ^ ((m : ℤ) * r ^ 2) * e w ^ (2 * (m : ℤ) * r)) *
        (e α * e w * e τ ^ r) ^ (-((2 * m * k : ℕ) : ℤ)) := by
    simp only [layerIdentity_e_zpow, layerIdentity_e_mul]
    congr 1
    push_cast
    ring
  rw [sub_add_cancel, h1, mul_div_assoc, layerIdentity_geom hv0 hr, mul_add, Finset.mul_sum]
  have hs := layerIdentity_sum_sort (fun j : ℤ =>
    e α ^ (2 * ((m : ℤ) + 1) * k) * e τ ^ ((m : ℤ) * k ^ 2) *
      (e α ^ (-2 * r) * e τ ^ ((m : ℤ) * r ^ 2) * e w ^ (2 * (m : ℤ) * r)) *
      (e α * e w * e τ ^ r) ^ (-j)) m k
  rw [hs]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [layerIdentity_e_zpow, layerIdentity_e_mul]
    congr 1
    push_cast
    ring

/-- **The layer identity.** For an integer `m ≥ 1`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`,
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, `q = e(τ)`, `u = e(w)` and `k ∈ ℕ`, the series
`∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u q^{n+k})` converges absolutely, and its sum is
`x^{2(m+1)k} q^{mk²} 𝒦_{m,x}(τ,w) + ∑_{ℓ=0}^{2m-1} (∑_{s=1}^{k} x^{2(m+1)(k-s)+ℓ}
q^{mk²-ms²+ℓs}) T^{[x]}_{m,ℓ}(τ,w)`. -/
theorem layer_identity {m : ℕ} (hm : 1 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ w : ℂ}
    (hp : (τ, w) ∈ halfPlaneProd \ divisor α) (k : ℕ) :
    Summable (fun n : ℤ => ‖e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
      e w ^ (2 * (m : ℤ) * n) / (1 - e α * e w * e τ ^ (n + k))‖) ∧
    ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) /
        (1 - e α * e w * e τ ^ (n + k)) =
      e α ^ (2 * ((m : ℤ) + 1) * k) * e τ ^ ((m : ℤ) * k ^ 2) * kernel m α τ w +
        ∑ ℓ ∈ range (2 * m), (∑ s ∈ Icc 1 k,
          e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s) + ℓ) *
            e τ ^ ((m : ℤ) * k ^ 2 - m * s ^ 2 + ℓ * s)) * twistedTheta m ℓ α τ w := by
  obtain ⟨f, hf⟩ : ∃ f : ℤ → ℂ, f = fun n => e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
      e w ^ (2 * (m : ℤ) * n) / (1 - e α * e w * e τ ^ (n + k)) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℤ → ℂ, K = fun r => e α ^ (-2 * r) * e τ ^ ((m : ℤ) * r ^ 2) *
      e w ^ (2 * (m : ℤ) * r) / (1 - e α * e w * e τ ^ r) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℤ → ℂ, T = fun (ℓ : ℕ) (j : ℤ) => e α ^ (-2 * j) *
      e τ ^ ((m : ℤ) * j ^ 2 + ℓ * j) * e w ^ ((ℓ : ℤ) + 2 * m * j) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℕ → ℂ, c = fun (ℓ s : ℕ) =>
      e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s) + ℓ) *
        e τ ^ ((m : ℤ) * k ^ 2 - m * s ^ 2 + ℓ * s) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = e α ^ (2 * ((m : ℤ) + 1) * k) * e τ ^ ((m : ℤ) * k ^ 2) :=
    ⟨_, rfl⟩
  suffices key : Summable (fun n => ‖f n‖) ∧ ∑' n, f n =
      C * ∑' r, K r + ∑ ℓ ∈ range (2 * m), (∑ s ∈ Icc 1 k, c ℓ s) * ∑' j, T ℓ j by
    subst hf hKdef hTdef hcdef hC
    exact key
  have hden : ∀ r : ℤ, 1 - e α * e w * e τ ^ r ≠ 0 := by
    intro r h
    obtain ⟨b, hb⟩ := (divisor_char α hα0 hα1 hp.1 r).1 h
    exact hp.2 (Set.mem_iUnion₂.2 ⟨-r, b, hb⟩)
  have hsing : ({(τ, w)} : Set (ℂ × ℂ)) ⊆ halfPlaneProd \ divisor α :=
    Set.singleton_subset_iff.2 hp
  have hK : Summable K := by
    obtain ⟨M, hM, -, hle⟩ :=
      kernelNormal_exists hm α hα0 hα1 {(τ, w)} isCompact_singleton hsing
    subst hKdef
    exact Summable.of_norm_bounded hM fun r => hle r _ rfl
  have hT : ∀ ℓ : ℕ, Summable (T ℓ) := by
    intro ℓ
    obtain ⟨M, hM, -, hle⟩ := twistedThetaNormal_exists hm ℓ α {(τ, w)} isCompact_singleton
      (hsing.trans Set.sdiff_subset)
    subst hTdef
    exact Summable.of_norm_bounded hM fun j => hle j _ rfl
  have hTs : ∀ (ℓ s : ℕ), Summable (fun r : ℤ => T ℓ (r - s)) := fun ℓ s =>
    (Equiv.subRight (s : ℤ)).summable_iff.2 (hT ℓ)
  have hg : ∀ r : ℤ, f (r - k) = C * K r + ∑ ℓ ∈ range (2 * m), ∑ s ∈ Icc 1 k,
      c ℓ s * T ℓ (r - s) := by
    intro r
    subst hf hKdef hTdef hcdef hC
    exact layerIdentity_term m α τ w k r (hden r)
  have hsum : Summable (fun r : ℤ => ∑ ℓ ∈ range (2 * m), ∑ s ∈ Icc 1 k,
      c ℓ s * T ℓ (r - s)) :=
    summable_sum fun ℓ _ => summable_sum fun s _ => (hTs ℓ s).mul_left _
  have hgs : Summable (fun r : ℤ => f (r - k)) := by
    simp_rw [hg]
    exact (hK.mul_left C).add hsum
  have hfs : Summable f := (Equiv.subRight (k : ℤ)).summable_iff.1 hgs
  refine ⟨summable_norm_iff.2 hfs, ?_⟩
  rw [← (Equiv.subRight (k : ℤ)).tsum_eq f]
  simp only [Equiv.subRight_apply]
  rw [tsum_congr hg, (hK.mul_left C).tsum_add hsum, tsum_mul_left]
  rw [Summable.tsum_finsetSum fun ℓ _ => summable_sum fun s _ => (hTs ℓ s).mul_left _]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Summable.tsum_finsetSum fun s _ => (hTs ℓ s).mul_left _, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight (s : ℤ)).tsum_eq (T ℓ)

end HigherDyson3
