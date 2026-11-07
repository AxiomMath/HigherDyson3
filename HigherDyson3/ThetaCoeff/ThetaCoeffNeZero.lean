/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.ThetaCoeff.ThetaLeading

/-!
# No theta coefficient vanishes identically

Let `m ≥ 2`, `α ∈ ℚ ∩ [0, 1)` and `0 ≤ ℓ < 2m`. Then `h_{m,ℓ,x}(τ) ≠ 0` for some `τ ∈ ℍ`.

With `c_ℓ = 1 + ℓ - ℓ²/(4m)`, the leading-term estimate
`|h_{m,ℓ,x}(τ) - e(ℓα/m) x^{ℓ-2} e(c_ℓ τ)| ≤ C |e((c_ℓ+2)τ)|` holds for `Im τ ≥ T`. At
`τ = it` the leading term has modulus `|e(c_ℓ τ)|` and the error is at most
`C e^{-4πt} |e(c_ℓ τ)|`, so `h_{m,ℓ,x}(it) ≠ 0` once `C e^{-4πt} < 1`.

## Main results

* `HigherDyson3.exists_thetaCoeffH_ne_zero`: some value of `h_{m,ℓ,x}` on `ℍ` is nonzero.
-/

public section

namespace HigherDyson3

/-- **No theta coefficient vanishes identically.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`0 ≤ ℓ < 2m` there is `τ ∈ ℍ` with `h_{m,ℓ,x}(τ) ≠ 0`, where `x = e(α)`. -/
theorem exists_thetaCoeffH_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ τ ∈ upperHalfPlaneSet, thetaCoeffH m ℓ α τ ≠ 0 := by
  obtain ⟨C, T, hC, hT, hbound⟩ := exists_norm_thetaCoeffH_sub_le hm hα0 hα1 hℓ
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (-(4 * Real.pi) * t)) Filter.atTop
      (nhds 0) := by
    have : Filter.Tendsto (fun t : ℝ => (4 * Real.pi) * t) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (by positivity)
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).congr fun t => ?_
    simp [neg_mul]
  obtain ⟨t, htT, htC⟩ := ((Filter.eventually_ge_atTop T).and
    (hlim.eventually (gt_mem_nhds (inv_pos.mpr hC)))).exists
  have ht : 0 < t := hT.trans_le htT
  set τ : ℂ := t * Complex.I with hτdef
  have hτim : τ.im = t := by simp [hτdef]
  have hτ : τ ∈ upperHalfPlaneSet := by change 0 < τ.im; rw [hτim]; exact ht
  refine ⟨τ, hτ, fun h0 => ?_⟩
  have hb := hbound τ hτ (by rw [hτim]; exact htT)
  set c : ℂ := 1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)
  have hsplit : e ((c + 2) * τ) = e (c * τ) * e (2 * τ) := by
    unfold e; rw [← Complex.exp_add]; ring_nf
  have he2 : ‖e (2 * τ)‖ = Real.exp (-(4 * Real.pi) * t) := by
    unfold e; rw [Complex.norm_exp]; congr 1; simp [hτdef]; ring
  have hu : ‖e (ℓ * α / m)‖ = 1 := by
    exact_mod_cast coeffCNormal_norm_e_ofReal ((ℓ : ℝ) * α / m)
  have hx : ‖e α‖ = 1 := by exact_mod_cast coeffCNormal_norm_e_ofReal (α : ℝ)
  have hpos : 0 < ‖e (c * τ)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  rw [h0, zero_sub, norm_neg, norm_mul, norm_mul, hu, norm_zpow, hx, one_zpow, one_mul,
    one_mul, hsplit, norm_mul, he2] at hb
  have : C * Real.exp (-(4 * Real.pi) * t) < 1 := by
    calc C * Real.exp (-(4 * Real.pi) * t) < C * C⁻¹ := mul_lt_mul_of_pos_left htC hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  nlinarith

end HigherDyson3
