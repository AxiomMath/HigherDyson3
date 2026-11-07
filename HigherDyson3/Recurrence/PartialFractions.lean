/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.FiniteDefectConstantTerm
public import HigherDyson3.Recurrence.FiniteDefectDegree
public import HigherDyson3.Recurrence.FiniteDefectQPole
public import HigherDyson3.Recurrence.FiniteCxVanishes
public import HigherDyson3.Characterization.Definitions

/-!
# The partial-fraction expansion of the rational defect

For `m ≥ 2`, `d = 2m + 1`, `x ∈ ℂ^×` and `0 < |q| < 1`, the normalized rational defect
`f_{d,x}(u;q) = (1-u)/(u(1-u^d)) (R_{d,x}(u;q) - C_x u^{d-1} G_d(x;q)/(1-xu))` equals
`Q_{d,x}(u;q) / (u (1 - u^d) (1 - xu)^{ε_x})`, and this proper rational function has the
partial-fraction expansion
`-X_0/u + ∑_{r<d} D_{r,x}/(1 - ω^r u) + ε_x E_x/(1 - xu)` with explicit, unique coefficients,
which are holomorphic in `0 < |q| < 1` with at most a simple pole at `q = 0`
[AOS, Proposition 3.2].

## Main results

* `HigherDyson3.normalizedDefect_eq`: `f_{d,x} = Q_{d,x}/(u(1-u^d)(1-xu)^{ε_x})`.
* `HigherDyson3.rationalDefect_div_eq`: the partial-fraction expansion.
* `HigherDyson3.partialFraction_unique`: uniqueness of the coefficients.
* `HigherDyson3.exists_differentiableOn_eq_mul_pfD`,
  `HigherDyson3.exists_differentiableOn_eq_mul_pfE`:
  the coefficients times `q` extend holomorphically to `|q| < 1`.

## Implementation notes

The proof clears denominators: the right-hand side times `u(1-u^d)(1-xu)^{ε_x}` is the
polynomial `pfPoly`, in which `(1-u^d)/(1-ω^r u)` is written as the geometric sum
`∑_{k<d} (ω^r u)^k`; two polynomials of degree at most `d + ε_x` agreeing at the `d + 1 + ε_x`
distinct poles `0`, `ω^{-r}`, `x^{-1}` are equal.
-/

public section

namespace HigherDyson3

open Polynomial Finset

/-- `ε_x = 1` if `x^d ≠ 1` and `0` if `x^d = 1`, `d = 2m + 1`. -/
noncomputable def defectEps (m : ℕ) (x : ℂ) : ℕ := if x ^ (2 * m + 1) = 1 then 0 else 1

/-- The polynomial `Q_{d,x}(u;q)` of [AOS, §3]: `(1-xu)(1-u)R - C_x u^{d-1}(1-u) g` if `x^d ≠ 1`,
`(1-u)R - d u^{d-1} g` if `x = 1`, and `(1-u)R` if `x^d = 1`, `x ≠ 1`, with
`R = R_{d,x}(u;q)` and `g = G_d(x;q)`. -/
noncomputable def rationalDefect (m : ℕ) (x q : ℂ) : ℂ[X] :=
  if x ^ (2 * m + 1) ≠ 1 then
    (1 - C x * X) * (1 - X) * defectPoly m x q - C (Cx m x * GProduct m x q) * X ^ (2 * m) * (1 - X)
  else if x = 1 then
    (1 - X) * defectPoly m x q - C ((2 * m + 1 : ℂ) * GProduct m x q) * X ^ (2 * m)
  else (1 - X) * defectPoly m x q

/-- The normalized rational defect
`f_{d,x}(u;q) = (1-u)/(u(1-u^d)) (R_{d,x}(u;q) - C_x u^{d-1} G_d(x;q)/(1-xu))` [AOS, §3]. -/
noncomputable def normalizedDefect (m : ℕ) (x q u : ℂ) : ℂ :=
  (1 - u) / (u * (1 - u ^ (2 * m + 1))) *
    ((defectPoly m x q).eval u - Cx m x * u ^ (2 * m) / (1 - x * u) * GProduct m x q)

/-- The denominator `u (1 - u^d) (1 - xu)^{ε_x}`. -/
noncomputable def defectDenom (m : ℕ) (x u : ℂ) : ℂ :=
  u * (1 - u ^ (2 * m + 1)) * (1 - x * u) ^ defectEps m x

/-- The coefficient `D_{r,x}(q) = ω^r Q_{d,x}(ω^{-r};q) / (d (1 - x ω^{-r})^{ε_x})`. -/
noncomputable def pfD (m : ℕ) (x q : ℂ) (r : ℕ) : ℂ :=
  omega m ^ r * (rationalDefect m x q).eval (omega m ^ r)⁻¹ /
    ((2 * m + 1 : ℂ) * (1 - x * (omega m ^ r)⁻¹) ^ defectEps m x)

/-- The coefficient `E_x(q) = x Q_{d,x}(x^{-1};q) / (1 - x^{-d})` if `x^d ≠ 1`, and `0`
otherwise. -/
noncomputable def pfE (m : ℕ) (x q : ℂ) : ℂ :=
  if x ^ (2 * m + 1) = 1 then 0 else x * (rationalDefect m x q).eval x⁻¹ / (1 - x⁻¹ ^ (2 * m + 1))

/-- The cleared-denominator form of the right-hand side
`A/u + ∑_{r<d} D_r/(1-ω^r u) + ε_x E/(1-xu)`. -/
noncomputable def pfPoly (m : ℕ) (x A : ℂ) (D : ℕ → ℂ) (E : ℂ) : ℂ[X] :=
  C A * (1 - X ^ (2 * m + 1)) * (1 - C x * X) ^ defectEps m x +
    ∑ r ∈ range (2 * m + 1), C (D r) * X * (∑ k ∈ range (2 * m + 1), (C (omega m ^ r) * X) ^ k) *
      (1 - C x * X) ^ defectEps m x +
    C ((defectEps m x : ℂ) * E) * X * (1 - X ^ (2 * m + 1))

theorem defectEps_def (m : ℕ) (x : ℂ) :
    defectEps m x = if x ^ (2 * m + 1) = 1 then 0 else 1 := (rfl)

theorem defectEps_eq_zero_of_pow_eq_one {m : ℕ} {x : ℂ} (hd : x ^ (2 * m + 1) = 1) :
    defectEps m x = 0 := by simp [defectEps, hd]

theorem rationalDefect_of_pow_ne_one {m : ℕ} {x : ℂ} (hd : x ^ (2 * m + 1) ≠ 1) (q : ℂ) :
    rationalDefect m x q = (1 - C x * X) * (1 - X) * defectPoly m x q -
      C (Cx m x * GProduct m x q) * X ^ (2 * m) * (1 - X) := by
  simp [rationalDefect, hd]

theorem rationalDefect_one (m : ℕ) (q : ℂ) :
    rationalDefect m 1 q = (1 - X) * defectPoly m 1 q -
      C ((2 * m + 1 : ℂ) * GProduct m 1 q) * X ^ (2 * m) := by
  simp [rationalDefect]

theorem rationalDefect_of_pow_eq_one {m : ℕ} {x : ℂ} (hd : x ^ (2 * m + 1) = 1) (hx : x ≠ 1)
    (q : ℂ) : rationalDefect m x q = (1 - X) * defectPoly m x q := by
  simp [rationalDefect, hd, hx]

theorem pfD_def (m : ℕ) (x q : ℂ) (r : ℕ) :
    pfD m x q r = omega m ^ r * (rationalDefect m x q).eval (omega m ^ r)⁻¹ /
      ((2 * m + 1 : ℂ) * (1 - x * (omega m ^ r)⁻¹) ^ defectEps m x) := (rfl)

theorem pfE_def (m : ℕ) (x q : ℂ) : pfE m x q =
    if x ^ (2 * m + 1) = 1 then 0
    else x * (rationalDefect m x q).eval x⁻¹ / (1 - x⁻¹ ^ (2 * m + 1)) :=
  (rfl)

theorem defectDenom_def (m : ℕ) (x u : ℂ) :
    defectDenom m x u = u * (1 - u ^ (2 * m + 1)) * (1 - x * u) ^ defectEps m x := (rfl)

theorem normalizedDefect_def (m : ℕ) (x q u : ℂ) : normalizedDefect m x q u =
    (1 - u) / (u * (1 - u ^ (2 * m + 1))) *
      ((defectPoly m x q).eval u - Cx m x * u ^ (2 * m) / (1 - x * u) * GProduct m x q) := (rfl)

theorem omega_isPrimitiveRoot (m : ℕ) : IsPrimitiveRoot (omega m) (2 * m + 1) := by
  have h := Complex.isPrimitiveRoot_exp (2 * m + 1) (by omega)
  convert h using 1
  rw [omega, e]
  congr 1
  push_cast
  field_simp

theorem omega_ne_zero (m : ℕ) : omega m ≠ 0 := by
  rw [omega, e]; exact Complex.exp_ne_zero _

theorem omega_pow_inv_pow_d (m r : ℕ) : ((omega m ^ r)⁻¹) ^ (2 * m + 1) = 1 := by
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, (omega_isPrimitiveRoot m).pow_eq_one, one_pow, inv_one]

theorem omega_pow_mul_pow_d (m r : ℕ) (u : ℂ) :
    (omega m ^ r * u) ^ (2 * m + 1) = u ^ (2 * m + 1) := by
  rw [mul_pow, ← pow_mul, mul_comm r, pow_mul, (omega_isPrimitiveRoot m).pow_eq_one, one_pow,
    one_mul]

/-- Orthogonality: `∑_{k<d} (ω^r ω^{-r'})^k = d` if `r = r'` and `0` otherwise, for `r, r' < d`. -/
theorem geom_sum_omega {m r r' : ℕ} (hr : r < 2 * m + 1) (hr' : r' < 2 * m + 1) :
    ∑ k ∈ range (2 * m + 1), (omega m ^ r * (omega m ^ r')⁻¹) ^ k =
      if r = r' then (2 * m + 1 : ℂ) else 0 := by
  have hω := omega_isPrimitiveRoot m
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero _ (omega_ne_zero m))]
  · set y := omega m ^ r * (omega m ^ r')⁻¹ with hy
    have hyd : y ^ (2 * m + 1) = 1 := by
      rw [hy, omega_pow_mul_pow_d, omega_pow_inv_pow_d]
    have hy1 : y ≠ 1 := by
      intro h1
      rw [hy, mul_inv_eq_one₀ (pow_ne_zero _ (omega_ne_zero m))] at h1
      exact h (hω.pow_inj hr hr' h1)
    have := geom_sum_mul y (2 * m + 1)
    rw [hyd, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hy1)

theorem defectEps_le_one (m : ℕ) (x : ℂ) : defectEps m x ≤ 1 := by
  unfold defectEps; split_ifs <;> simp

theorem defectEps_eq_one_iff {m : ℕ} {x : ℂ} : defectEps m x = 1 ↔ x ^ (2 * m + 1) ≠ 1 := by
  unfold defectEps; split_ifs with h <;> simp [h]

/-- The cleared-denominator polynomial evaluates to the denominator times the partial-fraction
sum at every `u` off the poles. -/
theorem eval_pfPoly {m : ℕ} {x u : ℂ} (A : ℂ) (D : ℕ → ℂ) (E : ℂ) (hu0 : u ≠ 0)
    (hud : u ^ (2 * m + 1) ≠ 1) (hxu : defectEps m x = 1 → 1 - x * u ≠ 0) :
    (pfPoly m x A D E).eval u = defectDenom m x u *
      (A / u + ∑ r ∈ range (2 * m + 1), D r / (1 - omega m ^ r * u) +
        (defectEps m x : ℂ) * E / (1 - x * u)) := by
  have hud' : 1 - u ^ (2 * m + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hud)
  have hden : ∀ r, 1 - omega m ^ r * u ≠ 0 := by
    intro r h
    apply hud
    rw [← omega_pow_mul_pow_d m r u, ← (sub_eq_zero.mp h), one_pow]
  have hgeom : ∀ r, ∑ k ∈ range (2 * m + 1), (omega m ^ r * u) ^ k =
      (1 - u ^ (2 * m + 1)) / (1 - omega m ^ r * u) := by
    intro r
    have hy1 : omega m ^ r * u ≠ 1 := fun h1 => hden r (by rw [h1, sub_self])
    rw [geom_sum_eq hy1, omega_pow_mul_pow_d, div_eq_div_iff (sub_ne_zero.mpr hy1) (hden r)]
    ring
  simp only [pfPoly, defectDenom, eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_pow,
    eval_X, eval_finsetSum]
  simp_rw [hgeom]
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  · congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun r _ => ?_
      field_simp [hden r]
  · rcases Nat.eq_zero_or_pos (defectEps m x) with h | h
    · rw [h]; simp
    · have h1 : defectEps m x = 1 := le_antisymm (defectEps_le_one m x) h
      have h2 : 1 - u * x ≠ 0 := by rw [mul_comm]; exact hxu h1
      rw [h1]
      field_simp [hxu h1, h2]

theorem eval_pfPoly_zero (m : ℕ) (x A : ℂ) (D : ℕ → ℂ) (E : ℂ) :
    (pfPoly m x A D E).eval 0 = A := by
  simp [pfPoly, zero_pow (show 2 * m + 1 ≠ 0 by omega), eval_finsetSum]

theorem eval_pfPoly_omega {m r' : ℕ} (hr' : r' < 2 * m + 1) (x A : ℂ) (D : ℕ → ℂ) (E : ℂ) :
    (pfPoly m x A D E).eval (omega m ^ r')⁻¹ =
      D r' * (omega m ^ r')⁻¹ * (2 * m + 1 : ℂ) * (1 - x * (omega m ^ r')⁻¹) ^ defectEps m x := by
  simp only [pfPoly, eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X,
    eval_finsetSum, omega_pow_inv_pow_d, sub_self, mul_zero, zero_mul, zero_add, add_zero]
  have : ∀ r ∈ range (2 * m + 1), D r * (omega m ^ r')⁻¹ *
      (∑ k ∈ range (2 * m + 1), (omega m ^ r * (omega m ^ r')⁻¹) ^ k) *
        (1 - x * (omega m ^ r')⁻¹) ^ defectEps m x =
      if r = r' then D r' * (omega m ^ r')⁻¹ * (2 * m + 1 : ℂ) *
        (1 - x * (omega m ^ r')⁻¹) ^ defectEps m x else 0 := by
    intro r hr
    rw [geom_sum_omega (Finset.mem_range.mp hr) hr']
    split_ifs with h
    · subst h; rfl
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (range (2 * m + 1)) r',
    ite_eq_left (Finset.mem_range.mpr hr')]

theorem eval_pfPoly_inv {m : ℕ} {x : ℂ} (hx : x ≠ 0) (hε : defectEps m x = 1) (A : ℂ)
    (D : ℕ → ℂ) (E : ℂ) :
    (pfPoly m x A D E).eval x⁻¹ = E * x⁻¹ * (1 - x⁻¹ ^ (2 * m + 1)) := by
  simp only [pfPoly, eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X,
    eval_finsetSum, hε, mul_inv_cancel₀ hx, sub_self, pow_one, mul_zero, zero_add,
    Finset.sum_const_zero, Nat.cast_one, one_mul]

theorem natDegree_C_mul_X_le' (a : ℂ) : (C a * X : ℂ[X]).natDegree ≤ 1 :=
  (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem natDegree_one_sub_C_mul_X_pow_le (a : ℂ) (k : ℕ) :
    ((1 - C a * X) ^ k : ℂ[X]).natDegree ≤ k := by
  refine (natDegree_pow_le).trans ?_
  have : (1 - C a * X : ℂ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_X_le' a))
  nlinarith

theorem natDegree_one_sub_X_pow_le (n : ℕ) : ((1 : ℂ[X]) - X ^ n).natDegree ≤ n :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le n))

theorem natDegree_pfPoly_le (m : ℕ) (x A : ℂ) (D : ℕ → ℂ) (E : ℂ) :
    (pfPoly m x A D E).natDegree ≤ 2 * m + 1 + defectEps m x := by
  unfold pfPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine (natDegree_mul_le).trans ?_
    refine add_le_add ((natDegree_C_mul_le _ _).trans (natDegree_one_sub_X_pow_le _)) ?_
    exact natDegree_one_sub_C_mul_X_pow_le _ _
  · refine natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
    refine (natDegree_mul_le).trans ?_
    have hgeom : (∑ k ∈ range (2 * m + 1), (C (omega m ^ r) * X) ^ k : ℂ[X]).natDegree ≤ 2 * m := by
      refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      refine (natDegree_pow_le).trans ?_
      have := Finset.mem_range.mp hk
      have h1 : (C (omega m ^ r) * X : ℂ[X]).natDegree ≤ 1 := natDegree_C_mul_X_le' _
      nlinarith
    have h2 : (C (D r) * X * ∑ k ∈ range (2 * m + 1), (C (omega m ^ r) * X) ^ k : ℂ[X]).natDegree
        ≤ 2 * m + 1 := by
      refine (natDegree_mul_le).trans ?_
      have h3 : (C (D r) * X : ℂ[X]).natDegree ≤ 1 := natDegree_C_mul_X_le' _
      omega
    have h4 := natDegree_one_sub_C_mul_X_pow_le x (defectEps m x)
    omega
  · rcases Nat.eq_zero_or_pos (defectEps m x) with h | h
    · rw [h]; simp
    · refine (natDegree_mul_le).trans ?_
      have h1 : (C ((defectEps m x : ℂ) * E) * X : ℂ[X]).natDegree ≤ 1 := natDegree_C_mul_X_le' _
      have h2 := natDegree_one_sub_X_pow_le (2 * m + 1)
      omega

theorem natDegree_defectPoly_le {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) : (defectPoly m x q).natDegree ≤ 2 * m - 1 := by
  have h := defectPoly_degree_le hm hx hq0 hq1
  have h' : (defectPoly m x q).natDegree ≤ 2 * m + 1 - 2 := natDegree_le_of_degree_le h
  omega

theorem natDegree_rationalDefect_le {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) : (rationalDefect m x q).natDegree ≤ 2 * m + 1 + defectEps m x := by
  have hR := natDegree_defectPoly_le hm hx hq0 hq1
  have h1X : ((1 : ℂ[X]) - X).natDegree ≤ 1 := by simpa using natDegree_one_sub_X_pow_le 1
  have h1xX : ((1 : ℂ[X]) - C x * X).natDegree ≤ 1 := by
    simpa using natDegree_one_sub_C_mul_X_pow_le x 1
  have hCX : ∀ a : ℂ, (C a * X ^ (2 * m) : ℂ[X]).natDegree ≤ 2 * m :=
    fun a => (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  unfold rationalDefect
  split_ifs with hd h1
  · have hε : defectEps m x = 1 := defectEps_eq_one_iff.mpr hd
    rw [hε]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      have := (natDegree_mul_le (p := (1 - C x * X : ℂ[X])) (q := 1 - X))
      omega
    · refine (natDegree_mul_le).trans ?_
      have := hCX (Cx m x * GProduct m x q)
      omega
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      omega
    · have := hCX ((2 * m + 1 : ℂ) * GProduct m x q)
      omega
  · refine (natDegree_mul_le).trans ?_
    omega

theorem eval_rationalDefect_zero {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) : (rationalDefect m x q).eval 0 = -XSeries m x 0 q := by
  have h0 : (defectPoly m x q).eval 0 = -XSeries m x 0 q := by
    rw [← coeff_zero_eq_eval_zero, defectPoly_coeff_zero hm hx hq0 hq1]
  have hz : (0 : ℂ) ^ (2 * m) = 0 := zero_pow (by omega)
  unfold rationalDefect
  split_ifs <;> simp [h0, hz]

theorem one_sub_mul_ne_zero_of_eps {m : ℕ} {x v : ℂ} (hε : defectEps m x = 1)
    (hv : v ^ (2 * m + 1) = 1) : 1 - x * v ≠ 0 := by
  intro h
  have hxv : x * v = 1 := (sub_eq_zero.mp h).symm
  have hd := defectEps_eq_one_iff.mp hε
  apply hd
  have := congrArg (· ^ (2 * m + 1)) hxv
  simpa [mul_pow, hv] using this

/-- **The partial-fraction identity, cleared form**: `Q_{d,x} = pfPoly(-X_0, D, E)`. -/
theorem rationalDefect_eq_pfPoly {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    rationalDefect m x q = pfPoly m x (-XSeries m x 0 q) (pfD m x q) (pfE m x q) := by
  have hω := omega_isPrimitiveRoot m
  have hd0 : (2 * m + 1 : ℂ) ≠ 0 := by exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
  let f : Option (Fin (2 * m + 1)) ⊕ Fin (defectEps m x) → ℂ := fun i =>
    match i with
    | .inl none => 0
    | .inl (some r) => (omega m ^ (r : ℕ))⁻¹
    | .inr _ => x⁻¹
  have hωne : ∀ r : ℕ, (omega m ^ r)⁻¹ ≠ 0 := fun r => inv_ne_zero (pow_ne_zero _ (omega_ne_zero m))
  have hxω : defectEps m x = 1 → ∀ r : ℕ, x⁻¹ ≠ (omega m ^ r)⁻¹ := by
    intro hε r h
    have h' : x = omega m ^ r := inv_injective h
    apply defectEps_eq_one_iff.mp hε
    rw [h', ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hεi : ∀ i : Fin (defectEps m x), defectEps m x = 1 := fun i =>
    le_antisymm (defectEps_le_one m x) (Fin.pos_iff_nonempty.mpr ⟨i⟩)
  have hinj : Function.Injective f := by
    intro a b h
    rcases a with (_ | r) | i
    · rcases b with (_ | r') | j
      · rfl
      · exact absurd h.symm (hωne r')
      · exact absurd h.symm (inv_ne_zero hx)
    · rcases b with (_ | r') | j
      · exact absurd h (hωne r)
      · have := hω.pow_inj r.2 r'.2 (inv_injective h)
        simp [Fin.ext this]
      · exact absurd h.symm (hxω (hεi j) r)
    · rcases b with (_ | r') | j
      · exact absurd h (inv_ne_zero hx)
      · exact absurd h (hxω (hεi i) r')
      · have hε := hεi i
        have : i = j := by
          have hi := i.2; have hj := j.2; exact Fin.ext (by omega)
        rw [this]
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ hinj ?_ ?_
  · intro i
    rcases i with (_ | r) | i
    · simp only [f]
      rw [eval_rationalDefect_zero hm hx hq0 hq1, eval_pfPoly_zero]
    · simp only [f]
      rw [eval_pfPoly_omega r.2, pfD]
      have hne : (1 - x * (omega m ^ (r : ℕ))⁻¹) ^ defectEps m x ≠ 0 := by
        rcases Nat.eq_zero_or_pos (defectEps m x) with h | h
        · rw [h, pow_zero]; exact one_ne_zero
        · have hε : defectEps m x = 1 := le_antisymm (defectEps_le_one m x) h
          rw [hε, pow_one]
          exact one_sub_mul_ne_zero_of_eps hε (omega_pow_inv_pow_d m r)
      have hω0 : omega m ^ (r : ℕ) ≠ 0 := pow_ne_zero _ (omega_ne_zero m)
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
        eq_div_iff (mul_ne_zero hd0 hne)]
      have : omega m ^ (r : ℕ) * (omega m ^ (r : ℕ))⁻¹ = 1 := mul_inv_cancel₀ hω0
      linear_combination (-(eval (omega m ^ (r : ℕ))⁻¹ (rationalDefect m x q)) * (2 * (m : ℂ) + 1) *
        (1 - x * (omega m ^ (r : ℕ))⁻¹) ^ defectEps m x) * this
    · have hε : defectEps m x = 1 :=
        le_antisymm (defectEps_le_one m x) (Fin.pos_iff_nonempty.mpr ⟨i⟩)
      simp only [f]
      rw [eval_pfPoly_inv hx hε, pfE, ite_eq_right (defectEps_eq_one_iff.mp hε)]
      have hxd : 1 - x⁻¹ ^ (2 * m + 1) ≠ 0 := by
        intro h
        apply defectEps_eq_one_iff.mp hε
        have : x⁻¹ ^ (2 * m + 1) = 1 := (sub_eq_zero.mp h).symm
        rw [inv_pow] at this
        exact inv_eq_one.mp this
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hxd]
      have : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
      linear_combination (-(eval x⁻¹ (rationalDefect m x q)) * (1 - x⁻¹ ^ (2 * m + 1))) * this
  · simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
    have h1 := natDegree_rationalDefect_le hm hx hq0 hq1
    have h2 := natDegree_pfPoly_le m x (-XSeries m x 0 q) (pfD m x q) (pfE m x q)
    omega

theorem defectDenom_ne_zero {m : ℕ} {x u : ℂ} (hu0 : u ≠ 0) (hud : u ^ (2 * m + 1) ≠ 1)
    (hxu : defectEps m x = 1 → 1 - x * u ≠ 0) : defectDenom m x u ≠ 0 := by
  unfold defectDenom
  refine mul_ne_zero (mul_ne_zero hu0 (sub_ne_zero.mpr (Ne.symm hud))) ?_
  rcases Nat.eq_zero_or_pos (defectEps m x) with h | h
  · rw [h, pow_zero]; exact one_ne_zero
  · have hε : defectEps m x = 1 := le_antisymm (defectEps_le_one m x) h
    rw [hε, pow_one]; exact hxu hε

/-- **The partial-fraction expansion of the rational defect** [AOS, Proposition 3.2]. For
`m ≥ 2`, `x ≠ 0`, `0 < |q| < 1` and `u ∉ {0} ∪ {ω^{-r}} ∪ {x^{-1}}`,
`Q_{d,x}(u;q) / (u(1-u^d)(1-xu)^{ε_x}) = -X_0/u + ∑_{r<d} D_{r,x}/(1 - ω^r u) + ε_x E_x/(1 - xu)`,
with `D_{r,x} = ω^r Q_{d,x}(ω^{-r})/(d (1 - x ω^{-r})^{ε_x})` and
`E_x = x Q_{d,x}(x^{-1})/(1 - x^{-d})` (`E_x = 0` if `x^d = 1`). -/
theorem rationalDefect_div_eq {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) (hu0 : u ≠ 0) (hud : u ^ (2 * m + 1) ≠ 1) (hxu : x * u ≠ 1) :
    (rationalDefect m x q).eval u / defectDenom m x u =
      -XSeries m x 0 q / u + ∑ r ∈ range (2 * m + 1), pfD m x q r / (1 - omega m ^ r * u) +
        (defectEps m x : ℂ) * pfE m x q / (1 - x * u) := by
  have hxu' : defectEps m x = 1 → 1 - x * u ≠ 0 := fun _ => sub_ne_zero.mpr (Ne.symm hxu)
  rw [rationalDefect_eq_pfPoly hm hx hq0 hq1, eval_pfPoly _ _ _ hu0 hud hxu',
    mul_div_cancel_left₀ _ (defectDenom_ne_zero hu0 hud hxu')]

/-- **The rational defect** [AOS, §3]: `f_{d,x}(u;q) = Q_{d,x}(u;q)/(u(1-u^d)(1-xu)^{ε_x})` for
`u ≠ 0`, `u^d ≠ 1`, `xu ≠ 1`. -/
theorem normalizedDefect_eq {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hu0 : u ≠ 0)
    (hud : u ^ (2 * m + 1) ≠ 1) (hxu : x * u ≠ 1) :
    normalizedDefect m x q u = (rationalDefect m x q).eval u / defectDenom m x u := by
  have h1 : 1 - u ^ (2 * m + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hud)
  have h2 : 1 - x * u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxu)
  unfold normalizedDefect defectDenom
  by_cases hd : x ^ (2 * m + 1) = 1
  · have hε : defectEps m x = 0 := by simp [defectEps, hd]
    rw [hε, pow_zero, mul_one]
    by_cases h1x : x = 1
    · subst h1x
      have hC : Cx m 1 = 2 * m + 1 := by simp [Cx, cyclotomicSum]
      have hQ : rationalDefect m 1 q = (1 - X) * defectPoly m 1 q -
          C ((2 * m + 1 : ℂ) * GProduct m 1 q) * X ^ (2 * m) := by
        simp [rationalDefect]
      rw [hC, hQ]
      have h3 : 1 - u ≠ 0 := by simpa using h2
      simp only [eval_sub, eval_mul, eval_one, eval_X, eval_C, eval_pow, one_mul] at *
      field_simp
    · have hC : Cx m x = 0 := Cx_eq_zero_of_pow_eq_one hm h1x hd
      have hQ : rationalDefect m x q = (1 - X) * defectPoly m x q := by
        simp [rationalDefect, hd, h1x]
      rw [hC, hQ]
      simp only [zero_mul, zero_div, sub_zero, eval_mul, eval_sub, eval_one, eval_X]
      field_simp
  · have hε : defectEps m x = 1 := by simp [defectEps, hd]
    have hQ : rationalDefect m x q = (1 - C x * X) * (1 - X) * defectPoly m x q -
        C (Cx m x * GProduct m x q) * X ^ (2 * m) * (1 - X) := by
      simp [rationalDefect, hd]
    rw [hε, pow_one, hQ]
    have h2' : 1 - u * x ≠ 0 := by rw [mul_comm]; exact h2
    simp only [eval_sub, eval_mul, eval_one, eval_X, eval_C, eval_pow]
    field_simp

/-- **Uniqueness of the partial-fraction coefficients** [AOS, Proposition 3.2]: any coefficients
`D'_r`, `E'` for which the expansion holds at every admissible `u` are `D_{r,x}` and (when
`x^d ≠ 1`) `E_x`. -/
theorem partialFraction_unique {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) (D' : ℕ → ℂ) (E' : ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → u ^ (2 * m + 1) ≠ 1 → x * u ≠ 1 →
      (rationalDefect m x q).eval u / defectDenom m x u =
        -XSeries m x 0 q / u + ∑ r ∈ range (2 * m + 1), D' r / (1 - omega m ^ r * u) +
          (defectEps m x : ℂ) * E' / (1 - x * u)) :
    (∀ r < 2 * m + 1, D' r = pfD m x q r) ∧ (x ^ (2 * m + 1) ≠ 1 → E' = pfE m x q) := by
  -- the two cleared-denominator polynomials agree on the infinite set of admissible `u`
  have hpoly : pfPoly m x (-XSeries m x 0 q) D' E' =
      pfPoly m x (-XSeries m x 0 q) (pfD m x q) (pfE m x q) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hfin : {u : ℂ | u = 0 ∨ u ^ (2 * m + 1) = 1 ∨ x * u = 1}.Finite := by
      have h1 : {u : ℂ | u ^ (2 * m + 1) = 1}.Finite := by
        refine (Polynomial.nthRoots (2 * m + 1) (1 : ℂ)).toFinset.finite_toSet.subset ?_
        intro u hu
        simp only [Set.mem_ofPred_eq] at hu
        simp [Polynomial.mem_nthRoots (show 0 < 2 * m + 1 by omega), hu]
      have h2 : {u : ℂ | x * u = 1} ⊆ {x⁻¹} := by
        intro u hu
        simp only [Set.mem_ofPred_eq] at hu
        simp [eq_inv_of_mul_eq_one_right hu]
      refine ((Set.finite_singleton 0).union
        (h1.union ((Set.finite_singleton x⁻¹).subset h2))).subset
        ?_
      intro u hu
      rcases hu with hu | hu | hu
      · left; exact hu
      · right; left; exact hu
      · right; right; exact hu
    refine (hfin.infinite_compl).mono fun u hu => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hu
    obtain ⟨hu0, hud, hxu⟩ := hu
    have hxu' : defectEps m x = 1 → 1 - x * u ≠ 0 := fun _ => sub_ne_zero.mpr (Ne.symm hxu)
    simp only [Set.mem_ofPred_eq]
    rw [eval_pfPoly _ _ _ hu0 hud hxu', eval_pfPoly _ _ _ hu0 hud hxu', ← h u hu0 hud hxu,
      ← rationalDefect_div_eq hm hx hq0 hq1 hu0 hud hxu]
  have hd0 : (2 * m + 1 : ℂ) ≠ 0 := by exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
  refine ⟨fun r hr => ?_, fun hd => ?_⟩
  · have := congrArg (Polynomial.eval (omega m ^ r)⁻¹) hpoly
    rw [eval_pfPoly_omega hr, eval_pfPoly_omega hr] at this
    have hne : (1 - x * (omega m ^ r)⁻¹) ^ defectEps m x ≠ 0 := by
      rcases Nat.eq_zero_or_pos (defectEps m x) with h | h
      · rw [h, pow_zero]; exact one_ne_zero
      · have hε : defectEps m x = 1 := le_antisymm (defectEps_le_one m x) h
        rw [hε, pow_one]
        exact one_sub_mul_ne_zero_of_eps hε (omega_pow_inv_pow_d m r)
    have hω : (omega m ^ r)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (omega_ne_zero m))
    exact mul_right_cancel₀ hω (mul_right_cancel₀ hd0 (mul_right_cancel₀ hne this))
  · have hε : defectEps m x = 1 := defectEps_eq_one_iff.mpr hd
    have := congrArg (Polynomial.eval x⁻¹) hpoly
    rw [eval_pfPoly_inv hx hε, eval_pfPoly_inv hx hε] at this
    have hxd : 1 - x⁻¹ ^ (2 * m + 1) ≠ 0 := by
      intro h0
      apply hd
      have : x⁻¹ ^ (2 * m + 1) = 1 := (sub_eq_zero.mp h0).symm
      rw [inv_pow] at this
      exact inv_eq_one.mp this
    exact mul_right_cancel₀ (inv_ne_zero hx) (mul_right_cancel₀ hxd this)

/-- `q Q_{d,x}(v;q)` extends to a holomorphic function of `q` on `|q| < 1`, for fixed `x ≠ 0` and
`v`. -/
theorem exists_differentiableOn_eq_mul_eval_rationalDefect {m : ℕ} (hm : 2 ≤ m) {x : ℂ}
    (hx : x ≠ 0) (v : ℂ) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * (rationalDefect m x q).eval v := by
  -- `q R_{d,x}(v;q)` extends holomorphically
  choose hc hcd hceq using fun a : Fin (2 * m) =>
    exists_differentiableOn_eq_mul_defectPoly_coeff hm hx (a := (a : ℕ)) (by omega)
  set hR : ℂ → ℂ := fun q => ∑ a : Fin (2 * m), hc a q * v ^ (a : ℕ) with hhR
  have hRd : DifferentiableOn ℂ hR (Metric.ball 0 1) := by
    refine DifferentiableOn.fun_sum fun a _ => ((hcd a).mul (differentiableOn_const _))
  have hReq : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → hR q = q * (defectPoly m x q).eval v := by
    intro q hq0 hq1
    rw [eval_eq_sum_range' (n := 2 * m) (by
      have := natDegree_defectPoly_le hm hx hq0 hq1; omega), Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hceq a q hq0 hq1]; ring
  have hg : DifferentiableOn ℂ (fun q => q * GProduct m x q) (Metric.ball 0 1) := by
    have := differentiableOn_gTail hm x 0
    refine differentiableOn_id.mul (this.congr fun q _ => ?_)
    simp [gTail]
  unfold rationalDefect
  split_ifs with hd h1
  · refine ⟨fun q => (1 - x * v) * (1 - v) * hR q - Cx m x * v ^ (2 * m) * (1 - v) *
      (q * GProduct m x q), ?_, fun q hq0 hq1 => ?_⟩
    · exact ((differentiableOn_const _).mul hRd).sub ((differentiableOn_const _).mul hg)
    · simp only [eval_sub, eval_mul, eval_one, eval_C, eval_X, eval_pow]
      rw [hReq q hq0 hq1]; ring
  · refine ⟨fun q => (1 - v) * hR q - (2 * m + 1) * v ^ (2 * m) * (q * GProduct m x q), ?_,
      fun q hq0 hq1 => ?_⟩
    · exact ((differentiableOn_const _).mul hRd).sub ((differentiableOn_const _).mul hg)
    · simp only [eval_sub, eval_mul, eval_one, eval_C, eval_X, eval_pow]
      rw [hReq q hq0 hq1]; ring
  · refine ⟨fun q => (1 - v) * hR q, (differentiableOn_const _).mul hRd, fun q hq0 hq1 => ?_⟩
    simp only [eval_mul, eval_sub, eval_one, eval_X]
    rw [hReq q hq0 hq1]; ring

/-- **Holomorphy of `D_{r,x}`** [AOS, Proposition 3.2]: for fixed `x ≠ 0`, `q D_{r,x}(q)` extends
holomorphically to `|q| < 1`; hence `D_{r,x}` is holomorphic on `0 < |q| < 1` with at most a simple
pole at `q = 0`. -/
theorem exists_differentiableOn_eq_mul_pfD {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) (r : ℕ) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * pfD m x q r := by
  obtain ⟨h, hd, heq⟩ := exists_differentiableOn_eq_mul_eval_rationalDefect hm hx (omega m ^ r)⁻¹
  refine ⟨fun q => omega m ^ r / ((2 * m + 1 : ℂ) * (1 - x * (omega m ^ r)⁻¹) ^ defectEps m x) *
    h q, (differentiableOn_const _).mul hd, fun q hq0 hq1 => ?_⟩
  simp only [pfD]
  rw [heq q hq0 hq1]
  ring

/-- **Holomorphy of `E_x`** [AOS, Proposition 3.2]: for fixed `x ≠ 0`, `q E_x(q)` extends
holomorphically to `|q| < 1`. -/
theorem exists_differentiableOn_eq_mul_pfE {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * pfE m x q := by
  by_cases hd : x ^ (2 * m + 1) = 1
  · exact ⟨fun _ => 0, differentiableOn_const _, fun q _ _ => by simp [pfE, hd]⟩
  obtain ⟨h, hdh, heq⟩ := exists_differentiableOn_eq_mul_eval_rationalDefect hm hx x⁻¹
  refine ⟨fun q => x / (1 - x⁻¹ ^ (2 * m + 1)) * h q, (differentiableOn_const _).mul hdh,
    fun q hq0 hq1 => ?_⟩
  simp only [pfE, ite_eq_right hd]
  rw [heq q hq0 hq1]
  ring

/-- A function `F` with `q F(q)` holomorphic on `|q| < 1` is holomorphic on `0 < |q| < 1`. -/
theorem differentiableOn_punctured_of_mul {F h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (Metric.ball 0 1))
    (heq : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * F q) :
    DifferentiableOn ℂ F {q : ℂ | 0 < ‖q‖ ∧ ‖q‖ < 1} := by
  have hopen : IsOpen {q : ℂ | 0 < ‖q‖ ∧ ‖q‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have h1 : DifferentiableOn ℂ (fun q => h q / q) {q : ℂ | 0 < ‖q‖ ∧ ‖q‖ < 1} :=
    (hd.mono fun q hq => mem_ball_zero_iff.mpr hq.2).div differentiableOn_id
      fun q hq => norm_pos_iff.mp hq.1
  refine h1.congr fun q hq => ?_
  rw [heq q hq.1 hq.2, mul_div_cancel_left₀ _ (norm_pos_iff.mp hq.1)]

end HigherDyson3
