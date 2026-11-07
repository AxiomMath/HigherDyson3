/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Definitions for the characterization of the Dyson seed

The objects of [AOS, §7] beyond those its statements use, which are in
`HigherDyson3.Definitions`: the ratios `h_i(c)`, the Lambert-type solutions `S_j(c)`, the
eigen-solutions `Z^{(k)}`, the general Lambert seed `Φ` with residue function `ρ_Φ`, and the formal
series `R_m(ζ_d; q)` in `ℤ[[q]]`.

Throughout, `m ≥ 2`, `d = 2m + 1`, `x = e(α)` is a root of unity, and `ω = e(1/d)`. For `c = e(β)`
the orbit `𝒟_c` of [AOS, (7.8)] is `divisor β`.
-/

public section

noncomputable section

open Complex Finset

namespace HigherDyson3

/-- The ratio `h_i(c) = (cq;q)_i / (c^d q^d; q^d)_i` of [AOS, (7.2)]. -/
@[expose]
def hRatio (m : ℕ) (c q : ℂ) (i : ℕ) : ℂ :=
  qPochhammer (c * q) q i / qPochhammer (c ^ (2 * m + 1) * q ^ (2 * m + 1)) (q ^ (2 * m + 1)) i

/-- The Lambert-type solution `S_j(c) = λ^j ∑_{i ≥ 0} λ^{2i} q^{i² + ij} h_i(c)`, `λ = c/x`,
of [AOS, (7.5)], for `j ∈ ℤ`. -/
@[expose]
def lambertSolution (m : ℕ) (x c q : ℂ) (j : ℤ) : ℂ :=
  (c / x) ^ j * ∑' i : ℕ, (c / x) ^ (2 * i) * q ^ ((i : ℤ) ^ 2 + i * j) * hRatio m c q i

/-- The eigen-solution `Z^{(k)} = (S_j(ω^k))_{j ≥ 0}` of [AOS, (7.12)]. -/
@[expose]
def eigenSolution (m : ℕ) (x q : ℂ) (k : ℕ) : ℕ → ℂ :=
  fun j => lambertSolution m x (omega m ^ k) q j

/-- The coefficients `b_i(c) = λ^{2i} q^{i²} h_i(c)`, `λ = c/x`, of [AOS, Lemma 7.2(d)]. -/
@[expose]
def lambertCoeff (m : ℕ) (x c : ℂ) (i : ℕ) (q : ℂ) : ℂ :=
  (c / x) ^ (2 * i) * q ^ (i ^ 2) * hRatio m c q i

/-- The Lambert-type seed `Φ(u) = x^{-2} ∑_{i ≥ 0} b_i(q) / (1 - c q^i u)` of [AOS, (7.10)],
written as a function of `(u, q)`. -/
@[expose]
def lambertSeed (x c : ℂ) (b : ℕ → ℂ → ℂ) (u q : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * ∑' i : ℕ, b i q / (1 - c * q ^ i * u)

/-- The residue function `ρ_Φ(τ) = x^{-2} ∑_{i ≥ 0} x^{2i} c^{2mi} q^{mi²} b_i(q)` of
[AOS, (7.11)], with `x = e(α)`, `q = e(τ)`. -/
@[expose]
def lambertResidue (m : ℕ) (α : ℚ) (c : ℂ) (b : ℕ → ℂ → ℂ) (τ : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * ∑' i : ℕ, e α ^ (2 * i) * c ^ (2 * m * i) * e τ ^ (m * i ^ 2) * b i (e τ)

/-- The formal finite `q`-Pochhammer symbol `(q^a; q^a)_n = ∏_{r=1}^n (1 - q^{ar})` in `ℤ[[q]]`. -/
@[expose]
def formalQPoch (a n : ℕ) : PowerSeries ℤ := ∏ r ∈ Icc 1 n, (1 - PowerSeries.X ^ (a * r))

/-- The formal series `∑_{n ≥ 0} q^{n²} (q;q)_n / (q^d;q^d)_n ∈ ℤ[[q]]`, `d = 2m + 1`, which is
`R_m(ζ_d; q)` at a primitive `d`-th root of unity [AOS, §1, §2]; coefficientwise, the `N`-th
coefficient only involves `n ≤ N`. -/
@[expose]
def primitiveRankSeries (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => ∑ n ∈ range (N + 1), PowerSeries.coeff N
    (PowerSeries.X ^ (n ^ 2) * formalQPoch 1 n *
      PowerSeries.invOfUnit (formalQPoch (2 * m + 1) n) 1)

end HigherDyson3
