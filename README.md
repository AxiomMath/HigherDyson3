[![](logo.svg)](https://axiommath.ai/)

# Beyond Mock Modularity: Elliptic Corrections for Higher Dyson Ranks

This is a Lean formalization of the paper of Alfes, Ono and Swaminathan on higher Dyson ranks and the elliptic corrections to their generating functions. Every numbered result of the paper is proved; the main results are listed below.

## Main Results

* For every `m ≥ 1`, the coefficient `[z^r][q^N] R_m(z;q)` equals the full-rank count `N_m(r,N)`.
* For every `m ≥ 1`, the full-rank count is symmetric: `N_m(r,N) = N_m(-r,N)`.
* For `m ≥ 2`, `d = 2m+1`, `x ≠ 0` and `0 < |q| < 1`, the seed values satisfy `∑_{r<d} x^r X_{j+r-2} - q^{j-1} X_j = C_x G_d(x;q)`.
* The constant `C_x` vanishes for every `x ≠ 1` with `x^d = 1`.
* The seed `G_{d,x}(u;q)` satisfies the finite functional equation in `u ↦ qu` with defect polynomial `R_{d,x}(U;q)`.
* The defect polynomial is the unique polynomial of degree at most `d-2` for which that functional equation holds on a nonempty open set.
* The defect polynomial `R_{d,x}(U;q)` has degree at most `d-2`.
* The constant term of `R_{d,x}(U;q)` is `-X_0(x;q)`.
* Each coefficient `q [U^a] R_{d,x}(U;q)` extends holomorphically to the open unit disk.
* For `x = e(α)` with `α ∈ ℚ ∩ [0,1)`, the series defining `E_{m,x}` converges normally on compact subsets of `(ℍ × ℂ) \ D_x`.
* The periodization `E_{m,x}` is holomorphic on `(ℍ × ℂ) \ D_x`.
* `E_{m,x}` satisfies the twisted elliptic transformation law under `w ↦ w + aτ + b`.
* The residue function `ρ_{m,x}` is holomorphic on `ℍ`.
* `ρ_{m,x}(τ) = x^{-2} + O(|e(τ)|)` as `Im τ → ∞`.
* `E_{m,x}` has at most simple poles along each component of `D_x`.
* The residue of `E_{m,x}` at `w = -α + aτ + b` is `-ρ_{m,x}(τ) x^{2(m+1)a} q^{-ma²} / (2πi)`.
* Where `ρ_{m,x}(τ) ≠ 0`, the pole of `E_{m,x}` at each point of `D_x` is genuine.
* Where `ρ_{m,x}(τ) = 0`, the singularity of `E_{m,x}` at each point of `D_x` is removable.
* `E_{m,x}` is not identically zero.
* The shift `w ↦ E_{m,x}(τ, w + α/m)` satisfies the untwisted elliptic transformation law.
* The finite part `E^fin_{m,x}` extends holomorphically to `ℍ × ℂ`.
* `E^fin_{m,x}` satisfies the twisted elliptic transformation law.
* The shift `w ↦ E^fin_{m,x}(τ, w + α/m)` satisfies the untwisted elliptic transformation law.
* `E^fin_{m,x}(τ, w + α/m) = ∑_{ℓ<2m} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ,w)`.
* The coefficients `h_{m,ℓ,x}` in that theta decomposition are unique.
* The series defining `h_{m,ℓ,x}` converges normally on compact subsets of `ℍ`.
* Each `h_{m,ℓ,x}` is holomorphic on `ℍ`.
* `h_{m,ℓ,x}(τ) = e(ℓα/m) x^{ℓ-2} e(c_ℓ τ) + O(|e((c_ℓ+2)τ)|)` with `c_ℓ = 1 + ℓ - ℓ²/(4m)`.
* No `h_{m,ℓ,x}` is identically zero on `ℍ`.
* `E^fin_{m,x}` is not identically zero.
* For `x = 1`, `h_{m,ℓ,1}(it)` is a positive real number for every `t > 0`.
* For `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0,1)` and `q = e(τ)` with `τ ∈ ℍ`, the sequence `X_j(x;q) / G_d(x;q)` solves the finite recurrence and tends to `1`; it is the only solution of the recurrence, for any constant `γ`, that tends to `1`, and that constant is `γ = 1` whenever `C_x ≠ 0`.
* The seed of every solution `Y` of the recurrence converges on `|u| < 1` and continues meromorphically to `ℂ`, with at most simple poles at the points `x^{-1}q^{-i}` and `ω^{-k}q^{-i}`, where `ω = e(1/d)`.
* The periodization of that continuation converges normally on compact sets off the orbits `D_x ∪ ⋃_k D_{ω^k}`, is holomorphic there, has at most simple poles, and satisfies the twisted elliptic transformation law.
* The exceptional set `Ξ_m` of `q` at which some residue function `ρ^{(k)}` vanishes is discrete in the punctured unit disk and contains no `q` with `0 < |q| ≤ 1/2`.
* For `q ∉ Ξ_m`, the periodization of a solution `Y` is holomorphic off `D_x` if and only if `Y` is a multiple of `(X_j(x;q))_j`.
* For `q ∉ Ξ_m` and each `ω^k ≠ x`, some solution of the recurrence with `γ = 0` has a periodization whose poles lie exactly along `D_{ω^k}`, each one genuine.
* For a primitive `d`-th root of unity `ζ`, the backward polynomial `P_J ∈ ℤ[q]` satisfies `R_m(ζ;q) ≡ P_J(q) (mod q^{J+1})`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been verified with the comparator (Lean kernel only).
