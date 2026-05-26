# Hilbert Polynomials of Graded Modules

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

In this repository, we have formalised the Hilbert polynomial of a graded module based on the Hilbert--Serre Theorem.

## Build Instructions

1. Ensure that `git` is installed. If it is not already installed, see:
https://git-scm.com/downloads
2. Install Lean 4 via `elan`: https://lean-lang.org/install/
3. Clone the repository:
```
git clone https://github.com/FMLJohn/HilbertPolynomial.git
cd HilbertPolynomial
```
4. Fetch the Mathlib build cache:
```
lake exe cache get
```
5. Build the project
```
lake build HilbertPolynomial
```

## How to Use the Blueprint

## Preliminary Definitions

1. `AdditiveFunction 𝒞 G`. Given an abelian category `𝒞` and an additive commutative group `G`, a function `λ` from the class of all objects of
`𝒞` to `G` is additive if `λ B = λ A + λ C` for every short exact sequence `0 --> A --> B --> C --> 0` in `𝒞`. `AdditiveFunction 𝒞 G` is the type of all additive functions from `𝒞` to `G`; we denote it as `𝒞 ⟹+ G`.
2. `generatingSetOverBaseRing 𝒜`. Given a commutative ring `A` and a function `𝒜 : ℕ → AddSubgroup A` with `GradedRing 𝒜`, if `S : generatingSetOverBaseRing 𝒜`, then `S` is a finite collection of homogeneous elements of `A` that generates `A` over `𝒜 0`.

From this point onward in this page, unless stated otherwise, we assume the following:
```
universe u
variable {A M : Type u}
variable [CommRing A] [noetherian_ring : IsNoetherianRing A]
variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜)
```

3. `S.poles`. The polynomial `∏ i ∈ S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)`, which has an inverse in `ℤ⟦X⟧ˣ`.
4. `μ.poincareSeries 𝒜 ℳ`. The Poincaré series of the graded module `M` with respect to `μ`, which is the power series
`∑ᵢ μ(Mᵢ) Xⁱ ∈ ℤ⟦X⟧`.

## Main Results and Definitions

1. `hilbert_serre 𝒜 ℳ μ S`. There exists a polynomial `p : Polynomial ℤ` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`.
2. `HilbertSerre.numeratorPolynomial ℳ μ S`. The polynomial `(hilbert_serre 𝒜 ℳ μ S).choose`.
3. `HilbertSerre.hilbertPolynomial ℳ μ S`. The Hilbert polynomial of `M` with respect to `μ`, which is defined as `((numeratorPolynomial ℳ μ S).map (Int.castRingHom ℚ)).hilbertPoly S.toFinset.card`.

From now on, assume that `hS : (i : S.toFinset) → S.deg i.2 = 1`.

4. `HilbertSerre.AdditiveFunction_eq_hilbertPolynomial_eval ℳ μ hS hn`. The key property of the Hilbert polynomial, i.e. for any `n : ℕ` that is large enough, the value of `μ` at `ℳ n` equals the value of the Hilbert polynomial at `n`.
5. `HilbertSerre.exists_unique_hilbertPolynomial ℳ μ hS`. The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h` satisfies the key property of the Hilbert polynomial, then `h` is the Hilbert polynomial itself.
6. `HilbertSerre.natDegree_hilbertPolynomial ℳ μ hhP`. If `hhP : hilbertPolynomial ℳ μ S ≠ 0`, then the degree of the Hilbert polynomial equals `S.toFinset.card - (numeratorPolynomial ℳ μ S).rootMultiplicity 1 - 1`.
