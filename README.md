# Hilbert Polynomials of Graded Modules

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

In this repository, we have formalised the Hilbert polynomial of a graded module based on the Hilbert--Serre Theorem.

## Preliminary Definitions

1. `AdditiveFunction 𝒞 G`. Given an abelian category `𝒞` and an additive commutative group `G`, a function `λ` from the class of all objects of
`𝒞` to `G` is additive if `λ B = λ A + λ C` for every short exact sequence `0 --> A --> B --> C --> 0` in `𝒞`. `AdditiveFunction 𝒞 G` is the type of all additive functions from `𝒞` to `G`; we denote it as `𝒞 ⟹+ G`.
2. `generatingSetOverBaseRing 𝒜`. Given a commutative ring `A` and a function `𝒜 : ℕ → AddSubgroup A` with `GradedRing 𝒜`, if `S : generatingSetOverBaseRing 𝒜`, then `S` is a finite collection of homogeneous elements of `A` that generates `A` over `𝒜 0`.

From now on, unless stated otherwise, we assume the following:
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

4. `S.poles`. The polynomial `∏ i ∈ S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)`, which has an inverse in `ℤ⟦X⟧ˣ`.
5. `μ.poincareSeries 𝒜 ℳ`. The Poincaré series of the graded module `M` with respect to `μ`, which is the power series
`∑ᵢ μ(Mᵢ) Xⁱ ∈ ℤ⟦X⟧`.

## Main Result/Definition

1. `hilbert_serre 𝒜 ℳ μ S`. There exists a polynomial `p : Polynomial ℤ` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`.
2. 
