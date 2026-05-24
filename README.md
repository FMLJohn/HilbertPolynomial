# Hilbert Polynomials of Graded Modules

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

In this repository, we have formalised the Hilbert polynomial of a graded module.

## Main Definitions

1. `AdditiveFunction 𝒞 G`. Given an abelian category `𝒞` and an additive commutative group `G`, a function `μ` from the class of all objects of
`𝒞` to `G` is additive if `μ B = μ A + μ C` for every short exact sequence `0 --> A --> B --> C --> 0` in `𝒞`. `AdditiveFunction 𝒞 G` is the type of all additive functions from `𝒞` to `G`.

The next few definitions are based on the following assumptions:

```
universe u

variable {A M : Type u}

variable [CommRing A] [noetherian_ring : IsNoetherianRing A]

variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]

variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)

variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
```

## Main Results
