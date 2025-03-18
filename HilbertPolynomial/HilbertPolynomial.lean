/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import HilbertPolynomial.HilbertSerre.Theorem

import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Hilbert polynomials

Remember the assumptions in the file `HilbertPolynomial/HilbertSerre/Theorem.lean`:
`universe u`
`variable {A M : Type u}`
`variable [CommRing A] [noetherian_ring : IsNoetherianRing A]`
`variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]`
`variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)`
`variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]`
`variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)`
`variable (S : generatingSetOverBaseRing 𝒜)`

This file inherits all the above settings. With an additional assumption
`hS : (i : S.toFinset) → S.deg i.2 = 1`, the main things achieved in this file are:
1. formalising the Hilbert polynomial `HilbertSerre.hilbertPolynomial ℳ μ S : ℚ[X]`;
2. proving that for any large enough `n : ℕ`, the value of the additive function `μ` at `ℳ n`
   is equal to the value of the Hilbert polynomial at `n`;
3. showing that the polynomial `h` satisfying the above property (i.e. for any large enough
   `n : ℕ`, the value of `μ` at `ℳ n` equals the value of `h` at `n`) is unique;
4. proving a theorem `HilbertSerre.natDegree_hilbertPolynomial`, which tells us the specific
   degree of any non-zero Hilbert polynomial.
-/

universe u
variable {A M : Type u}
variable [CommRing A] [noetherian_ring : IsNoetherianRing A]
variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜) (hS : (i : S.toFinset) → S.deg i.2 = 1)

open AdditiveFunction BigOperators generatingSetOverBaseRing Polynomial PowerSeries

namespace HilbertSerre

variable {𝒜}

/--
Remember the Hilbert Serre Theorem (`hilbert_serre`), which says that there exists some
`p : ℤ[X]` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`. This definition is the
polynomial `p` guaranteed by `hilbert_serre`.
-/
noncomputable def numeratorPolynomial : Polynomial ℤ := (hilbert_serre 𝒜 ℳ μ S).choose

theorem numeratorPolynomial_mul_inv_poles_eq_poincareSeries :
    (numeratorPolynomial ℳ μ S).toPowerSeries * S.poles⁻¹ = μ.poincareSeries 𝒜 ℳ :=
  (hilbert_serre 𝒜 ℳ μ S).choose_spec.symm

/--
The Hilbert polynomial, i.e. the polynomial such that for any `n : ℕ` which
is big enough, the value of `μ` at `ℳ n` is equal to its value at `n`.
-/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  (Polynomial.map (Int.castRingHom ℚ) (numeratorPolynomial ℳ μ S)).hilbertPoly S.toFinset.card

variable {S}

include hS in
/--
The key property of the Hilbert polynomial, i.e. for any `n : ℕ` that is large enough,
the value of `μ` at `ℳ n` is equal to the value of the Hilbert polynomial at `n`.
-/
theorem AdditiveFunction_eq_hilbertPolynomial_eval
    {n : ℕ} (hn : (numeratorPolynomial ℳ μ S).natDegree < n) :
    μ.toFun (FGModuleCat.of (𝒜 0) (ℳ n)) = (hilbertPolynomial ℳ μ S).eval (n : ℚ) := by
  change Int.castRingHom ℚ _ = _
  have heq1 : μ.toFun (FGModuleCat.of (𝒜 0) (ℳ n)) = coeff ℤ n (μ.poincareSeries 𝒜 ℳ) := by
    rw [poincareSeries, coeff_mk]
    rfl
  have heq2 : (PowerSeries.map (Int.castRingHom ℚ)) (numeratorPolynomial ℳ μ S) =
      Polynomial.map (Int.castRingHom ℚ) (numeratorPolynomial ℳ μ S) := by
    ext n
    simp only [PowerSeries.coeff_map, coeff_coe, eq_intCast, polynomial_map_coe]
  have heq3 : map (Int.castRingHom ℚ) ↑S.poles⁻¹ = invOneSubPow ℚ S.toFinset.card := by
    simp only [poles, hS, pow_one, Finset.prod_const, Finset.card_attach, Units.inv_mk,
      invOneSubPow_eq_inv_one_sub_pow, inv_pow]
    refine Units.eq_inv_of_mul_eq_one_right ?_
    · have : ((1 - PowerSeries.X) ^ S.toFinset.card : ℚ⟦X⟧) = (PowerSeries.map (Int.castRingHom ℚ))
          ((1 - PowerSeries.X) ^ S.toFinset.card : ℤ⟦X⟧) := by
        simp only [map_pow, map_sub, map_one, PowerSeries.map_X]
      rw [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, this, ← map_mul]
      simp only [map_pow, map_sub, constantCoeff_X, sub_zero, one_pow, Units.val_one, invOfUnit_mul,
        map_one]
  rw [heq1, hilbertPolynomial, ← numeratorPolynomial_mul_inv_poles_eq_poincareSeries ℳ μ S,
    ← PowerSeries.coeff_map, map_mul, heq2, heq3, coeff_mul_invOneSubPow_eq_hilbertPoly_eval]
  exact lt_of_le_of_lt natDegree_map_le hn

include hS in
/--
The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h` satisfies the key
property of the Hilbert polynomial (i.e. for any large enough `n : ℕ`, the value of `μ` at `ℳ n`
equals the value of `h` at `n`), then `h` is the Hilbert polynomial itself.
-/
theorem exists_unique_hilbertPolynomial :
    ∃! h : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
    μ.toFun (FGModuleCat.of (𝒜 0) (ℳ n)) = h.eval (n : ℚ) := by
  use hilbertPolynomial ℳ μ S; constructor
  · use (numeratorPolynomial ℳ μ S).natDegree
    exact fun n hn => AdditiveFunction_eq_hilbertPolynomial_eval ℳ μ hS hn
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPolynomial ℳ μ S)
    apply ((Set.Ioi_infinite (max N (numeratorPolynomial ℳ μ S).natDegree)).image
      Nat.cast_injective.injOn).mono
    rintro x ⟨n, hn, rfl⟩
    simp only [Set.mem_Ioi, sup_lt_iff, Set.mem_setOf_eq] at hn ⊢
    rw [← AdditiveFunction_eq_hilbertPolynomial_eval ℳ μ hS hn.2, hhN n hn.1]

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbertPolynomial (hhP : hilbertPolynomial ℳ μ S ≠ 0) :
    (hilbertPolynomial ℳ μ S).natDegree =
    S.toFinset.card - (numeratorPolynomial ℳ μ S).rootMultiplicity 1 - 1 := by
  simp only [hilbertPolynomial, Polynomial.natDegree_hilbertPoly_of_ne_zero hhP,
    eq_rootMultiplicity_map (Int.castRingHom ℚ).injective_int, eq_intCast, Int.cast_one]

end HilbertSerre
