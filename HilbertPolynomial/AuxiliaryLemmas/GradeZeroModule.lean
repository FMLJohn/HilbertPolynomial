/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.GradedMulAction
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The i-th grade of a graded module over a graded semiring.

The main results of this file:
1. If `A` is a graded semiring and `M` is a graded `A`-module, then each grade
   of `M` is a module over the 0-th grade of `A`.
-/

variable {ιA ιM A M σ' σ : Type*}
variable [AddMonoid ιA] [DecidableEq ιA] [AddAction ιA ιM]
variable [Semiring A] [SetLike σ' A] [AddSubmonoidClass σ' A]
variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ M]
variable (𝒜 : ιA → σ') (ℳ : ιM → σ)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

namespace DirectSum

instance GradeZero.smul_at_i (i : ιM) : SMul (𝒜 0) (ℳ i) where
  smul a0 mi := ⟨a0.1 • mi, by
    have := SetLike.GradedSMul.smul_mem a0.2 mi.2
    rw [zero_vadd] at this
    exact this⟩

instance GradeZero.mulAction_at_i (i : ιM) : MulAction (𝒜 0) (ℳ i) :=
{ GradeZero.smul_at_i 𝒜 ℳ i with
  one_smul := fun _ => Subtype.ext <| show (1 : A) • _ = _ from one_smul _ _
  mul_smul := fun _ _ _ => Subtype.ext <| show ((_ : A) * (_ : A)) • _ = _ from mul_smul _ _ _ }

instance GradeZero.distribMulAction_at_i (i : ιM) : DistribMulAction (𝒜 0) (ℳ i) :=
{ GradeZero.mulAction_at_i 𝒜 ℳ i with
  smul_zero := λ a ↦ ZeroMemClass.coe_eq_zero.mp <| show (a : A) • (0 : M) = (0 : M) by
    exact smul_zero (a : A)
  smul_add := λ a x y ↦ SetCoe.ext <| show (a : A) • ((x : M) + (y : M)) =
    (a : A) • (x : M) + (a : A) • (y : M) by refine' smul_add ↑a ↑x ↑y }

/-- For each `i : ιM`, `ℳ i` is an `𝒜 0`-module. -/
instance GradeZero.module_at_i (i : ιM) : Module (𝒜 0) (ℳ i) :=
{ GradeZero.distribMulAction_at_i _ _ _ with
  add_smul := λ r s x ↦ SetCoe.ext <| show ((r : A) + (s : A)) • (x : M) =
    (r : A) • (x : M) + (s : A) • (x : M) by refine' add_smul ↑r ↑s ↑x
  zero_smul := λ x ↦ ZeroMemClass.coe_eq_zero.mp <| show (0 : A) • (x : M) = (0 : M) by
    refine' zero_smul A ↑x }

end DirectSum
