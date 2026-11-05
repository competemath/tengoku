/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.Algebraic.Integral
import Tengoku.Seed.Algebra.Polynomial.Basis
import Tengoku.Seed.RingTheory.TensorProduct.Nontrivial
import Tengoku.Seed.RingTheory.FiniteStability
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficient fields detected by faithful point actions

Named consumer: the actual coefficient-rank producer in blueprint `lem:affine-action`.
An injective map on algebraically closed base-field points forces the tensor diagonal to
be nilpotent. A transcendental parameter has a nonnilpotent tensor diagonal, so a faithful
coefficient map cannot lower the function-field transcendence degree. Pure inseparability
is permitted; no infinitesimal-faithfulness shortcut is used.

**Status:** proved. `SchemeActionCoefficientAlgebraicity` supplies the actual coefficient-map
application; `SchemeActionGenus` derives rank and genus zero after constants. `SchemeCurveGenus`
proves original-base genus and rationality for faithful regular affine curve actions. Non-affine
and rational-action cases and arbitrary-action classification remain open.
-/

namespace AclGeom

noncomputable section

open TensorProduct

/-- An element vanishing at every point of a finite-type algebra over an algebraically closed
field is nilpotent. Named consumers: the faithful coefficient-rank argument and specialization
in constant-field rationality descent.-/
theorem isNilpotent_of_forall_algHom_eq_zero {k S : Type*} [Field k] [IsAlgClosed k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] {z : S}
    (hz : ∀ φ : S →ₐ[k] k, φ z = 0) : IsNilpotent z := by
  let : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  have hrad : z ∈ (⊥ : Ideal S).radical := by
    rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
    intro M hM
    let : M.IsMaximal := hM.2
    let : Field (S ⧸ M) := Ideal.Quotient.field M
    let : Module.Finite k (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ M)
    let φ : (S ⧸ M) →ₐ[k] k := IsAlgClosed.lift
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply φ.injective
    change (φ.comp (Ideal.Quotient.mkₐ k M)) z = φ 0
    rw [map_zero]
    exact hz _
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  exact ⟨n, Ideal.mem_bot.mp hn⟩

/-- Independent powers stay independent under extension of constants. Named consumer: the
nonnilpotent diagonal of a transcendental parameter.-/
theorem transcendental_one_tmul {L C E : Type*} [Field L] [Field C] [Field E]
    [Algebra L C] [Algebra L E] {r : E} (hr : Transcendental L r) :
    Transcendental C ((1 : C) ⊗ₜ[L] r : C ⊗[L] E) := by
  have hp : LinearIndependent L (fun n : ℕ ↦ r ^ n) := by
    have h := (Polynomial.basisMonomials L).linearIndependent.map'
      (Polynomial.aeval r).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hr))
    have he : (Polynomial.aeval r).toLinearMap ∘ Polynomial.basisMonomials L =
        fun n : ℕ ↦ r ^ n := by
      funext n
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, Polynomial.coe_basisMonomials,
        Polynomial.aeval_monomial, map_one, one_mul]
    rw [he] at h
    exact h
  have ht := Module.Flat.linearIndependent_one_tmul (S := C) hp
  have he : (Polynomial.aeval ((1 : C) ⊗ₜ[L] r : C ⊗[L] E)).toLinearMap ∘
      Polynomial.basisMonomials C = fun n : ℕ ↦ (1 : C) ⊗ₜ[L] (r ^ n) := by
    funext n
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, Polynomial.coe_basisMonomials,
      Polynomial.aeval_monomial, map_one, one_mul, Algebra.TensorProduct.tmul_pow, one_pow]
  apply transcendental_iff_injective.mpr
  apply LinearMap.injective_of_linearIndependent
    (f := (Polynomial.aeval ((1 : C) ⊗ₜ[L] r : C ⊗[L] E)).toLinearMap)
    (Polynomial.basisMonomials C).span_eq
  rw [he]
  exact ht

/-- A transcendental element has a nonnilpotent tensor diagonal. Named consumer: algebraicity
of the coefficient-field inclusion detected by faithful base-field points.-/
theorem not_isNilpotent_tensor_diagonal {L E : Type*} [Field L] [Field E] [Algebra L E]
    {r : E} (hr : Transcendental L r) :
    ¬ IsNilpotent (r ⊗ₜ[L] (1 : E) - (1 : E) ⊗ₜ[L] r) := by
  have : Nontrivial (E ⊗[L] E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain L E E
      (algebraMap L E).injective (algebraMap L E).injective
  intro hnil
  obtain ⟨n, hn⟩ := hnil
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp only [pow_zero, one_ne_zero] at hn
  have hal : IsAlgebraic E (r ⊗ₜ[L] (1 : E) - (1 : E) ⊗ₜ[L] r) :=
    IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn0) (by rw [hn]; exact isAlgebraic_zero)
  have hc : IsAlgebraic E (r ⊗ₜ[L] (1 : E)) := by
    change IsAlgebraic E (algebraMap E (E ⊗[L] E) r)
    exact isAlgebraic_algebraMap r
  apply transcendental_one_tmul (C := E) hr
  have he : -(r ⊗ₜ[L] (1 : E) - (1 : E) ⊗ₜ[L] r) + r ⊗ₜ[L] (1 : E) =
      (1 : E) ⊗ₜ[L] r := by rw [neg_sub, sub_add_cancel]
  rw [← he]
  exact hal.neg.add hc

/-- Injective restriction of base-field points makes the tensor diagonal nilpotent.
Named consumer: `isAlgebraic_fractionRing_of_injective_points`.-/
theorem tensor_diagonal_isNilpotent_of_injective_points
    {k B A : Type*} [Field k] [IsAlgClosed k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    [Algebra.FiniteType k A]
    (hpoints : Function.Injective
      (fun φ : A →ₐ[k] k ↦ φ.comp (IsScalarTower.toAlgHom k B A))) (a : A) :
    IsNilpotent (a ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] a) := by
  let : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
  have : Algebra.FiniteType k (A ⊗[B] A) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero (k := k)
  intro φ
  let f : A →ₐ[k] k := φ.comp
    ((Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] A).restrictScalars k)
  let g : A →ₐ[k] k := φ.comp
    ((Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars k)
  have he : f.comp (IsScalarTower.toAlgHom k B A) =
      g.comp (IsScalarTower.toAlgHom k B A) := by
    ext b
    change φ ((Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] A)
        (algebraMap B A b)) =
      φ ((Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A) (algebraMap B A b))
    rw [AlgHom.commutes, AlgHom.commutes]
  have hf := hpoints he
  rw [map_sub]
  exact sub_eq_zero.mpr (AlgHom.congr_fun hf a)

/-- The fraction field of a finite-type domain is algebraic over a compatible coefficient
field when restriction of base-field points to the coefficient ring is injective.
Pure inseparability is allowed.
Named consumer: the actual generic-action coefficient field has the full group rank.-/
theorem isAlgebraic_fractionRing_of_injective_points
    {k B A C E : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [CommRing A] [IsDomain A] [Algebra k B] [Algebra k A] [Algebra B A]
    [IsScalarTower k B A] [Algebra.FiniteType k A]
    [Field C] [Field E] [Algebra B C]
    [Algebra A E] [IsFractionRing A E] [Algebra B E] [IsScalarTower B A E]
    [Algebra C E] [IsScalarTower B C E]
    (hpoints : Function.Injective
      (fun φ : A →ₐ[k] k ↦ φ.comp (IsScalarTower.toAlgHom k B A))) :
    Algebra.IsAlgebraic C E := by
  have ha (a : A) : IsAlgebraic C (algebraMap A E a) := by
    by_contra h
    have htr : Transcendental C (algebraMap A E a) := h
    have hd := tensor_diagonal_isNilpotent_of_injective_points hpoints a
    let f : A →ₐ[B] E ⊗[C] E :=
      ((Algebra.TensorProduct.includeLeft : E →ₐ[C] E ⊗[C] E).restrictScalars B).comp
        (IsScalarTower.toAlgHom B A E)
    let g : A →ₐ[B] E ⊗[C] E :=
      ((Algebra.TensorProduct.includeRight : E →ₐ[C] E ⊗[C] E).restrictScalars B).comp
        (IsScalarTower.toAlgHom B A E)
    let ψ : A ⊗[B] A →ₐ[B] E ⊗[C] E :=
      Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
    have hd' : IsNilpotent ((algebraMap A E a) ⊗ₜ[C] (1 : E) -
        (1 : E) ⊗ₜ[C] (algebraMap A E a)) := by
      have hm := hd.map ψ
      change IsNilpotent (ψ (a ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] a)) at hm
      rw [map_sub, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul] at hm
      simp only [map_one, mul_one, one_mul] at hm
      exact hm
    exact not_isNilpotent_tensor_diagonal htr hd'
  constructor
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [div_eq_mul_inv]
  exact (ha a).mul (IsAlgebraic.inv (ha b))

end

end AclGeom
