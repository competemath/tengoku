/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.AffinePurelyInseparable
import Tengoku.Seed.RingTheory.Algebraic.Integral
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.Polynomial.IsIntegral
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polynomial inclusion dominated by relative Frobenius

**Status:** a finite universally injective polynomial-algebra inclusion, over a perfect
field, internally yields a polynomial-algebra map in the reverse direction whose composite
is T to T^(p^n). Pure inseparability gives a common exponent. Integral closedness of k[T]
puts the powers in k[T], and inverse Frobenius on coefficients makes the map k-linear.
The coefficient algebra is only a domain; its normality is not assumed. Named consumer:
the actual finite Ga cover of the original normal subgroup (#21). This does not invert
or declare a scheme monomorphism of the original finite map.
-/

namespace AclGeom.FiniteGaCover
noncomputable section
open Polynomial
universe u

/-- Named consumer: a finite Ga cover of the actual normal subgroup. A finite radicial
polynomial-algebra inclusion is dominated by a relative Frobenius. This does not invert
that inclusion.
@isnad1 id=ex.2h4v.s9.15fa692cb944 from=translated src=- shape=96cacf23 vocab=1390bf09
-/
theorem exists_polynomial_frobenius_factor
    {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : ℕ) [ExpChar k p] [PerfectRing k p]
    (α : k[X] →ₐ[k] A) (hinj : Function.Injective α) (hfin : α.toRingHom.Finite)
    [AlgebraicGeometry.UniversallyInjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom α.toRingHom))] :
    ∃ (n : ℕ) (θ : A →ₐ[k] k[X]), Function.Injective θ ∧
      θ.comp α = aeval (X ^ p ^ n) := by
  let R := k[X]
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R A := α.toRingHom.toAlgebra
  have : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun c ↦ (α.commutes c).symm
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  have : Module.Finite R A := hfin
  have : IsScalarTower R A L := inferInstance
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr
    ((IsFractionRing.injective A L).comp hinj)
  let : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have : FiniteDimensional K L := inferInstance
  have : IsPurelyInseparable K L :=
    isPurelyInseparable_of_universallyInjective (R := R) (A := A) (K := K) (L := L)
  have : IsPurelyInseparable.HasExponent K L := inferInstance
  have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  let n := IsPurelyInseparable.exponent K L
  let f : L →+* K := IsPurelyInseparable.iterateFrobenius K L p (le_refl n)
  let π : A →+* K := f.comp (algebraMap A L)
  have hπ (a : A) : ∃ r : R, algebraMap R K r = π a := by
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (algebraMap K L).injective).mp
    change IsIntegral R (algebraMap K L (f (algebraMap A L a)))
    rw [IsPurelyInseparable.algebraMap_iterateFrobenius]
    exact ((Algebra.IsIntegral.isIntegral (R := R) a).algebraMap).pow _
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofLeftInverse
    (Classical.choose_spec (IsFractionRing.injective R K).hasLeftInverse)
  let πR : A →+* R := e.symm.toRingHom.comp (π.codRestrict _ hπ)
  have hπR (a : A) : algebraMap R K (πR a) = π a := by
    exact congrArg Subtype.val (e.apply_symm_apply (π.codRestrict _ hπ a))
  have hbase (r : R) : πR (α r) = r ^ p ^ n := by
    apply IsFractionRing.injective R K
    rw [hπR, map_pow]
    change f (algebraMap A L (algebraMap R A r)) = (algebraMap R K r) ^ p ^ n
    rw [← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L]
    exact IsPurelyInseparable.iterateFrobenius_algebraMap L p (le_refl n) _
  let σ := (iterateFrobeniusEquiv k p n).symm
  let θraw : A →+* R := (Polynomial.mapRingHom σ.toRingHom).comp πR
  have hc (c : k) : θraw (algebraMap k A c) = C c := by
    rw [← α.commutes c]
    change Polynomial.map σ.toRingHom (πR (α (C c))) = C c
    rw [hbase, Polynomial.map_pow, Polynomial.map_C]
    change C (σ c) ^ p ^ n = C c
    rw [← Polynomial.C_pow]
    apply congrArg C
    exact (iterateFrobeniusEquiv k p n).apply_symm_apply c
  let θ : A →ₐ[k] k[X] := { θraw with commutes' := hc }
  have hθinj : Function.Injective θ := by
    apply (Polynomial.map_injective σ.toRingHom σ.injective).comp
    intro a b hab
    have hh : π a = π b := (hπR a).symm.trans ((congrArg (algebraMap R K) hab).trans (hπR b))
    exact (IsFractionRing.injective A L) (f.injective hh)
  refine ⟨n, θ, hθinj, ?_⟩
  apply Polynomial.algHom_ext
  change Polynomial.map σ.toRingHom (πR (α X)) = (aeval (X ^ p ^ n)) X
  rw [hbase, Polynomial.map_pow, Polynomial.map_X, aeval_X]

end
end AclGeom.FiniteGaCover
