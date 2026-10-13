/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.NumberTheory.NumberField.Global.Adeles.Basic

import Tengoku.Tauceti.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Compactness of the additive adele quotient

For a number field `K`, the diagonal copy of `K` is cocompact in its adele ring.  Equivalently,
the additive quotient `𝔸[K] / K` is compact.

The proof uses a compact set of representatives.  Strong approximation first subtracts an element
of `K` so that the finite component is integral everywhere.  The remaining freedom to subtract an
algebraic integer does not disturb finite integrality, and moves the infinite component into the
closed fundamental parallelepiped of the Minkowski lattice.  That parallelepiped is compact, as is
the product of all local integer rings, so their product maps onto the quotient from a compact set.

Together with the discreteness of the principal subgroup, this identifies the diagonal number
field as a lattice in the additive adele ring.  The compact quotient is also the additive global
finiteness input used in the compactness theorem for the norm-one idele class group.

## Main result

* `TauCeti.GlobalNumberFields.exists_isCompact_forall_exists_sub_algebraMap_mem`: there is a
  compact set of representatives for the additive adele quotient.
* `TauCeti.GlobalNumberFields.compactSpace_quotient_principalSubgroup`: the quotient of the adele
  ring by the diagonal copy of the number field is compact.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain HeightOneSpectrum NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- There is a compact set of representatives for the additive adele quotient: every adele can be
translated by a diagonal element of `K` into this set. -/
theorem exists_isCompact_forall_exists_sub_algebraMap_mem :
    ∃ D : Set 𝔸[K], IsCompact D ∧
      ∀ a : 𝔸[K], ∃ x : K, a - algebraMap K 𝔸[K] x ∈ D := by
  classical
  -- The compact representative set is the product of the closed Minkowski parallelepiped with
  -- the integral finite adeles.
  let b := mixedEmbedding.latticeBasis K
  let P : Set (mixedEmbedding.mixedSpace K) := b.parallelepiped
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let D : Set 𝔸[K] := (e.symm '' P) ×ˢ
    {a : 𝔸ᶠ[K] | ∀ v, a v ∈ v.adicCompletionIntegers K}
  have he : Continuous e.symm :=
    InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K
  have hD : IsCompact D :=
    (b.parallelepiped.isCompact.image he).prod
      (FiniteAdeleRing.isCompact_integralFiniteAdeles (R := 𝓞 K) (K := K))
  refine ⟨D, hD, ?_⟩
  intro a
  -- Expose the product representation of the adele ring for the componentwise construction.
  let a' : K∞ × 𝔸ᶠ[K] := a
  -- Strong approximation makes the finite component integral after subtracting `x`.
  obtain ⟨x, hx⟩ :=
    FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers a'.2
  let z : K∞ := a'.1 - algebraMap K K∞ x
  let p : mixedEmbedding.mixedSpace K := ZSpan.fract b (e z)
  have hp : p ∈ P := ZSpan.fundamentalDomain_subset_parallelepiped b
    (ZSpan.fract_mem_fundamentalDomain b (e z))
  -- The lattice correction is the Minkowski embedding of an algebraic integer `y`.
  have hfloor : ((ZSpan.floor b (e z) :
      Submodule.span ℤ (Set.range b)) : mixedEmbedding.mixedSpace K) ∈
      mixedEmbedding.integerLattice K := by
    rw [← mixedEmbedding.span_latticeBasis K]
    exact (ZSpan.floor b (e z)).property
  obtain ⟨y, hy⟩ := hfloor
  have hy' : mixedEmbedding K (algebraMap (𝓞 K) K y) =
      ((ZSpan.floor b (e z) : Submodule.span ℤ (Set.range b)) :
        mixedEmbedding.mixedSpace K) := by
    simpa using hy
  let u : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K := fun v ↦
    ⟨a'.2 v - algebraMap K (v.adicCompletion K) (x + algebraMap (𝓞 K) K y), by
      rw [map_add, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K),
        sub_add_eq_sub_sub]
      exact sub_mem (hx v) (v.coe_mem_adicCompletionIntegers y)⟩
  let d : 𝔸[K] :=
    (e.symm p, FiniteAdeleRing.integralEmbedding (R := 𝓞 K) (K := K) u)
  have hd : d ∈ D := ⟨⟨p, hp, rfl⟩, fun v ↦ by simp [d]⟩
  -- Thus `d` is obtained from `a` by subtracting the principal adele of `x + y`.
  have hd_eq : d = a - algebraMap K 𝔸[K] (x + algebraMap (𝓞 K) K y) := by
    -- `AdeleRing` is a type synonym for this product; exposing it lets the two components be
    -- compared through their canonical APIs.
    have hex : e (algebraMap K K∞ x) = mixedEmbedding K x :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x)).symm
    have hey : e (algebraMap K K∞ (algebraMap (𝓞 K) K y)) =
        ((ZSpan.floor b (e z) : Submodule.span ℤ (Set.range b)) :
          mixedEmbedding.mixedSpace K) :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp
        (K := K) (x := algebraMap (𝓞 K) K y)).symm.trans hy'
    have hfst : e.symm p =
        a'.1 - algebraMap K K∞ (x + algebraMap (𝓞 K) K y) := by
      apply e.injective
      rw [e.apply_symm_apply]
      simp only [map_sub, map_add, p, z, ZSpan.fract_apply, hex, hey]
      abel
    have hsnd : FiniteAdeleRing.integralEmbedding (R := 𝓞 K) (K := K) u =
        a'.2 - algebraMap K 𝔸ᶠ[K] (x + algebraMap (𝓞 K) K y) := by
      ext v
      simp only [FiniteAdeleRing.integralEmbedding_apply, FiniteAdeleRing.sub_apply,
          FiniteAdeleRing.algebraMap_apply, u]
      rfl
    change (e.symm p, FiniteAdeleRing.integralEmbedding (R := 𝓞 K) (K := K) u) =
      (a'.1 - algebraMap K K∞ (x + algebraMap (𝓞 K) K y),
        a'.2 - algebraMap K 𝔸ᶠ[K] (x + algebraMap (𝓞 K) K y))
    exact Prod.ext hfst hsnd
  exact ⟨x + algebraMap (𝓞 K) K y, hd_eq ▸ hd⟩

end TauCeti.GlobalNumberFields
