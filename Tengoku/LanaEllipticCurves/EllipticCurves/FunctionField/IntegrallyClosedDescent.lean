/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of integral closedness along a faithfully flat extension

This file proves that **integral closedness descends along a faithfully flat algebra of domains**:

* `IsIntegrallyClosed.of_faithfullyFlat` : if `B` is a faithfully flat `A`-algebra, both `A` and `B`
  are domains, and `B` is integrally closed, then `A` is integrally closed.

This is a general commutative-algebra fact (no elliptic-curve content) and is a Mathlib-upstream
candidate. It is the ring-theoretic engine of the general-base-field normality of the affine
coordinate ring of a Weierstrass curve (issue #476, child A #477): with the algebraically-closed
case `isIntegrallyClosed_of_isAlgClosed` (`CoordinateRingNormalAlgClosed.lean`, PR #191) available,
this descends `IsIntegrallyClosed` from `F̄[W] = F[W] ⊗_F F̄` (faithfully flat over `F[W]`, as `F̄`
is free over `F`) down to `F[W]` for an arbitrary base field `F`.

## The mathematics

Work in the fraction fields `K = Frac A` and `L = Frac B`. Faithful flatness makes `algebraMap A B`
injective (`FaithfulSMul.algebraMap_injective`), so it lifts to an `A`-algebra hom `f : K →ₐ[A] L`.
Take `x ∈ K` integral over `A`; then `f x` is integral over `A`, hence over `B`, so by
`IsIntegrallyClosed B` we get `f x = algebraMap B L b` for some `b : B`. Writing `x = a / s`
(`a : A`, `s ∈ A⁰`) and comparing in `L` — where `algebraMap A L` factors through `algebraMap A B`
by the scalar tower — injectivity of `algebraMap B L` yields
`b · algebraMap A B s = algebraMap A B a` in `B`, i.e.
`algebraMap A B a ∈ (Ideal.span {s}).map (algebraMap A B)`. Faithful flatness contracts this ideal
(`Ideal.comap_map_eq_self_of_faithfullyFlat`), giving `a ∈ Ideal.span {s}`, i.e. `s ∣ a`. Hence
`x = a / s` is the image of the quotient and lies in `A`, so `A` is integrally closed.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.
* EGA IV, 6.5.4 (normality descends under faithfully flat morphisms).
-/

open scoped nonZeroDivisors

namespace IsIntegrallyClosed

/-- **Descent of integral closedness along a faithfully flat extension.**
If `B` is a faithfully flat `A`-algebra, `A` and `B` are integral domains, and `B` is integrally
closed, then `A` is integrally closed. -/
theorem of_faithfullyFlat {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A := by
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  -- `Frac B` is canonically an `A`-algebra via `A → B → Frac B` (scalar tower)
  have hAL : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hAB
  -- the induced `A`-algebra hom on fraction fields
  set f : FractionRing A →ₐ[A] FractionRing B :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId A (FractionRing B)) hAL with hf
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective A⁰ x
  have hspec := IsLocalization.mk'_spec (FractionRing A) a s
  -- `f x` is integral over `B`, hence lands in `B` by integral closedness
  have hxB : IsIntegral B (f (IsLocalization.mk' (FractionRing A) a s)) := (hx.map f).tower_top
  obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff (FractionRing B)).mp ‹IsIntegrallyClosed B› hxB
  -- image of `mk'_spec` under `f`, using `f` fixes the scalars
  have hEq1 : f (IsLocalization.mk' (FractionRing A) a s)
      * algebraMap A (FractionRing B) (s : A) = algebraMap A (FractionRing B) a := by
    have h := congrArg f hspec
    simpa only [map_mul, AlgHom.commutes] using h
  -- descend to a divisibility relation in `B`
  have hEqB : b * algebraMap A B (s : A) = algebraMap A B a := by
    apply IsFractionRing.injective B (FractionRing B)
    have e1 : algebraMap B (FractionRing B) (b * algebraMap A B (s : A))
        = algebraMap B (FractionRing B) b * algebraMap A (FractionRing B) (s : A) := by
      rw [map_mul, IsScalarTower.algebraMap_apply A B (FractionRing B) (s : A)]
    have e2 : algebraMap B (FractionRing B) (algebraMap A B a)
        = algebraMap A (FractionRing B) a :=
      (IsScalarTower.algebraMap_apply A B (FractionRing B) a).symm
    rw [e1, e2, hb]
    exact hEq1
  -- `algebraMap A B a` lies in the pushforward of `span {s}`, which faithful flatness contracts
  have hmem : algebraMap A B a ∈ (Ideal.span {(s : A)}).map (algebraMap A B) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, by rw [← hEqB, mul_comm]⟩
  have ha : a ∈ Ideal.span {(s : A)} := by
    have hcomap : a ∈ ((Ideal.span {(s : A)}).map (algebraMap A B)).comap (algebraMap A B) :=
      Ideal.mem_comap.mpr hmem
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  -- so `x = a / s = c` lies in `A`
  have hu : IsUnit (algebraMap A (FractionRing A) (s : A)) :=
    IsLocalization.map_units (FractionRing A) s
  refine ⟨c, mul_right_cancel₀ hu.ne_zero ?_⟩
  rw [hspec, ← map_mul]
  congr 1
  rw [hc]; ring

end IsIntegrallyClosed
