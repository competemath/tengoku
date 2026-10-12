/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import Tengoku.Tauceti.TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension

/-!
# The graded Ext-Euler characteristic

Let `C` be a `k`-linear abelian category with a chosen grading-shift autoequivalence `e`.
The bigraded Ext groups of two objects are

```text
Ext^{n,j}(X,Y) = Ext^n(X,Y{j}).
```

Their q-Euler characteristic is the Laurent polynomial

```text
χ_q(X,Y) = ∑ n, (-1)^n ∑ j, q⁻ʲ dim_k Ext^{n,j}(X,Y).
```

This construction uses two separate support conditions.  For each cohomological degree, the
internal-degree family must have finite Laurent support, and the Ext groups must vanish in every
internal degree above a common cohomological bound.  These conditions are recorded separately by
`TauCeti.IsGradedExtInternallyFinite` and
`TauCeti.IsGradedExtBounded`.  Their conjunction `TauCeti.IsGradedEulerAdmissible` is consumed by
`TauCeti.gradedExtEuler`; no infinite sum or totalized `finsum` occurs.

The internal-degree convention is inherited from
`TauCeti.targetShiftGradedDimension`: shifting the target by `j` contributes `q⁻ʲ`.  The
characteristic coefficient theorem makes both signs visible and is the supported way to compute
the polynomial.

## Main definitions

* `TauCeti.GradedExt`: the bigraded family `Ext^n(X,Y{j})`.
* `TauCeti.IsGradedExtInternallyFinite`: finite-dimensionality and finite internal support in
  each cohomological degree.
* `TauCeti.IsGradedExtBoundedBy` and `TauCeti.IsGradedExtBounded`: a uniform cohomological
  vanishing bound across all internal degrees.
* `TauCeti.IsGradedEulerAdmissible`: the two support conditions together.
* `TauCeti.IsGradedEulerAdmissibleOn`: every pair in two object properties is graded
  Euler-admissible.
* `TauCeti.gradedExtDimension`: the target-shift graded dimension in one cohomological degree.
* `TauCeti.gradedExtEuler`: the q-Euler characteristic of an admissible pair.

## Main results

* `TauCeti.IsGradedEulerAdmissible.isEulerAdmissible`: a graded Euler-admissible pair is
  ordinarily Euler-admissible against every fixed target shift.
* `TauCeti.IsGradedEulerAdmissible.of_shortExact₂` and
  `TauCeti.IsGradedEulerAdmissible.of_shortExact₂'`: graded Euler-admissibility is closed under
  extensions in the second and the first variable.
* `TauCeti.gradedExtEuler_of_iso`: the q-Euler characteristic depends only on the isomorphism
  classes of the two objects.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for the bigraded Ext-Euler form and
  its q-antilinear/q-linear shift convention.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layers 5--6, "Graded Ext and graded descent"
  and "q-Euler form".
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]
  (k : Type t) [Field k] [Linear k C] [HasExt.{w} C]
  (e : C ≌ C)

/-- The **bigraded Ext group** `Ext^{n,j}(X,Y) = Ext^n(X,Y{j})`, where `{j}` is the `j`-fold
power of the chosen grading-shift autoequivalence. -/
abbrev GradedExt (X Y : C) (n : ℕ) (j : ℤ) : Type w :=
  Ext.{w} X ((e ^ j).functor.obj Y) n

/-- The internal grading of `Ext` is finite in each cohomological degree: every
`Ext^{n,j}(X,Y)` is finite-dimensional and, for fixed `n`, only finitely many internal degrees
are nonzero.  This says nothing about how many cohomological degrees survive. -/
structure IsGradedExtInternallyFinite (X Y : C) : Prop where
  /-- Each fixed cohomological degree has finite Laurent support in the internal grading. -/
  finiteLaurentSupport (n : ℕ) : HasFiniteLaurentSupport k (GradedExt.{w} e X Y n)

/-- The bigraded Ext groups vanish in every internal degree from cohomological degree `N` on. -/
structure IsGradedExtBoundedBy (X Y : C) (N : ℕ) : Prop where
  /-- Every internal-degree piece vanishes above the cohomological bound. -/
  subsingleton ⦃n : ℕ⦄ (hn : N ≤ n) (j : ℤ) : Subsingleton (GradedExt.{w} e X Y n j)

/-- The bigraded Ext groups vanish in every internal degree for all sufficiently large
cohomological degrees.  The bound is uniform in the internal degree. -/
structure IsGradedExtBounded (X Y : C) : Prop where
  /-- Some natural number uniformly bounds the cohomological support. -/
  exists_bound : ∃ N, IsGradedExtBoundedBy.{w} e X Y N

/-- A pair is **graded Euler-admissible** when its internal support is finite in each
cohomological degree and its cohomological support has a uniform finite bound.  The construction
of its Laurent-polynomial-valued Ext-Euler characteristic uses these two conditions. -/
structure IsGradedEulerAdmissible (X Y : C) : Prop where
  /-- Finite-dimensionality and finite internal support in every cohomological degree. -/
  internallyFinite : IsGradedExtInternallyFinite.{w} k e X Y
  /-- Uniform eventual vanishing in the cohomological degree. -/
  bounded : IsGradedExtBounded.{w} e X Y

namespace IsGradedExtBoundedBy

variable {e}

/-- A cohomological vanishing bound may always be raised. -/
theorem mono {X Y : C} {N M : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) (hNM : N ≤ M) :
    IsGradedExtBoundedBy.{w} e X Y M :=
  ⟨fun {_n} hn j ↦ h.subsingleton (hNM.trans hn) j⟩

/-- An explicit cohomological bound witnesses eventual graded Ext-vanishing. -/
theorem isGradedExtBounded {X Y : C} {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) :
    IsGradedExtBounded.{w} e X Y :=
  ⟨N, h⟩

end IsGradedExtBoundedBy

/-! ### Admissibility on object properties -/

section Admissibility

variable {k} {e}

/-- Every pair of objects in `P × Q` is graded Euler-admissible.  The internal-support and
cohomological bounds may depend on the pair. -/
structure IsGradedEulerAdmissibleOn (P Q : ObjectProperty C) : Prop where
  /-- Each pair drawn from `P` and `Q` is graded Euler-admissible. -/
  isGradedEulerAdmissible ⦃X Y : C⦄ (hX : P X) (hY : Q Y) :
    IsGradedEulerAdmissible.{w} k e X Y

/-! ### Passage to one internal degree -/

/-- A uniform graded Ext bound gives the same ordinary Ext bound against every fixed target
shift. -/
theorem IsGradedExtBoundedBy.isExtBoundedBy {X Y : C} {N : ℕ}
    (h : IsGradedExtBoundedBy.{w} e X Y N) (j : ℤ) :
    IsExtBoundedBy.{w} X ((e ^ j).functor.obj Y) N :=
  ⟨fun _ hn ↦ h.subsingleton hn j⟩

/-! ### Closure under extensions -/

variable {S : ShortComplex C}

/-- A uniform graded Ext bound is closed under extensions in the second variable. -/
theorem IsGradedExtBoundedBy.of_shortExact₂ (hS : S.ShortExact) {X : C} {N₁ N₃ : ℕ}
    (h₁ : IsGradedExtBoundedBy.{w} e X S.X₁ N₁)
    (h₃ : IsGradedExtBoundedBy.{w} e X S.X₃ N₃) :
    IsGradedExtBoundedBy.{w} e X S.X₂ (max N₁ N₃) :=
  ⟨fun _n hn j ↦
    ((h₁.isExtBoundedBy j).of_shortExact₂ (hS.map_of_exact (e ^ j).functor)
      (h₃.isExtBoundedBy j)).subsingleton hn⟩

/-- A uniform graded Ext bound is closed under extensions in the first variable. -/
theorem IsGradedExtBoundedBy.of_shortExact₂' (hS : S.ShortExact) {Y : C} {N₁ N₃ : ℕ}
    (h₁ : IsGradedExtBoundedBy.{w} e S.X₁ Y N₁)
    (h₃ : IsGradedExtBoundedBy.{w} e S.X₃ Y N₃) :
    IsGradedExtBoundedBy.{w} e S.X₂ Y (max N₁ N₃) :=
  ⟨fun _n hn j ↦
    ((h₁.isExtBoundedBy j).of_shortExact₂' hS
      (h₃.isExtBoundedBy j)).subsingleton hn⟩

end Admissibility

/-! ### The q-Euler value -/

/-- The Laurent polynomial
`∑ j, q⁻ʲ dim_k Ext^{n,j}(X,Y)` in one cohomological degree. -/
noncomputable def gradedExtDimension {X Y : C}
    {n : ℕ} (h : HasFiniteLaurentSupport k (GradedExt.{w} e X Y n)) : LaurentPolynomial ℤ :=
  targetShiftGradedDimension k (GradedExt.{w} e X Y n) h

/-- The coefficient of `q^j` in the graded Ext dimension is
`dim_k Ext^{n,-j}(X,Y)`. -/
@[simp]
theorem coeff_gradedExtDimension {X Y : C}
    {n : ℕ} (h : HasFiniteLaurentSupport k (GradedExt.{w} e X Y n)) (j : ℤ) :
    (gradedExtDimension k e h).coeff j =
      Module.finrank k (GradedExt.{w} e X Y n (-j)) :=
  coeff_targetShiftGradedDimension h j

/-- The q-Euler sum truncated to cohomological degrees below `N`.  The internal sum in every
term is genuine because `h` supplies finite Laurent support. -/
noncomputable def truncatedGradedExtEuler {X Y : C}
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (N : ℕ) : LaurentPolynomial ℤ :=
  ∑ n ∈ Finset.range N,
    ((-1 : ℤ) ^ n) • gradedExtDimension k e (h.finiteLaurentSupport n)

/-- The empty truncation of the graded Ext-Euler sum is zero. -/
@[simp]
theorem truncatedGradedExtEuler_zero {X Y : C}
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    truncatedGradedExtEuler k e h 0 = 0 :=
  Finset.sum_empty

/-- Raising the truncation bound by one adds the signed graded dimension in the new degree. -/
@[simp]
theorem truncatedGradedExtEuler_succ {X Y : C}
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (N : ℕ) :
    truncatedGradedExtEuler k e h (N + 1) =
      truncatedGradedExtEuler k e h N +
        ((-1 : ℤ) ^ N) • gradedExtDimension k e (h.finiteLaurentSupport N) :=
  Finset.sum_range_succ _ N

/-- The **graded Ext-Euler characteristic**
`χ_q(X,Y) = ∑ n,j (-1)^n q⁻ʲ dim_k Ext^{n,j}(X,Y)` of a graded Euler-admissible pair. -/
noncomputable def gradedExtEuler {X Y : C} (h : IsGradedEulerAdmissible.{w} k e X Y) :
    LaurentPolynomial ℤ :=
  truncatedGradedExtEuler k e h.internallyFinite h.bounded.exists_bound.choose

/-! ### Isomorphism invariance -/

variable {e} {X X' Y Y' : C}

/-- A cohomological vanishing bound for bigraded Ext depends only on the isomorphism classes of
the two objects. -/
theorem IsGradedExtBoundedBy.of_iso {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N)
    (i : X ≅ X') (j : Y ≅ Y') : IsGradedExtBoundedBy.{w} e X' Y' N :=
  ⟨fun n hn d ↦ haveI := h.subsingleton hn d
    (extAddEquivOfIso i ((e ^ d).functor.mapIso j) n).symm.toEquiv.subsingleton⟩

/-- Eventual cohomological vanishing of bigraded Ext depends only on the isomorphism classes of
the two objects. -/
theorem IsGradedExtBounded.of_iso (h : IsGradedExtBounded.{w} e X Y)
    (i : X ≅ X') (j : Y ≅ Y') : IsGradedExtBounded.{w} e X' Y' :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.of_iso i j⟩

end TauCeti
