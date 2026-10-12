/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic
public import Tengoku.Tauceti.TauCeti.Algebra.Homology.Ext.Equivalence
public import Tengoku.Tauceti.TauCeti.CategoryTheory.Equivalence.Pow

/-!
# The shift identities of the graded Ext-Euler characteristic

Let `C` be a `k`-linear abelian category with a grading shift `e : C ≌ C`, written `{1}`.  The
q-Euler characteristic `χ_q(X, Y) = ∑ n,j (-1)^n q⁻ʲ dim_k Ext^n(X, Y{j})` of
`TauCeti.gradedExtEuler` is q-linear in its second argument and q-antilinear in its first:

```text
χ_q(X, Y{1}) = q · χ_q(X, Y),        χ_q(X{1}, Y) = q⁻¹ · χ_q(X, Y).
```

These are the generating identities behind the sesquilinearity of the q-Euler form, and they fix
the handedness of the internal grading.

Both identities come from a reindexing of the internal degree.  Shifting the target by one
identifies `Ext^{n,j}(X, Y{1})` with `Ext^{n,j+1}(X, Y)`, which multiplies the target-shift graded
dimension by `q`; shifting the source instead identifies `Ext^{n,j}(X{1}, Y)` with
`Ext^{n,j-1}(X, Y)` and multiplies it by `q⁻¹`.  The source identity uses that `Ext` is invariant
under the equivalence `e`, so it needs `e` to be `k`-linear and not merely additive: an additive
isomorphism of `k`-vector spaces need not preserve dimension.  The comparison of `e ^ (j + 1)`
with the composites `e ^ j ∘ e` and `e ∘ e ^ j` is
`CategoryTheory.Equivalence.powSuccIso` and `CategoryTheory.Equivalence.powSuccRightIso`.

Every identity below takes a single admissibility witness, for the unshifted pair: the shifted
witness it needs is the one this file constructs from it.

## Main definitions

* `TauCeti.shiftSourceObjIso`: the comparison `(Y{j-1}){1} ≅ Y{j}` through which a source shift
  is moved into the internal degree.
* `TauCeti.gradedExtShiftTargetEquiv`: `Ext^{n,j}(X, Y{1}) ≃ₗ[k] Ext^{n,j+1}(X, Y)`.
* `TauCeti.gradedExtShiftTargetInverseEquiv`: `Ext^{n,j}(X, Y{-1}) ≃ₗ[k] Ext^{n,j-1}(X, Y)`.
* `TauCeti.gradedExtShiftSourceEquiv`: `Ext^{n,j}(X{1}, Y) ≃ₗ[k] Ext^{n,j-1}(X, Y)`.
* `TauCeti.gradedExtShiftSourceInverseEquiv`: `Ext^{n,j}(X{-1}, Y) ≃ₗ[k] Ext^{n,j+1}(X, Y)`.

## Main results

* `TauCeti.IsGradedEulerAdmissible.shiftTarget` and
  `TauCeti.IsGradedEulerAdmissible.shiftSource`: graded Euler-admissibility is preserved by the
  grading shift in either variable; `TauCeti.IsGradedEulerAdmissible.shiftTargetInverse` and
  `TauCeti.IsGradedEulerAdmissible.shiftSourceInverse` are the same for the inverse shift.
* `TauCeti.gradedExtEuler_shiftTarget`: `χ_q(X, Y{1}) = q · χ_q(X, Y)`.
* `TauCeti.gradedExtEuler_shiftSource`: `χ_q(X{1}, Y) = q⁻¹ · χ_q(X, Y)`.
* `TauCeti.gradedExtEuler_shiftTargetInverse` and
  `TauCeti.gradedExtEuler_shiftSourceInverse`: the two identities for the inverse shift `{-1}`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Sections 1.2 and 2.2, for the q-antilinear/q-linear
  convention of the q-Euler form.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (k : Type t) (e : C ≌ C)

/-! ### Shifting the target

Nothing in this section needs the shift to be additive or linear: the reindexing is induced by an
isomorphism of objects.  The two reindexing equivalences need only a commutative ring of scalars;
`k` is a field only from the point where dimensions are taken. -/

section CommRing

variable [CommRing k] [Linear k C]

/-- Shifting the target of a bigraded `Ext` group raises its internal degree by one:
`Ext^{n,j}(X, Y{1}) ≅ Ext^{n,j+1}(X, Y)`. -/
noncomputable def gradedExtShiftTargetEquiv (X Y : C) (n : ℕ) (j : ℤ) :
    GradedExt.{w} e X (e.functor.obj Y) n j ≃ₗ[k] GradedExt.{w} e X Y n (j + 1) :=
  extLinearEquivOfIso k (Iso.refl X) ((e.powSuccIso j).app Y).symm n

/-- `TauCeti.gradedExtShiftTargetEquiv` composes with the comparison isomorphism
`(Y{1}){j} ≅ Y{j+1}`. -/
@[simp]
theorem gradedExtShiftTargetEquiv_apply (X Y : C) (n : ℕ) (j : ℤ)
    (x : GradedExt.{w} e X (e.functor.obj Y) n j) :
    gradedExtShiftTargetEquiv k e X Y n j x =
      x.comp (Ext.mk₀ ((e.powSuccIso j).app Y).inv) (add_zero n) := by
  simp [gradedExtShiftTargetEquiv]

/-- Shifting the target by the inverse shift lowers the internal degree by one:
`Ext^{n,j}(X, Y{-1}) ≅ Ext^{n,j-1}(X, Y)`. -/
noncomputable def gradedExtShiftTargetInverseEquiv (X Y : C) (n : ℕ) (j : ℤ) :
    GradedExt.{w} e X (e.inverse.obj Y) n j ≃ₗ[k] GradedExt.{w} e X Y n (j - 1) :=
  extLinearEquivOfIso k (Iso.refl X) ((e.powPredIso j).app Y) n

/-- `TauCeti.gradedExtShiftTargetInverseEquiv` composes with the comparison isomorphism
`(Y{-1}){j} ≅ Y{j-1}`. -/
@[simp]
theorem gradedExtShiftTargetInverseEquiv_apply (X Y : C) (n : ℕ) (j : ℤ)
    (x : GradedExt.{w} e X (e.inverse.obj Y) n j) :
    gradedExtShiftTargetInverseEquiv k e X Y n j x =
      x.comp (Ext.mk₀ ((e.powPredIso j).app Y).hom) (add_zero n) := by
  simp [gradedExtShiftTargetInverseEquiv]

end CommRing

section Field

variable [Field k] [Linear k C]
variable {k e}
variable {X Y : C}

/-- A cohomological vanishing bound is preserved by shifting the target. -/
theorem IsGradedExtBoundedBy.shiftTarget {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) :
    IsGradedExtBoundedBy.{w} e X (e.functor.obj Y) N :=
  ⟨fun n hn j => have := h.subsingleton hn (j + 1)
    (extAddEquivOfIso (Iso.refl X) ((e.powSuccIso j).app Y).symm n).toEquiv.subsingleton⟩

/-- A cohomological vanishing bound is preserved by the inverse shift of the target. -/
theorem IsGradedExtBoundedBy.shiftTargetInverse {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) :
    IsGradedExtBoundedBy.{w} e X (e.inverse.obj Y) N :=
  ⟨fun n hn j => have := h.subsingleton hn (j - 1)
    (extAddEquivOfIso (Iso.refl X) ((e.powPredIso j).app Y) n).toEquiv.subsingleton⟩

/-- Eventual cohomological vanishing of bigraded `Ext` is preserved by shifting the target. -/
theorem IsGradedExtBounded.shiftTarget (h : IsGradedExtBounded.{w} e X Y) :
    IsGradedExtBounded.{w} e X (e.functor.obj Y) :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.shiftTarget⟩

/-- Eventual cohomological vanishing of bigraded `Ext` is preserved by the inverse shift of the
target. -/
theorem IsGradedExtBounded.shiftTargetInverse (h : IsGradedExtBounded.{w} e X Y) :
    IsGradedExtBounded.{w} e X (e.inverse.obj Y) :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.shiftTargetInverse⟩

end Field

/-! ### Shifting the source

The source identity uses that `Ext` is invariant under `e`, so `e` must be `k`-linear and not
merely additive.  As for the target, the two reindexing equivalences need only a commutative ring
of scalars. -/

/-- The comparison `(Y{j-1}){1} ≅ Y{j}`, which moves a source shift into the internal degree. -/
noncomputable def shiftSourceObjIso (Y : C) (j : ℤ) :
    e.functor.obj ((e ^ (j - 1)).functor.obj Y) ≅ (e ^ j).functor.obj Y :=
  ((e.powSuccRightIso (j - 1)).app Y).symm ≪≫
    eqToIso (congrArg (fun i : ℤ => (e ^ i).functor.obj Y) (by ring : j - 1 + 1 = j))

section CommRingSource

variable [CommRing k] [Linear k C] [e.functor.Additive] [e.functor.Linear k]

end CommRingSource

section FieldSource

variable [Field k] [Linear k C] [e.functor.Additive] [e.functor.Linear k]
variable {k e}
variable {X Y : C}

end FieldSource

end TauCeti
