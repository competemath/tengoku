/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Families.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scheme realizations of weak-stability family probes

The neutral scheme-indexed triangulated family lives under
`AlgebraicGeometry/DerivedCategory/Families/`. This file adds only the
geometric realizations of weak-stability topological probes on the underlying
Zariski space of an actual scheme. The declarations keep the namespace of the
probe structures they extend so that dot notation such as
`ChargeProbe.ofScheme` resolves; the file lives with the scheme because that
is the object it is about.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u v

/-- A charge probe on the underlying Zariski space of an actual scheme.-/
def ChargeProbe.ofScheme (X : Scheme.{u}) {A : Type v} (value : X → A) :
    ChargeProbe A where
  Point := X
  topology := inferInstance
  value := value

/--
@isnad1 id=iff.0h3v.s5.521829dd7418 from=translated src=- shape=fbdcd0c8 vocab=d7db008d
-/
@[simp]
theorem ChargeProbe.ofScheme_isLocallyConstant_iff
    (X : Scheme.{u}) {A : Type v} (value : X → A) :
    (ChargeProbe.ofScheme X value).IsLocallyConstant ↔
      _root_.IsLocallyConstant value :=
  Iff.rfl

/-- An openness probe on the underlying Zariski space of an actual scheme.-/
def OpenLocusProbe.ofScheme (X : Scheme.{u}) (locus : Set X) :
    OpenLocusProbe where
  Point := X
  topology := inferInstance
  locus := locus

/--
@isnad1 id=iff.0h2v.s5.eb2d739e7939 from=translated src=- shape=5c367e32 vocab=95d8f061
-/
@[simp]
theorem OpenLocusProbe.ofScheme_isOpen_iff
    (X : Scheme.{u}) (locus : Set X) :
    (OpenLocusProbe.ofScheme X locus).IsOpen ↔ _root_.IsOpen locus :=
  Iff.rfl

/-- A generic-semistability probe on the underlying Zariski space of an
actual scheme.-/
def GenericSemistabilityProbe.ofScheme
    (X : Scheme.{u}) (genericPoint : X) (semistableLocus : Set X) :
    GenericSemistabilityProbe where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  semistableLocus := semistableLocus

/--
@isnad1 id=iff.0h3v.s7.72461fb0a66b from=translated src=- shape=ad290dec vocab=24b82552
-/
@[simp]
theorem GenericSemistabilityProbe.ofScheme_isGenericallyOpen_iff
    (X : Scheme.{u}) (genericPoint : X) (semistableLocus : Set X) :
    (GenericSemistabilityProbe.ofScheme X genericPoint
      semistableLocus).IsGenericallyOpen ↔
      genericPoint ∈ semistableLocus →
        ∃ U : Set X, _root_.IsOpen U ∧ genericPoint ∈ U ∧ U ⊆ semistableLocus :=
  Iff.rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.Families
