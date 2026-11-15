import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliPackageAbs (A : Type u) [CommRing A] (D : LevelModuliDatum.{u} A) where

  B₀ : Type u

  [instCommRing : CommRing B₀]

  [instAlgebra : Algebra A B₀]

  univ : D.Pt B₀

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : B₀ →ₐ[A] T, D.map φ univ = x

attribute [instance] LevelModuliPackageAbs.instCommRing LevelModuliPackageAbs.instAlgebra

namespace LevelModuliPackageAbs

variable {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)

def j₀ : P.B₀ := D.jOf P.univ

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : P.B₀ →ₐ[A] T :=
  (P.represents T x).choose

/--
@isnad1 id=eq.0h5v.s6.47d4f414341d from=translated src=- shape=73f2752d vocab=58972799
-/
theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1

/--
@isnad1 id=eq.1h6v.s7.0f3f740f77e0 from=translated src=- shape=1fdc36d1 vocab=1ad8b59f
-/
theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : P.B₀ →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl

end LevelModuliPackageAbs

end ModularCurve
