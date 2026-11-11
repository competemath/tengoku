/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the algebraic part of Clawristotle's
`CoherentCohomologyFinite.SegreCoordinatePresentation`.
-/
import Tengoku.Aintlib.ModularCurves.ForMathlib.SegreDiagonalSurjectivity
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coordinate presentation of the Segre image

The standard coordinates of the target projective space are reindexed by pairs.
The homogeneous coordinate ring of the image is the range of the resulting map.
-/

open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

/-- The dimension of the target of `ℙ^m × ℙ^n ↪ ℙ^(mn+m+n)`.-/
def segreDimension (m n : ℕ) : ℕ :=
  m * n + m + n

/--
@isnad1 id=eq.0h2v.s5.119253d03144 from=translated src=- shape=e7f9466e vocab=f16e4ca3
-/
lemma segreDimension_succ (m n : ℕ) :
    segreDimension m n + 1 = (m + 1) * (n + 1) := by
  simp only [segreDimension]
  ring

/-- Reindex the target coordinates by pairs of coordinates of the two factors.-/
def segreIndexEquiv (m n : ℕ) :
    Fin (segreDimension m n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
  (finCongr (segreDimension_succ m n)).trans finProdFinEquiv.symm

/-- The Segre coordinate map with standard target coordinates.-/
def segreStandardCoordinateHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) R →ₐ[R]
      MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R :=
  (segreCoordinateHom R m n).comp
    (MvPolynomial.renameEquiv R (segreIndexEquiv m n)).toAlgHom

/--
@isnad1 id=eq.0h4v.s11.b6f166f85a96 from=translated src=- shape=fb669597 vocab=884f671f
-/
@[simp]
lemma segreStandardCoordinateHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (segreDimension m n + 1)) :
    segreStandardCoordinateHom R m n (X i) =
      X (segreIndexEquiv m n i).1 ⊗ₜ[R] X (segreIndexEquiv m n i).2 := by
  change segreCoordinateHom R m n
    (rename (segreIndexEquiv m n) (X i)) = _
  rw [rename_X, segreCoordinateHom_X]

/-- The homogeneous coordinate ring of the Segre image.-/
abbrev SegreCoordinateRing
    (R : Type u) [CommRing R] (m n : ℕ) :=
  (segreStandardCoordinateHom R m n).range

/-- The coordinate map with codomain restricted to its image.-/
abbrev segreRangeCoordinateHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) R →ₐ[R]
      SegreCoordinateRing R m n :=
  (segreStandardCoordinateHom R m n).rangeRestrict

/--
@isnad1 id=surjecti.0h3v.s13.45586e812f1a from=translated src=- shape=15f7daba vocab=66abd3a5
-/
lemma segreRangeCoordinateHom_surjective
    (R : Type u) [CommRing R] (m n : ℕ) :
    Function.Surjective (segreRangeCoordinateHom R m n) :=
  AlgHom.rangeRestrict_surjective _

/--
@isnad1 id=eq.0h4v.s13.4c69bcb35888 from=translated src=- shape=83d1a750 vocab=84137032
-/
@[simp]
lemma segreRangeCoordinateHom_val
    (R : Type u) [CommRing R] (m n : ℕ)
    (p : MvPolynomial (Fin (segreDimension m n + 1)) R) :
    ((segreRangeCoordinateHom R m n p : SegreCoordinateRing R m n) :
      MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R) =
        segreStandardCoordinateHom R m n p :=
  rfl

end MvPolynomial
