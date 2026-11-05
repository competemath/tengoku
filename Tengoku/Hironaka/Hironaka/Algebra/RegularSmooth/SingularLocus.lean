/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Defs
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
public import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Basic
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Regular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The singular locus and its ideal sheaf

Consequences of the comparison of regular and smooth points for `X` locally of finite type over a
perfect field `k`: the singular locus `Sing X` is the complement of the smooth locus of
`X → Spec k` (`Hironaka/Algebra/RegularSmooth/RegularSmoothEquiv.lean`), hence closed (Mathlib's
`Scheme.Hom.isOpen_smoothLocus`; [Sta, Tag 00TT]); the regular locus is dense when `X` is reduced
and contains the generic point when `X` is integral (Mathlib's `dense_smoothLocus_of_perfectField`,
`genericPoint_mem_smoothLocus_of_perfectField`); and the ideal sheaf `𝒥` of `Sing X` with its
reduced structure is the vanishing ideal sheaf of `Sing X` (`Scheme.singIdeal`). The main
theorems (`Challenge/Algebraic.lean`) state Main Theorem I with `Sing X`.

`Sing X` need not be closed for an arbitrary scheme, and Mathlib's `IdealSheafData.vanishingIdeal`
takes a closed set; since the vanishing ideal of a set is that of its closure, `singIdeal X` is
defined for every scheme as the vanishing ideal sheaf of `closure (Sing X)`, and under the
hypotheses above its support is exactly `Sing X` (`coe_support_singIdeal_eq_singularLocus`). It is a
radical ideal sheaf (the reduced induced structure), and it is the unit ideal iff `X` is regular.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The ideal sheaf `𝒥` of the singular locus with its reduced structure: the vanishing ideal
sheaf of `closure (Sing X)`, whose support is `Sing X` itself when the latter is closed. It is a
factor of the single centre `D` with `|D| = Sing X` in
`Hironaka/Resolution/Algebraic/Hir64/SingleCenter.lean`.-/
noncomputable def singIdeal (X : Scheme.{u}) : X.IdealSheafData :=
  IdealSheafData.vanishingIdeal ⟨closure X.singularLocus, isClosed_closure⟩

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The defining equation of `singIdeal X`.-/
theorem singIdeal_eq_vanishingIdeal_closure_singularLocus (X : Scheme.{u}) :
    X.singIdeal = IdealSheafData.vanishingIdeal ⟨closure X.singularLocus, isClosed_closure⟩ :=
  rfl

/-- The support of `singIdeal X` is the closure of `Sing X`.-/
theorem coe_support_singIdeal (X : Scheme.{u}) :
    (X.singIdeal.support : Set X) = closure X.singularLocus :=
  rfl

/-- `singIdeal X` is a radical ideal sheaf (the reduced structure on the singular locus): the
vanishing ideal sheaf of the support of any ideal sheaf is its radical (Mathlib's
`vanishingIdeal_support`), and the support of `singIdeal X` is the closed set it vanishes on.-/
theorem radical_singIdeal (X : Scheme.{u}) : X.singIdeal.radical = X.singIdeal := by
  rw [← IdealSheafData.vanishingIdeal_support]
  rfl

/-- `singIdeal X` is the unit ideal sheaf iff `X` is regular (the singular locus is empty).-/
theorem singIdeal_eq_top_iff_isRegular (X : Scheme.{u}) : X.singIdeal = ⊤ ↔ IsRegular X := by
  rw [isRegular_iff_singularLocus_eq_empty]
  constructor
  · intro h
    have hsupp := congrArg (fun I : X.IdealSheafData => (I.support : Set X)) h
    simp only [coe_support_singIdeal, IdealSheafData.support_top, Closeds.coe_bot] at hsupp
    exact Set.eq_empty_of_subset_empty (hsupp ▸ subset_closure)
  · intro h
    have hZ : (⟨closure X.singularLocus, isClosed_closure⟩ : Closeds X) = ⊥ := by
      apply Closeds.ext
      rw [Closeds.coe_mk, h, closure_empty, Closeds.coe_bot]
    rw [singIdeal_eq_vanishingIdeal_closure_singularLocus, hZ]
    exact IdealSheafData.vanishingIdeal_bot

end AlgebraicGeometry.Scheme
