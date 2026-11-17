/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ZeroCounting.ZetaZeros

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rectangle geometry for the zeta argument principle

This file supplies the geometric part of the direct Backlund--Turing route.
It proves that safe horizontal contour heights exist and that a rectangle
which contains the critical strip horizontally, has positive lower height,
and has safe horizontal sides is admissible for a zeta argument-principle
calculation.

No contour integral or zero-count formula is postulated here.  In particular,
the existence of safe heights follows only from Mathlib's local finiteness of
the actual nontrivial zeta-zero set.
-/

open Set

namespace OverflowResidueRH

/-- A closed axis-parallel rectangle in the complex plane.-/
structure ZetaRectangle where
  left : Real
  right : Real
  bottom : Real
  top : Real
  left_lt_right : left < right
  bottom_lt_top : bottom < top

namespace ZetaRectangle

/-- Membership in the closed rectangle.-/
def ContainsClosed (R : ZetaRectangle) (s : Complex) : Prop :=
  R.left <= s.re ∧ s.re <= R.right ∧
    R.bottom <= s.im ∧ s.im <= R.top

/-- Membership in the open rectangle.-/
def ContainsOpen (R : ZetaRectangle) (s : Complex) : Prop :=
  R.left < s.re ∧ s.re < R.right ∧
    R.bottom < s.im ∧ s.im < R.top

/-- Membership in the topological boundary, expressed without importing a
separate rectangle topology API.-/
def ContainsBoundary (R : ZetaRectangle) (s : Complex) : Prop :=
  R.ContainsClosed s ∧ ¬ R.ContainsOpen s

/-- A height is safe for the horizontal part of a zeta contour when no actual
Mathlib-nontrivial zeta zero has that imaginary part.-/
def ZetaGoodHeight (T : Real) : Prop :=
  ∀ s : Complex, IsMathlibNontrivialZetaZero s → s.im ≠ T

/-- The set of actual positive zeta-zero heights up to `B` is finite.-/
theorem zetaZeroHeightSetUpTo_finite (B : Real) :
    (Complex.im '' zetaNontrivialZerosUpToHeightSet B).Finite :=
  (zetaNontrivialZerosUpToHeightSet_finite B).image Complex.im

/-- Every nonempty positive real interval contains a safe zeta contour
height.  This is the exact avoidance lemma needed before applying a rectangle
argument principle.-/
theorem exists_zetaGoodHeight_between
    {A B : Real} (hA : 0 < A) (hAB : A < B) :
    ∃ T : Real, A < T ∧ T < B ∧ ZetaGoodHeight T := by
  let H : Set Real := Complex.im '' zetaNontrivialZerosUpToHeightSet B
  have hH : H.Finite := zetaZeroHeightSetUpTo_finite B
  have hdiff : (Set.Ioo A B \ H).Infinite :=
    (Set.Ioo_infinite hAB).sdiff hH
  obtain ⟨T, hT, hTnot⟩ := hdiff.nonempty
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro s hs hsT
  apply hTnot
  refine ⟨s, ?_, hsT⟩
  refine ⟨hs, ?_, ?_⟩
  · rw [hsT]
    exact lt_trans hA hT.1
  · rw [hsT]
    exact hT.2.le

/-- A bundled safe height inside an open interval.-/
structure SafeContourHeight (A B : Real) where
  height : Real
  left_lt : A < height
  lt_right : height < B
  good : ZetaGoodHeight height

/-- Safe horizontal zeta-contour heights exist in every positive open
interval.-/
theorem safeContourHeight_nonempty
    {A B : Real} (hA : 0 < A) (hAB : A < B) :
    Nonempty (SafeContourHeight A B) := by
  obtain ⟨T, hAT, hTB, hgood⟩ := exists_zetaGoodHeight_between hA hAB
  exact ⟨⟨T, hAT, hTB, hgood⟩⟩

/-- The fixed-width rectangle `[-1,2] × [A,T]` used to state a concrete
positive-height argument-principle obligation.-/
def standard (A T : Real) (hAT : A < T) : ZetaRectangle where
  left := -1
  right := 2
  bottom := A
  top := T
  left_lt_right := by norm_num
  bottom_lt_top := hAT

@[simp] theorem standard_left (A T : Real) (hAT : A < T) :
    (standard A T hAT).left = -1 := rfl

@[simp] theorem standard_right (A T : Real) (hAT : A < T) :
    (standard A T hAT).right = 2 := rfl

@[simp] theorem standard_bottom (A T : Real) (hAT : A < T) :
    (standard A T hAT).bottom = A := rfl

@[simp] theorem standard_top (A T : Real) (hAT : A < T) :
    (standard A T hAT).top = T := rfl

/-- No actual nontrivial zeta zero lies on the rectangle boundary.-/
def NoZerosOnBoundary (R : ZetaRectangle) : Prop :=
  ∀ s : Complex,
    IsMathlibNontrivialZetaZero s → R.ContainsBoundary s → False

/-- The unique zeta pole at `1` is not on the rectangle boundary.-/
def PoleNotOnBoundary (R : ZetaRectangle) : Prop :=
  ¬ R.ContainsBoundary (1 : Complex)

/-- The geometric admissibility conditions needed by a zeta
argument-principle theorem.-/
structure AdmissibleForZeta (R : ZetaRectangle) : Prop where
  noZerosOnBoundary : R.NoZerosOnBoundary
  poleNotOnBoundary : R.PoleNotOnBoundary

/-- A rectangle which contains the critical strip horizontally, lies above
the real axis, and has good horizontal heights has no zeta zero or pole on
its boundary.  Thus the geometric part of the argument-principle route is
unconditional.-/
theorem admissibleForZeta_of_wide_positive_good
    {R : ZetaRectangle}
    (hleft : R.left < 0)
    (hright : 1 < R.right)
    (hbottom : 0 < R.bottom)
    (hbottomGood : ZetaGoodHeight R.bottom)
    (htopGood : ZetaGoodHeight R.top) :
    R.AdmissibleForZeta where
  noZerosOnBoundary := by
    intro s hs hboundary
    rcases hboundary with ⟨hclosed, hnotOpen⟩
    have hxi : entireRiemannXi s = 0 :=
      entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs
    have hstrip : s.re ∈ Set.Ioo (0 : Real) 1 :=
      entireRiemannXi_zero_re_mem_Ioo hxi
    have hreLeft : R.left < s.re := lt_trans hleft hstrip.1
    have hreRight : s.re < R.right := lt_trans hstrip.2 hright
    have himBottom : R.bottom < s.im :=
      lt_of_le_of_ne hclosed.2.2.1 (Ne.symm (hbottomGood s hs))
    have himTop : s.im < R.top :=
      lt_of_le_of_ne hclosed.2.2.2 (htopGood s hs)
    exact hnotOpen ⟨hreLeft, hreRight, himBottom, himTop⟩
  poleNotOnBoundary := by
    intro hboundary
    have him := hboundary.1.2.2.1
    norm_num at him
    linarith

/-- The standard rectangle is admissible whenever its two horizontal
heights are positive/safe.-/
theorem standard_admissibleForZeta
    {A T : Real} (hA : 0 < A) (hAT : A < T)
    (hAgood : ZetaGoodHeight A) (hTgood : ZetaGoodHeight T) :
    (standard A T hAT).AdmissibleForZeta := by
  apply admissibleForZeta_of_wide_positive_good
  · norm_num
  · norm_num
  · exact hA
  · exact hAgood
  · exact hTgood

/-- Every point of a positive-height closed rectangle is a regular point of
`riemannZeta`; the only exceptional point for Mathlib's differentiability
theorem is `1`, whose imaginary part is zero.-/
theorem differentiableAt_riemannZeta_of_containsClosed_bottom_pos
    {R : ZetaRectangle} (hbottom : 0 < R.bottom)
    {s : Complex} (hs : R.ContainsClosed s) :
    DifferentiableAt Complex riemannZeta s := by
  apply differentiableAt_riemannZeta
  intro hs1
  subst s
  have him := hs.2.2.1
  norm_num at him
  linarith

/-- On an admissible positive-height rectangle, zeta is nonzero at every
boundary point.  The admissibility field excludes nontrivial zeros; positive
height separately excludes both the negative-even trivial zeros and `1`.-/
theorem riemannZeta_ne_zero_of_admissible_on_boundary
    {R : ZetaRectangle} (H : R.AdmissibleForZeta)
    (hbottom : 0 < R.bottom) {s : Complex}
    (hs : R.ContainsBoundary s) :
    riemannZeta s ≠ 0 := by
  intro hz
  have himpos : 0 < s.im := lt_of_lt_of_le hbottom hs.1.2.2.1
  apply H.noZerosOnBoundary s ?_ hs
  refine ⟨hz, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    norm_num at himpos
  · intro hs1
    subst s
    norm_num at himpos

end ZetaRectangle

end OverflowResidueRH
