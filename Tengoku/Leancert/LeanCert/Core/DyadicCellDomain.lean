/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Core.CertifiedCellDomain
import Tengoku.Leancert.LeanCert.Core.IntervalDyadic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Certified dyadic interval subdivision

Exact midpoint bisection supplies the first `CertifiedCellDomain` instance.
Both children are closed: their shared midpoint seam is deliberately retained.
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Core

namespace IntervalDyadic

/-- The two exact closed halves used by generic certified subdivision. -/
def certifiedChildren (I : IntervalDyadic) : List IntervalDyadic :=
  [I.bisect.1, I.bisect.2]

instance : CertifiedCellDomain IntervalDyadic ℝ where
  children := certifiedChildren
  contains I x := x ∈ I
  diameter I := I.width.toRat
  childSubset := by
    intro parent child x hchild hx
    simp only [certifiedChildren, List.mem_cons, List.not_mem_nil, or_false] at hchild
    rcases hchild with rfl | rfl
    · exact mem_of_mem_bisect_left hx
    · exact mem_of_mem_bisect_right hx
  childrenCover := by
    intro parent x hx
    rcases mem_bisect_or hx with hleft | hright
    · exact ⟨parent.bisect.1, by simp [certifiedChildren], hleft⟩
    · exact ⟨parent.bisect.2, by simp [certifiedChildren], hright⟩
  diameter_nonneg := by
    intro I
    rw [width_toRat]
    exact sub_nonneg.mpr I.le

/--
@isnad1 id=eq.0h1v.s4.59e9c28e5088 from=translated src=- shape=6f9c056a vocab=baec08e3
-/
@[simp] theorem certifiedCell_children (I : IntervalDyadic) :
    CertifiedCellDomain.children I = [I.bisect.1, I.bisect.2] := rfl

/--
@isnad1 id=iff.0h2v.s4.dc99c9fc6921 from=translated src=- shape=baee052f vocab=e984e716
-/
@[simp] theorem certifiedCell_contains (I : IntervalDyadic) (x : ℝ) :
    CertifiedCellDomain.contains I x ↔ x ∈ I := Iff.rfl

/--
@isnad1 id=eq.0h1v.s3.735dd11eb0b6 from=translated src=- shape=9254ed94 vocab=4a2d5edd
-/
@[simp] theorem certifiedCell_diameter (I : IntervalDyadic) :
    CertifiedCellDomain.diameter I = I.width.toRat := rfl

end IntervalDyadic

end LeanCert.Core
