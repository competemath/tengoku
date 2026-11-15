import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace WeierstrassCurve

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : Affine R}

def coordsOrZero : W.Point → R × R
  | .zero => (0, 0)
  | .some x y _ => (x, y)

/--
@isnad1 id=eq.0h2v.s5.c7d2430ea6d8 from=translated src=- shape=f8d1a560 vocab=602cee3a
-/
@[simp] lemma coordsOrZero_zero : ((.zero : W.Point)).coordsOrZero = (0, 0) := rfl

/--
@isnad1 id=eq.1h4v.s5.0fdc504fcb1a from=translated src=- shape=e712e4a3 vocab=4bbd190f
-/
@[simp] lemma coordsOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).coordsOrZero = (x, y) := rfl

end Affine.Point

section SummingSet

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) : Finset (F × F) :=
  (Finset.Icc 1 n).image fun k => (k • Q).coordsOrZero

/--
@isnad1 id=iff.0h5v.s7.138bf40aa75d from=translated src=- shape=777cd1ed vocab=96a65d05
-/
lemma mem_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ} {P : F × F} :
    P ∈ W.oddOrderSummingSet Q n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k • Q).coordsOrZero = P := by
  simp only [oddOrderSummingSet, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ⟨k, h1, h2, h3⟩, fun ⟨k, h1, h2, h3⟩ => ⟨k, ⟨h1, h2⟩, h3⟩⟩

end SummingSet

end WeierstrassCurve
