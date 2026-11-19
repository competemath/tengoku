/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PairCode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Intrinsic corner coordinates

A corner is encoded by its middle line and the slopes of its first and last
lines. The first line meets the middle line at height `a`, and the last meets
it at height `b`. Lebesgue measure in these four vector coordinates is the
intrinsic corner measure used in the supplied manuscript.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Middle-line intercept and slope, followed by the first and last slopes.-/
abbrev CornerCoordinates (m : ℕ) := Line m × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))

/-- First line of a corner, recovered from its first junction.-/
def cornerFirst (a : ℝ) (p : CornerCoordinates m) : Line m :=
  lineAt a (atHeight a p.1) p.2.1

/-- Last line of a corner, recovered from its second junction.-/
def cornerLast (b : ℝ) (p : CornerCoordinates m) : Line m :=
  lineAt b (atHeight b p.1) p.2.2

/--
@isnad1 id=eq.0h3v.s5.56d4fae9bf32 from=translated src=- shape=fb9d7967 vocab=f725b943
-/
theorem atHeight_cornerFirst (a : ℝ) (p : CornerCoordinates m) :
    atHeight a (cornerFirst a p) = atHeight a p.1 := by
  simp [cornerFirst, atHeight_lineAt]

/--
@isnad1 id=eq.0h3v.s5.755ac4f1efdb from=translated src=- shape=fb9d7967 vocab=28abcb93
-/
theorem atHeight_cornerLast (b : ℝ) (p : CornerCoordinates m) :
    atHeight b (cornerLast b p) = atHeight b p.1 := by
  simp [cornerLast, atHeight_lineAt]

/-- Parent pair, ordered as middle line then first line.-/
def cornerParent (a : ℝ) (p : CornerCoordinates m) : PairCoordinates m :=
  (atHeight a p.1, (p.1.2, p.2.1))

/-- Inner pair, ordered as middle line then last line.-/
def cornerInner (b : ℝ) (p : CornerCoordinates m) : PairCoordinates m :=
  (atHeight b p.1, (p.1.2, p.2.2))

/--
@isnad1 id=eq.0h3v.s6.83ea94728c29 from=translated src=- shape=c6ac91aa vocab=459d993c
-/
theorem first_cornerParent (a : ℝ) (p : CornerCoordinates m) :
    lineAt a (cornerParent a p).1 (cornerParent a p).2.1 = p.1 := lineAt_atHeight a p.1

/--
@isnad1 id=eq.0h3v.s5.eb7d9bff1d24 from=translated src=- shape=2d6411c9 vocab=2d452068
-/
theorem second_cornerParent (a : ℝ) (p : CornerCoordinates m) :
    lineAt a (cornerParent a p).1 (cornerParent a p).2.2 = cornerFirst a p := rfl

/--
@isnad1 id=eq.0h3v.s6.f394b2cee2ab from=translated src=- shape=c6ac91aa vocab=0dde5b3c
-/
theorem first_cornerInner (b : ℝ) (p : CornerCoordinates m) :
    lineAt b (cornerInner b p).1 (cornerInner b p).2.1 = p.1 := lineAt_atHeight b p.1

/--
@isnad1 id=eq.0h3v.s5.3dce7676ca91 from=translated src=- shape=2d6411c9 vocab=dc201127
-/
theorem second_cornerInner (b : ℝ) (p : CornerCoordinates m) :
    lineAt b (cornerInner b p).1 (cornerInner b p).2.2 = cornerLast b p := rfl

/-- Intrinsic corners formed by three lines in one family.-/
def cornerFamily (a b : ℝ) (G : Set (Line m)) : Set (CornerCoordinates m) :=
  {p | cornerFirst a p ∈ G ∧ p.1 ∈ G ∧ cornerLast b p ∈ G}

/--
@isnad1 id=measurab.1h4v.s8.d4307e83039c from=translated src=- shape=f185822b vocab=3e0aaa86
-/
theorem measurableSet_cornerFamily (a b : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    MeasurableSet (cornerFamily a b G) := by
  have h₁ : Continuous (cornerFirst (m := m) a) := by
    unfold cornerFirst lineAt atHeight
    fun_prop
  have h₃ : Continuous (cornerLast (m := m) b) := by
    unfold cornerLast lineAt atHeight
    fun_prop
  exact (hG.preimage h₁.measurable).inter
    ((hG.preimage measurable_fst).inter (hG.preimage h₃.measurable))

/--
@isnad1 id=mem.1h5v.s5.cf2ade12903d from=translated src=- shape=e4744c33 vocab=171fcd18
-/
theorem cornerParent_mem_pairFamily {a b : ℝ} {G : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ cornerFamily a b G) : cornerParent a p ∈ pairFamily a G :=
  ⟨by simpa only [first_cornerParent] using hp.2.1, hp.1⟩

/--
@isnad1 id=mem.1h5v.s5.b4c1aaf7c2e3 from=translated src=- shape=215aba16 vocab=52b67301
-/
theorem cornerInner_mem_pairFamily {a b : ℝ} {G : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ cornerFamily a b G) : cornerInner b p ∈ pairFamily b G :=
  ⟨by simpa only [first_cornerInner] using hp.2.1, hp.2.2⟩

end NKBesicovitch.Projection
