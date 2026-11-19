/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Tengoku.Jsp000198Lean.Prize.Geometry.EmptyPolygon

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The recursive separation conditions of a Horton configuration

The function is considered only on indices below `2 ^ depth`. The two children
are its even and odd subsequences. The conditions use actual real-plane signed
areas; existence and the empty-polygon bound are separate proof obligations.
-/

namespace Prize.Horton

open Prize.Geometry

def evenPoints (p : ℕ → Point) : ℕ → Point := fun i => p (2 * i)
def oddPoints (p : ℕ → Point) : ℕ → Point := fun i => p (2 * i + 1)

def IsHorton : ℕ → (ℕ → Point) → Prop
  | 0, _ => True
  | depth + 1, p =>
      IsHorton depth (evenPoints p) ∧
      IsHorton depth (oddPoints p) ∧
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        0 < orient (p (2 * i)) (p (2 * j)) (p (2 * t + 1))) ∧
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        orient (p (2 * i + 1)) (p (2 * j + 1)) (p (2 * t)) < 0)

/--
@isnad1 id=ishorton.1h2v.s4.e421891f6fd0 from=translated src=- shape=f22628ca vocab=39672b7a
-/
theorem IsHorton.even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) : IsHorton depth (evenPoints p) := h.1

/--
@isnad1 id=ishorton.1h2v.s4.3c2d609d533a from=translated src=- shape=f22628ca vocab=10639d2c
-/
theorem IsHorton.odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) : IsHorton depth (oddPoints p) := h.2.1

/--
@isnad1 id=lt.4h5v.s7.4672489c324b from=translated src=- shape=b2bd9a7d vocab=e971a080
-/
theorem IsHorton.above {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j t : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) (ht : t < 2 ^ depth) :
    0 < orient (p (2 * i)) (p (2 * j)) (p (2 * t + 1)) :=
  h.2.2.1 i j t hij hj ht

/--
@isnad1 id=lt.4h5v.s7.c8559c529693 from=translated src=- shape=ed1d15fc vocab=e971a080
-/
theorem IsHorton.below {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j t : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) (ht : t < 2 ^ depth) :
    orient (p (2 * i + 1)) (p (2 * j + 1)) (p (2 * t)) < 0 :=
  h.2.2.2 i j t hij hj ht

/-- The segment is visible from above: no intermediate-index point is above it.-/
def UpperVisible (p : ℕ → Point) (i j : ℕ) : Prop :=
  ∀ t : ℕ, i < t → t < j → orient (p i) (p j) (p t) ≤ 0

/-- The corresponding visibility condition from below.-/
def LowerVisible (p : ℕ → Point) (i j : ℕ) : Prop :=
  ∀ t : ℕ, i < t → t < j → 0 ≤ orient (p i) (p j) (p t)

/--
@isnad1 id=uppervis.1h3v.s6.d046c6a73aec from=translated src=- shape=a46f8404 vocab=41e2222c
-/
theorem upperVisible_odd {p : ℕ → Point} {i j : ℕ}
    (h : UpperVisible p (2 * i + 1) (2 * j + 1)) :
    UpperVisible (oddPoints p) i j := by
  intro t hit htj
  exact h (2 * t + 1) (by omega) (by omega)

/--
@isnad1 id=lowervis.1h3v.s5.15013e62eb3a from=translated src=- shape=a01b80fc vocab=5b465dea
-/
theorem lowerVisible_even {p : ℕ → Point} {i j : ℕ}
    (h : LowerVisible p (2 * i) (2 * j)) :
    LowerVisible (evenPoints p) i j := by
  intro t hit htj
  exact h (2 * t) (by omega) (by omega)

/--
@isnad1 id=not.3h4v.s6.c8d42e42bbb1 from=translated src=- shape=de796575 vocab=3ceffef2
-/
theorem IsHorton.not_upperVisible_even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) :
    ¬UpperVisible p (2 * i) (2 * j) := by
  intro hv
  have hp := h.above hij hj (lt_trans hij hj)
  have hn := hv (2 * i + 1) (by omega) (by omega)
  exact (not_lt_of_ge hn) hp

/--
@isnad1 id=not.3h4v.s6.a6d7e3cd8b9d from=translated src=- shape=73645810 vocab=8de2d0c0
-/
theorem IsHorton.not_lowerVisible_odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) :
    ¬LowerVisible p (2 * i + 1) (2 * j + 1) := by
  intro hv
  have hp := h.below hij hj hj
  have hn := hv (2 * j) (by omega) (by omega)
  exact (not_lt_of_ge hn) hp

end Prize.Horton
