/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Staggered-adoption path helpers

Shared helpers for adoption paths encoded as `WithTop (Fin T)`, where `⊤`
represents the never-treated path.
-/

module
public import Tengoku

/-! # Adoption Path Helpers

This file provides finite-period adoption-path predicates for staggered-treatment
designs, including eventual treatment, never treatment, and whether adoption has
occurred by a period. The never-treated path is represented as an infinite
adoption date, so absorbing treatment remains zero in every finite period for
such units.

These paper-agnostic helpers are shared by staggered-adoption modules:
Sun-Abraham path helpers wrap these declarations, and Goodman-Bacon uses the
same raw infinite-date encoding for proof stability. -/

@[expose] public section

namespace Causalean
namespace Panel
namespace AdoptionPath

/-- [For a panel with a finite horizon of $T$ periods](hyp:T) and [a finite adoption period $g$](hyp:g), [the finite adoption path](goal) is the path whose adoption date is $g$, rather than the never-treated date. -/
def finite {T : ℕ} (g : Fin T) : WithTop (Fin T) :=
  (g : WithTop (Fin T))

/-- Embedding a finite adoption period into the shared adoption-path type is
definitionally the ordinary finite-period inclusion.
@isnad1 id=eq.0h2v.s4.7606feab1fdc from=translated src=- shape=7bb58983 vocab=1c37df63
-/
@[simp] theorem finite_eq {T : ℕ} (g : Fin T) :
    finite g = (g : WithTop (Fin T)) := rfl

/-- [For a finite-period horizon](hyp:T), [an adoption path $a$](hyp:a), and [a period $t$ in that horizon](hyp:t), [the treated-by-$t$ predicate](goal) holds exactly when the adoption date is no later than $t$. -/
def le {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop :=
  a ≤ (t : WithTop (Fin T))

/-- The treated-by-period predicate is exactly the order comparison with the
finite period viewed as an adoption date.
@isnad1 id=eq.0h3v.s5.44109f298931 from=translated src=- shape=84ad168e vocab=768b3de6
-/
@[simp] theorem le_eq {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) :
    le a t = (a ≤ (t : WithTop (Fin T))) := rfl

/-- [For a finite-period horizon](hyp:T), [an adoption path $a$](hyp:a), and [a period $t$ in that horizon](hyp:t), [the untreated-at-$t$ predicate](goal) holds exactly when $t$ is strictly before the adoption date. -/
def lt {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop :=
  (t : WithTop (Fin T)) < a

/-- The untreated-before-adoption predicate is exactly the strict order
comparison with the finite period viewed as an adoption date.
@isnad1 id=eq.0h3v.s5.b119236a3e37 from=translated src=- shape=6134f9ef vocab=70af4e3d
-/
@[simp] theorem lt_eq {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) :
    lt a t = ((t : WithTop (Fin T)) < a) := rfl

/-- [For a finite-period horizon](hyp:T) and [an adoption path $a$](hyp:a), [the finite-path predicate](goal) holds exactly when its adoption date is not the never-treated date. -/
def isFinite {T : ℕ} (a : WithTop (Fin T)) : Prop :=
  a ≠ ⊤

/-- A path is eventually treated exactly when its adoption date is not infinite.
@isnad1 id=eq.0h2v.s4.7ad6e1bf9e5a from=translated src=- shape=0e2d5b47 vocab=c69e0157
-/
@[simp] theorem isFinite_eq {T : ℕ} (a : WithTop (Fin T)) :
    isFinite a = (a ≠ ⊤) := rfl

/-- [For a finite-period horizon](hyp:T) and [an adoption path $a$](hyp:a), [the infinite-path predicate](goal) holds exactly when its adoption date is the never-treated date. -/
def isInfinite {T : ℕ} (a : WithTop (Fin T)) : Prop :=
  a = ⊤

/-- A path is never treated exactly when its adoption date is infinite.
@isnad1 id=eq.0h2v.s4.166ff9a2ea73 from=translated src=- shape=95cd3768 vocab=bf041469
-/
@[simp] theorem isInfinite_eq {T : ℕ} (a : WithTop (Fin T)) :
    isInfinite a = (a = ⊤) := rfl

/-- [For a finite-period horizon](hyp:T) and [an adoption path $h$](hyp:h), [the never-treated predicate](goal) holds exactly when $h$ has the never-treated adoption date. -/
def isNeverTreated {T : ℕ} (h : WithTop (Fin T)) : Prop :=
  isInfinite h

/-- The Sun-Abraham-compatible never-treated name is the infinite adoption-date
predicate.
@isnad1 id=eq.0h2v.s4.bee0ad8a31d7 from=translated src=- shape=95cd3768 vocab=87421334
-/
@[simp] theorem isNeverTreated_eq {T : ℕ} (h : WithTop (Fin T)) :
    isNeverTreated h = (h = ⊤) := rfl

/-- [For a finite-period horizon](hyp:T) and [an adoption path $h$](hyp:h), [the eventually-treated predicate](goal) holds exactly when $h$ has a finite adoption date. -/
def isEventuallyTreated {T : ℕ} (h : WithTop (Fin T)) : Prop :=
  isFinite h

/-- The Sun-Abraham-compatible eventually-treated name is the finite
adoption-date predicate.
@isnad1 id=eq.0h2v.s4.4cd8c8c23559 from=translated src=- shape=0e2d5b47 vocab=ce1f4ed5
-/
@[simp] theorem isEventuallyTreated_eq {T : ℕ} (h : WithTop (Fin T)) :
    isEventuallyTreated h = (h ≠ ⊤) := rfl

open Classical in
/-- [For a finite-period horizon](hyp:T), [an adoption path $h$](hyp:h), and [a period $t$ in that horizon](hyp:t), [the absorbing treatment indicator](goal) equals one exactly when $h$ has adopted by $t$, and equals zero otherwise.

Since the never-treated date is later than every finite period, the never-treated path is untreated in every finite period. -/
noncomputable def absorbingTreatment {T : ℕ} (h : WithTop (Fin T)) (t : Fin T) : ℝ :=
  if le h t then 1 else 0

/-- [For an adoption date `h` and period `t` within a horizon of `T` periods](hyp:h,t,T),
[the absorbing treatment indicator equals one exactly when adoption has occurred by that
period, and zero otherwise](goal).
@isnad1 id=eq.0h3v.s6.3b0c35e811d0 from=translated src=- shape=9ebffb8d vocab=7333661d
-/
@[simp] theorem absorbingTreatment_eq {T : ℕ} (h : WithTop (Fin T)) (t : Fin T) :
    absorbingTreatment h t = if h ≤ (t : WithTop (Fin T)) then 1 else 0 := by
  unfold absorbingTreatment le
  by_cases hle : h ≤ (t : WithTop (Fin T)) <;> simp [hle]

/-- If `t < A`, then adoption has not occurred by `t`.
@isnad1 id=not.1h3v.s4.df0a63111124 from=translated src=- shape=99e0aa37 vocab=82fd5b3d
-/
theorem not_le_of_lt {T : ℕ} {a : WithTop (Fin T)} {t : Fin T}
    (hlt : lt a t) : ¬ le a t := by
  cases a <;> simp [lt, le] at *
  exact hlt

/-- Never-treated paths are untreated in every finite period.
@isnad1 id=lt.1h3v.s4.7f11f0edf214 from=translated src=- shape=285994c0 vocab=b4b97beb
-/
theorem lt_of_isInfinite {T : ℕ} {a : WithTop (Fin T)} {t : Fin T}
    (ha : isInfinite a) : lt a t := by
  unfold isInfinite lt at *
  rw [ha]
  exact WithTop.coe_lt_top t

end AdoptionPath
end Panel
end Causalean
