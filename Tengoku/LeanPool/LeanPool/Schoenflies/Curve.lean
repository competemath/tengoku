/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.Plane
public import Tengoku

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

@[expose] public section

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

/-! ### The unit interval, as a subset of `ℝ` -/

/--
@isnad1 id=mem.0h0v.s3.459cb626b961 from=translated src=- shape=d52416c9 vocab=5b115103
-/
theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

/--
@isnad1 id=mem.0h0v.s3.27950bef9fb0 from=translated src=- shape=d52416c9 vocab=5b115103
-/
theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

/--
@isnad1 id=iscompac.0h0v.s3.3f669002c26d from=translated src=- shape=25b03439 vocab=61f78ae6
-/
theorem isCompact_I : IsCompact I := isCompact_Icc

/--
@isnad1 id=isconnec.0h0v.s3.d8bd38af27ff from=translated src=- shape=25b03439 vocab=e3db48e8
-/
theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous.
@isnad1 id=iscompac.3h2v.s6.73cdb3a758a2 from=translated src=- shape=35efe7e2 vocab=24824cf2
-/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

/--
@isnad1 id=isarc.1h3v.s3.fe6461ccc126 from=translated src=- shape=e9fd18df vocab=c6825fb2
-/
theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

/--
@isnad1 id=mem.1h3v.s4.004b895d9591 from=translated src=- shape=e42577a1 vocab=09388cfe
-/
theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

/--
@isnad1 id=mem.1h3v.s4.46309703ee31 from=translated src=- shape=c6429753 vocab=09388cfe
-/
theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

/-- Running a piece the other way round.
@isnad1 id=isarcbet.1h3v.s4.c7f7cc78bbbd from=translated src=- shape=18f1d965 vocab=9f6d8e13
-/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

/--
@isnad1 id=iscompac.1h1v.s5.80f29490c8c4 from=translated src=- shape=f3db9897 vocab=b7d01bea
-/
theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

/--
@isnad1 id=isconnec.1h1v.s5.42663dad9599 from=translated src=- shape=f3db9897 vocab=582d47b6
-/
theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

/--
@isnad1 id=nonempty.1h1v.s3.28a3bb5393b4 from=translated src=- shape=f3db9897 vocab=d4590fa6
-/
theorem nonempty (h : IsArc A) : A.Nonempty := h.isConnected.nonempty

/--
@isnad1 id=isclosed.1h1v.s5.806b1ad46443 from=translated src=- shape=f3db9897 vocab=12c70090
-/
theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

/-- Every arc is an arc between its two endpoints.
@isnad1 id=ex.1h1v.s4.da7b1dee6d91 from=translated src=- shape=8b98ae14 vocab=c6825fb2
-/
theorem exists_isArcBetween (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨f, hc, hi, him⟩ := h
  exact ⟨f 0, f 1, f, hc, hi, him, rfl, rfl⟩

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

/--
@isnad1 id=iscompac.1h1v.s5.d36c52db56b0 from=translated src=- shape=f3db9897 vocab=24ced3ac
-/
theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

/--
@isnad1 id=isconnec.1h1v.s5.728d6de1b701 from=translated src=- shape=f3db9897 vocab=cbd19e59
-/
theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

/--
@isnad1 id=nonempty.1h1v.s3.3f1ab61ba5ae from=translated src=- shape=f3db9897 vocab=6e9096fe
-/
theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

/--
@isnad1 id=isclosed.1h1v.s5.00018116e07b from=translated src=- shape=f3db9897 vocab=df11aeec
-/
theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies
