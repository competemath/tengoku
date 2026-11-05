/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Scheme.BlowUp.Rees.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The graded Rees algebra: components and degree one

Basic facts about the grading `reesAlgebra.grading I` of the Rees algebra `⨁ᵢ Iⁱ tⁱ`
[Hau14, Definition 4.6], in which Mathlib's polynomial variable `X` plays the role of Hauser's `t`.

* `reesAlgebra.coe_component`: the degree-`n` component of `p` is the monomial `(coeff n p) tⁿ`.
* `reesAlgebra.degreeOne I : I →ₗ[R] reesAlgebra I`: the degree-one element `a t` of `a ∈ I`
  [Hau14, Definition 4.16], whose range is the degree-one piece
  (`reesAlgebra.grading_one_eq_range`) and whose values generate the irrelevant ideal
  (`Hironaka.Scheme.BlowUp.Rees.Irrelevant`).
-/

@[expose] public section

open Polynomial

universe u

variable {R : Type u} [CommRing R]

section Components

variable {I : Ideal R}

/--
@isnad1 id=eq.0h4v.s13.4d18f982d9e6 from=translated src=- shape=ca0c27ae vocab=b0e98012
-/
@[simp]
theorem reesAlgebra.coe_component (n : ℕ) (p : reesAlgebra I) :
    ((reesAlgebra.component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) :=
  rfl

end Components

section DegreeOne

variable (I : Ideal R)

/-- The degree-one element `a t` of the Rees algebra, for `a ∈ I` — an element of `I` defines a
homogeneous element of degree `1` of the Rees algebra [Hau14, Definition 4.16] — as an `R`-linear
map `I → reesAlgebra I`.  Its range is the degree-one piece (`reesAlgebra.grading_one_eq_range`),
its values generate the irrelevant ideal (`reesAlgebra.irrelevant_le_span_degreeOne`), and the
chart cover of the affine blow-up is indexed by it (`affineBlowUp.affineOpenCover`).-/
noncomputable def reesAlgebra.degreeOne : I →ₗ[R] reesAlgebra I where
  toFun a := ⟨monomial 1 (a : R), reesAlgebra.monomial_mem.mpr (by simp)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (by simp [smul_monomial])

variable {I}

/--
@isnad1 id=eq.0h3v.s10.49120cc8f50a from=translated src=- shape=7a16a888 vocab=1eb94ab5
-/
@[simp]
theorem reesAlgebra.coe_degreeOne (a : I) :
    (reesAlgebra.degreeOne I a : R[X]) = monomial 1 (a : R) :=
  rfl

/--
@isnad1 id=mem.0h3v.s11.e7a45db0fa05 from=translated src=- shape=8cc3ae73 vocab=d8913bbb
-/
theorem reesAlgebra.degreeOne_mem (a : I) :
    reesAlgebra.degreeOne I a ∈ reesAlgebra.grading I 1 :=
  reesAlgebra.mem_grading_of_coe_eq_monomial rfl

/-- The degree-one piece is `I t`: its elements are exactly the `a t`, `a ∈ I`.
@isnad1 id=iff.0h3v.s11.9acfe1d17042 from=translated src=- shape=866f3c53 vocab=d8913bbb
-/
theorem reesAlgebra.mem_grading_one_iff {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I 1 ↔ ∃ a : I, reesAlgebra.degreeOne I a = p := by
  refine ⟨fun hp => ?_, fun ⟨a, ha⟩ => ha ▸ reesAlgebra.degreeOne_mem a⟩
  obtain ⟨c, hc, hpc⟩ := reesAlgebra.mem_grading_iff_exists.mp hp
  exact ⟨⟨c, by simpa using hc⟩, Subtype.ext hpc.symm⟩

variable (I) in
/-- The degree-one piece is the range of `a ↦ a t`.
@isnad1 id=eq.0h2v.s9.f5628356be10 from=translated src=- shape=0806dcea vocab=fdfc119e
-/
theorem reesAlgebra.grading_one_eq_range :
    reesAlgebra.grading I 1 = LinearMap.range (reesAlgebra.degreeOne I) :=
  Submodule.ext fun _ => reesAlgebra.mem_grading_one_iff.trans LinearMap.mem_range.symm

end DegreeOne
