/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Radical
public import Tengoku

/-!
# Admissible ideals and bound quiver algebras

A two-sided ideal `I` of a path algebra `kQ` is *admissible* when it is squeezed between a power
of the arrow ideal `R` and its square, `R ^ N ≤ I ≤ R ^ 2`. The two bounds say complementary
things about the relations `I` imposes. The upper bound `I ≤ R ^ 2` says that every relation is a
combination of paths of length at least two: a relation involving a vertex idempotent or a single
arrow would change the quiver data itself — identifying or collapsing vertices or arrows — rather
than impose a relation on the paths of `Q`. The lower bound `R ^ N ≤ I` says that all long enough
paths are killed, which is what cuts the quotient down to finite dimension.

The quotient `kQ ⧸ I` by an admissible ideal is a *bound quiver algebra*, and the two main results
here are its two basic properties: it is **finite-dimensional** whenever the quiver has finitely
many vertices and arrows, even when `kQ` itself is not, and every element of the arrow ideal
becomes **nilpotent** in it.

## Main definitions

* `TauCeti.IsAdmissibleIdeal`: the predicate `R ^ N ≤ I ≤ R ^ 2` on a two-sided ideal of a path
  algebra, for the arrow ideal `R = TauCeti.arrowIdeal k Q` and some `N`.

## Main results

* `TauCeti.IsAdmissibleIdeal.finiteDimensional_quotient`: **a bound quiver algebra is
  finite-dimensional**, over a quiver with finitely many vertices and finitely many arrows. No
  acyclicity is needed, and the one-loop quiver shows that this is a genuine gain: its path
  algebra `k[X]` is infinite-dimensional (`TauCeti.not_finiteDimensional_pathAlgebra_oneLoop`)
  while the quotients `k[X] ⧸ (Xⁿ)` by the admissible ideals of
  `TauCeti.isAdmissibleIdeal_arrowIdeal_pow` are not.
* `TauCeti.IsAdmissibleIdeal.isNilpotent_mk_of_mem_arrowIdeal`: the image of an element of
  the arrow ideal in a bound quiver algebra is nilpotent.
* `TauCeti.IsAdmissibleIdeal.ofPath_notMem_of_length_lt_two`, together with
  `TauCeti.IsAdmissibleIdeal.vertexIdempotent_notMem` and
  `TauCeti.IsAdmissibleIdeal.ofArrow_notMem`: an admissible ideal contains no vertex idempotent and
  no arrow, so the quiver survives the passage to the quotient. In particular the quotient is
  nonzero, `TauCeti.IsAdmissibleIdeal.nontrivial_quotient`. More is true and is
  `TauCeti.IsAdmissibleIdeal.linearIndependent_mk_ofPath_of_length_lt_two`: the vertices and the
  arrows stay *linearly independent* in the quotient, so the quotient map is injective on their
  span.
* `TauCeti.isAdmissibleIdeal_iff`: admissibility checked entirely on the path basis.
* `TauCeti.isAdmissibleIdeal_arrowIdeal_pow`: the powers `R ^ n` with `2 ≤ n` are admissible, and
  `TauCeti.isAdmissibleIdeal_bot_of_isAcyclic`: over a finite acyclic quiver the zero ideal is
  admissible, so `kQ` is itself a bound quiver algebra, with no relations.

## Implementation notes

The exponent `N` of the lower bound is existentially quantified in the definition rather than
carried as data: no result below depends on a particular choice, and quantifying it makes
`TauCeti.isAdmissibleIdeal_arrowIdeal_pow` and `TauCeti.isAdmissibleIdeal_bot_of_isAcyclic` the
statements they should be. The usual textbook phrasing adds `2 ≤ N`, which is redundant: `R ^ N`
decreases in `N`, so `R ^ N ≤ I` for some `N` gives it for every larger one.

`Ideal R` means *left* ideal in Mathlib, two-sidedness being the separate typeclass
`Ideal.IsTwoSided` — which `TauCeti.arrowIdeal` carries. Admissibility is a notion about
*two-sided* ideals: it is the quotient *algebra* `kQ ⧸ I` that it exists to describe, and the two
inclusions `R ^ N ≤ I ≤ R ^ 2` alone do not force `I` to be two-sided. `TauCeti.IsAdmissibleIdeal`
therefore takes `[I.IsTwoSided]` as an argument of the predicate itself, so that the ideals it
speaks of are exactly the admissible ones, and every consequence — in particular those about the
quotient, where `Ideal.Quotient` asks for the same instance — is available from the predicate
alone. For the ideals of `TauCeti.isAdmissibleIdeal_arrowIdeal_pow` and
`TauCeti.isAdmissibleIdeal_bot_of_isAcyclic` the instance is found by synthesis.

Finite dimensionality is proved by spanning: the images of the paths of length less than `N` span
the quotient, because every longer path already lies in `I`, and there are finitely many of them
(`TauCeti.Quiver.finite_setOf_length_lt`). This is where the finiteness of the *arrow* types
enters — the rest of the file needs only finitely many vertices, that being what makes `kQ`
unital.

## References

This implements the "admissible ideal" part of Layer 3A of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, the finite-dimensional
algebra infrastructure that its `kQ/I` presentation theorem rests on. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. II.2.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

section Defs

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- A two-sided ideal of a path algebra is **admissible** when some power of the arrow ideal is
contained in it and it is contained in the square of the arrow ideal. The quotient of the path
algebra by an admissible ideal is a *bound quiver algebra*. -/
structure IsAdmissibleIdeal (I : Ideal (pathAlgebra k Q)) [I.IsTwoSided] : Prop where
  /-- Some power of the arrow ideal is contained in `I`: all long enough paths are killed. -/
  exists_arrowIdeal_pow_le : ∃ N, arrowIdeal k Q ^ N ≤ I
  /-- `I` is contained in the square of the arrow ideal: every relation is supported on the paths
  of length at least two. -/
  le_arrowIdeal_sq : I ≤ arrowIdeal k Q ^ 2

namespace IsAdmissibleIdeal

variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- **An admissible ideal contains every long enough path**: this is the lower bound, read on the
path basis. -/
theorem exists_ofPath_mem (h : IsAdmissibleIdeal I) :
    ∃ N, ∀ x : Quiver.TotalPath Q, N ≤ x.2.2.length → (ofPath x : pathAlgebra k Q) ∈ I := by
  obtain ⟨N, hN⟩ := h.exists_arrowIdeal_pow_le
  exact ⟨N, fun x hx => hN (mem_arrowIdeal_pow.2 (ofPath_mem_pathSpan hx))⟩

end IsAdmissibleIdeal

variable (k Q)

end Defs

/-! ### The bound quiver algebra -/

section Quotient

variable {k : Type w} {Q : Type u} [CommRing k] [Quiver.{v} Q] [Finite Q]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

namespace IsAdmissibleIdeal

end IsAdmissibleIdeal

end Quotient

section FiniteDimensional

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Finite Q]
variable [∀ a b : Q, Finite (a ⟶ b)]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- **A bound quiver algebra is finite-dimensional.** The images of the paths of length less than
`N` span it, because a longer path already lies in the ideal, and a quiver with finitely many
vertices and finitely many arrows has only finitely many paths of bounded length. The path algebra
itself need not be finite-dimensional: that needs finitely many paths of *every* length, hence
acyclicity, whereas the bound `R ^ N ≤ I` supplies the missing truncation. -/
theorem IsAdmissibleIdeal.finiteDimensional_quotient (h : IsAdmissibleIdeal I) :
    FiniteDimensional k (pathAlgebra k Q ⧸ I) := by
  obtain ⟨N, hN⟩ := h.exists_ofPath_mem
  set π : pathAlgebra k Q →ₗ[k] pathAlgebra k Q ⧸ I := (Ideal.Quotient.mkₐ k I).toLinearMap with hπ
  have hπ_apply (f : pathAlgebra k Q) : π f = Ideal.Quotient.mk I f := by
    rw [hπ, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  -- The images of *all* the basis paths span the quotient, the quotient map being onto.
  have htop : Submodule.span k (Set.range fun x : Quiver.TotalPath Q => π (ofPath x)) = ⊤ := by
    have hmap : Submodule.map π ⊤ = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 (fun y => by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨f, rfl⟩)]
    rw [← hmap, ← (pathAlgebraBasis k Q).span_eq, Submodule.map_span, coe_pathAlgebraBasis,
      ← Set.range_comp]
    rfl
  -- Only the short ones are needed: the rest map to zero.
  have hshort : Submodule.span k
      ((fun x : Quiver.TotalPath Q => π (ofPath x)) '' {x | x.2.2.length < N}) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htop]
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun x => SetLike.mem_coe.2 ?_)
    by_cases hx : x.2.2.length < N
    · exact Submodule.subset_span ⟨x, hx, rfl⟩
    · have hzero : π (ofPath x) = 0 :=
        (hπ_apply _).trans (Ideal.Quotient.eq_zero_iff_mem.2 (hN x (by omega)))
      rw [hzero]
      exact Submodule.zero_mem _
  exact ⟨hshort ▸ Submodule.fg_span ((Quiver.finite_setOf_length_lt N).image _)⟩

end FiniteDimensional

end TauCeti
