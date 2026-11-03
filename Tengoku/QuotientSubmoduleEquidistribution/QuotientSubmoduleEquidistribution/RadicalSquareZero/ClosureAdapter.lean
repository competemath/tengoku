import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.LevelPolynomial
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RadicalSquareZero.Combinatorics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closure-system adapter for radical-square-zero weighted enumeration

This module isolates the exact interface needed to turn the
common-core fiber calculation into an equality of level polynomials.

The two finite ground types and their closure operators are arbitrary.
For each side, the only assumptions are:

* an equivalence from its type of closed sets to the corresponding
  sigma type of decorated common cores; and
* an exact equation identifying the cardinality of each closed set with
  the appropriate decoration weight.

In particular, this module assumes no module classification, no
separated-representation correspondence, and no fact about
radical-square-zero algebras.
-/

namespace QuotientSubmoduleEquidistribution.RadicalSquareZeroCombinatorics

open Finset Polynomial Set
open scoped BigOperators

universe u v w₁ w₂

variable {Core : Type u} {Vertex : Type v}
  [Fintype Core] [Fintype Vertex] [DecidableEq Vertex]

namespace CoreFamily

/-- An explicit size-preserving parametrization of the `A`-side closed
sets by the `A` decorations of the common cores.-/
structure AClosedParametrization
    {E : Type w₁} [Finite E]
    (F : CoreFamily Core Vertex)
    (cl : QuotientSubmoduleEquidistribution.SetClosure E) where
  closedEquiv : cl.Closeds ≃ Σ x : Core, F.AChoice x
  ncard_closed (C : cl.Closeds) :
    (C : Set E).ncard =
      F.aWeight (closedEquiv C).1 (closedEquiv C).2

/-- An explicit size-preserving parametrization of the `B`-side closed
sets by the `B` decorations of the common cores.-/
structure BClosedParametrization
    {E : Type w₂} [Finite E]
    (F : CoreFamily Core Vertex)
    (cl : QuotientSubmoduleEquidistribution.SetClosure E) where
  closedEquiv : cl.Closeds ≃ Σ x : Core, F.BChoice x
  ncard_closed (C : cl.Closeds) :
    (C : Set E).ncard =
      F.bWeight (closedEquiv C).1 (closedEquiv C).2

namespace AClosedParametrization

variable {E : Type w₁} [Finite E]
  {F : CoreFamily Core Vertex}
  {cl : QuotientSubmoduleEquidistribution.SetClosure E}

/-- A size-preserving decorated-core parametrization identifies the
`A`-side level polynomial with the abstract `A` enumerator.
@isnad1 id=eq.0h6v.s5.9a5ea1c96c0a from=translated src=- shape=3a8dbdc8 vocab=814659f9
-/
theorem levelPolynomial_eq_aEnumerator
    (p : AClosedParametrization F cl) :
    cl.levelPolynomial = F.aEnumerator := by
  classical
  let e :
      (Σ x : Core, F.AChoice x) ≃ cl.Closeds :=
    p.closedEquiv.symm
  have hweight :
      ∀ w : Σ x : Core, F.AChoice x,
        ((e w : cl.Closeds) : Set E).ncard =
          F.aWeight w.1 w.2 := by
    intro w
    change
      ((p.closedEquiv.symm w : cl.Closeds) : Set E).ncard =
        F.aWeight w.1 w.2
    calc
      ((p.closedEquiv.symm w : cl.Closeds) : Set E).ncard =
          F.aWeight
            (p.closedEquiv (p.closedEquiv.symm w)).1
            (p.closedEquiv (p.closedEquiv.symm w)).2 :=
        p.ncard_closed (p.closedEquiv.symm w)
      _ = F.aWeight w.1 w.2 := by
        rw [p.closedEquiv.apply_symm_apply]
  rw [QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
    cl e (fun w ↦ F.aWeight w.1 w.2) hweight]
  rw [Fintype.sum_sigma]
  rfl

end AClosedParametrization

namespace BClosedParametrization

variable {E : Type w₂} [Finite E]
  {F : CoreFamily Core Vertex}
  {cl : QuotientSubmoduleEquidistribution.SetClosure E}

/-- A size-preserving decorated-core parametrization identifies the
`B`-side level polynomial with the abstract `B` enumerator.
@isnad1 id=eq.0h6v.s5.ff9487072fb7 from=translated src=- shape=3a8dbdc8 vocab=25e79bc1
-/
theorem levelPolynomial_eq_bEnumerator
    (p : BClosedParametrization F cl) :
    cl.levelPolynomial = F.bEnumerator := by
  classical
  let e :
      (Σ x : Core, F.BChoice x) ≃ cl.Closeds :=
    p.closedEquiv.symm
  have hweight :
      ∀ w : Σ x : Core, F.BChoice x,
        ((e w : cl.Closeds) : Set E).ncard =
          F.bWeight w.1 w.2 := by
    intro w
    change
      ((p.closedEquiv.symm w : cl.Closeds) : Set E).ncard =
        F.bWeight w.1 w.2
    calc
      ((p.closedEquiv.symm w : cl.Closeds) : Set E).ncard =
          F.bWeight
            (p.closedEquiv (p.closedEquiv.symm w)).1
            (p.closedEquiv (p.closedEquiv.symm w)).2 :=
        p.ncard_closed (p.closedEquiv.symm w)
      _ = F.bWeight w.1 w.2 := by
        rw [p.closedEquiv.apply_symm_apply]
  rw [QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
    cl e (fun w ↦ F.bWeight w.1 w.2) hweight]
  rw [Fintype.sum_sigma]
  rfl

end BClosedParametrization

/-- Once both closure systems have the explicit fiber
parametrizations, the separated-side level polynomial is the original
one times the universal Boolean factor.
@isnad1 id=eq.0h9v.s7.daa719886f1f from=translated src=- shape=dc91a76b vocab=a7acc48f
-/
theorem levelPolynomial_B_eq_levelPolynomial_A_mul
    {Eₐ : Type w₁} {Eᵦ : Type w₂}
    [Finite Eₐ] [Finite Eᵦ]
    {F : CoreFamily Core Vertex}
    {clA : QuotientSubmoduleEquidistribution.SetClosure Eₐ}
    {clB : QuotientSubmoduleEquidistribution.SetClosure Eᵦ}
    (pA : AClosedParametrization F clA)
    (pB : BClosedParametrization F clB) :
    clB.levelPolynomial =
      clA.levelPolynomial *
        (1 + X) ^ Fintype.card Vertex := by
  rw [pB.levelPolynomial_eq_bEnumerator,
    pA.levelPolynomial_eq_aEnumerator,
    F.bEnumerator_eq_aEnumerator_mul]

end CoreFamily

end QuotientSubmoduleEquidistribution.RadicalSquareZeroCombinatorics
