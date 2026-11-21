/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Tengoku.LeanSpectralTheory.Spectral.Stone.Theorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Intrinsic statement of Stone's generator relation

This file packages Stone's generator relation intrinsically, by the exact
punctured-neighborhood difference-quotient domain and limit, without exposing
the library's choice-based construction of the generator. It states Stone's
theorem in both directions: every strongly continuous unitary group has a
self-adjoint generator, and every self-adjoint operator generates such a
group.
-/
namespace Tengoku.LeanSpectralTheory end Tengoku.LeanSpectralTheory open Tengoku.LeanSpectralTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- `U` has infinitesimal generator `A`: its domain is exactly the vectors
whose Stone difference quotient converges, and the limit is `A`.-/
def Tengoku.LeanSpectralTheory.StrongContUnitary.Generates (U : StrongContUnitary E)
    (A : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ A.domain ↔
    ∃ y, Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) ∧
  ∀ x : A.domain, Filter.Tendsto
    (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
    (nhdsWithin 0 {0}ᶜ) (nhds (A x))
-- Tengoku: root names of this library moved to Tengoku.LeanSpectralTheory so they do not collide with other libraries (generated)
