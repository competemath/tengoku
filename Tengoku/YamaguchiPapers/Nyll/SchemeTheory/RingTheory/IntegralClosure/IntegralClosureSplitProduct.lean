/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.Algebra.Algebra.Pi
import Tengoku.Seed.RingTheory.Finiteness.Prod
import Tengoku.Seed.RingTheory.Etale.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalization of a split finite generic algebra

If the base ring is integrally closed in an ambient algebra, its integral
closure in a finite product of copies of that algebra is the same finite
product of the base ring. Coordinate evaluation supplies every integral
coordinate; conversely a finite product of copies of the base is finite,
so all of its elements are integral. This also proves that this actual
integral closure is étale over the base.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- Normalize a split finite product by normalizing each actual coordinate.-/
def integralClosureSplitProductEquiv
    (R : Type u) (K : Type v) (ι : Type w)
    [CommRing R] [CommRing K] [Algebra R K]
    [IsIntegrallyClosedIn R K] [Finite ι] :
    integralClosure R (ι → K) ≃ₐ[R] (ι → R) := by
  letI : IsIntegralClosure (ι → R) R (ι → K) :=
    { algebraMap_injective := by
        intro a b h
        funext i
        apply (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn R K)).1
        exact congrFun h i
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          have hi (i : ι) : IsIntegral R (x i) :=
            hx.map (Pi.evalAlgHom R (fun _ : ι => K) i)
          choose a ha using fun i => IsIntegrallyClosedIn.algebraMap_eq_of_integral (hi i)
          exact ⟨a, funext ha⟩
        · rintro ⟨a, rfl⟩
          exact (IsIntegral.of_finite R a).map (IsScalarTower.toAlgHom R (ι → R) (ι → K)) }
  exact IsIntegralClosure.equiv R (integralClosure R (ι → K)) (ι → K) (ι → R)

/-- The actual integral closure of a finite split product is étale.-/
theorem integralClosure_splitProduct_etale
    (R : Type u) (K : Type v) (ι : Type w)
    [CommRing R] [CommRing K] [Algebra R K]
    [IsIntegrallyClosedIn R K] [Finite ι] :
    Algebra.Etale R (integralClosure R (ι → K)) :=
  Algebra.Etale.of_equiv (integralClosureSplitProductEquiv R K ι).symm

end SchemeTheory
