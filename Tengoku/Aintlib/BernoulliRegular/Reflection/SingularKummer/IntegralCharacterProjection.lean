/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.ElementaryQuotientComponent
public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.ProjectedSubgroupComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: integral lifts of character projections

The character projection on `A / pA` and on `A[p]` has coefficients in
`ZMod p`.  To apply the finite-group comparison to an actual subgroup of `A`,
we use the integer lift obtained by replacing each coefficient by its standard
representative in `ℕ`.

This file defines that lift and proves that, after passing to `A / pA` or
restricting to `A[p]`, it recovers the corresponding `ZMod p` character
projection.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace IntegralCharacterProjection

open ElementaryQuotientComponent
open TorsionComponent

variable {p : ℕ} [NeZero p]
variable {A : Type*} [AddCommGroup A]

/-- The integer-coefficient lift of the `i`-th character projection.-/
def integralProjection
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    A →+ A :=
  ∑ d : CharacterProjection.Delta p,
    (CharacterProjection.characterProjectionCoefficient (p := p) i d).val •
      (Multiplicative.toAdd (ρ d)).toAddMonoidHom

/--
@isnad1 id=eq.0h5v.s9.1cb9ebfb73b6 from=translated src=- shape=ba4249f5 vocab=5432790e
-/
@[simp]
theorem integralProjection_apply
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) (x : A) :
    integralProjection (p := p) i ρ x =
      ∑ d : CharacterProjection.Delta p,
        (CharacterProjection.characterProjectionCoefficient (p := p) i d).val •
          (Multiplicative.toAdd (ρ d)) x := by
  simp [integralProjection]

/-- The finite subgroup of `A` obtained as the range of the integer lift.-/
abbrev integralComponentSubgroup
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    AddSubgroup A :=
  (integralProjection (p := p) i ρ).range

/-- The integer lift induces the usual character projection on `A / pA`.
@isnad1 id=eq.0h5v.s9.727b8feb8ff2 from=translated src=- shape=f553b641 vocab=f2695e57
-/
theorem quotientMap_integralProjection
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) (x : A) :
    quotientMap A p (integralProjection (p := p) i ρ x) =
      elementaryProjection (p := p) i ρ (quotientMap A p x) := by
  simp [integralProjection, CharacterProjection.characterProjection,
    CharacterProjection.projection]

/-- On `A[p]`, the integer lift is the usual torsion character projection.
@isnad1 id=eq.0h5v.s8.b839aeb1ffe9 from=translated src=- shape=f65f996a vocab=5bf183f0
-/
theorem torsionProjection_apply_coe
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (x : PTorsion A p) :
    ((torsionProjection (p := p) i ρ x : PTorsion A p) : A) =
      integralProjection (p := p) i ρ x.1 := by
  simp [integralProjection, torsionProjection, CharacterProjection.characterProjection,
    CharacterProjection.projection]

end IntegralCharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
