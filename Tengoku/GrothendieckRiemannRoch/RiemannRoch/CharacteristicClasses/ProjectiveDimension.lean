/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveIntegral
import Tengoku.Seed.RingTheory.KrullDimension.Field
import Tengoku.Seed.RingTheory.KrullDimension.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dimension bound for standard projective space

Every proper homogeneous ideal in the standard graded polynomial ring over a field is contained
in the irrelevant ideal.  Thus adjoining a top element to the projective spectrum embeds
strictly monotonically into the ordinary prime spectrum by sending the new top to the irrelevant
prime.  The polynomial ring has dimension `n + 1`, while adjoining a top increases Krull
dimension by one, giving `dim ℙⁿ ≤ n`.
-/

noncomputable section

open AlgebraicGeometry Order

universe u

namespace SchemeProjectiveSpace

attribute [local instance] gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The irrelevant ideal of the standard graded polynomial ring over a field is prime.
@isnad1 id=isprime.0h2v.s9.21350d0ab575 from=translated src=- shape=b1b45ddf vocab=99df1fe8
-/
theorem irrelevantIdeal_isPrime :
    (HomogeneousIdeal.irrelevant (grading k n)).toIdeal.IsPrime := by
  letI : IsDomain (grading k n 0) :=
    (degreeZeroEquiv k n).toMulEquiv.isDomain k
  have hker : RingHom.ker (GradedRing.projZeroRingHom (grading k n)) =
      RingHom.ker (GradedRing.projZeroRingHom' (grading k n)) := by
    ext p
    simp only [RingHom.mem_ker, GradedRing.projZeroRingHom_apply]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rw [HomogeneousIdeal.toIdeal_irrelevant, hker]
  exact RingHom.ker_isPrime _

/-- The irrelevant ideal as a point of the ordinary prime spectrum.-/
def irrelevantPrime : PrimeSpectrum (Polynomial k n) :=
  ⟨(HomogeneousIdeal.irrelevant (grading k n)).toIdeal,
    irrelevantIdeal_isPrime k n⟩

/-- Add the irrelevant prime below the scheme specialization order, mapping into the dual of the
ordinary prime spectrum.-/
def withBotToPrimeSpectrumDual :
    WithBot (space k n) → (PrimeSpectrum (Polynomial k n))ᵒᵈ
  | ⊥ => irrelevantPrime k n
  | (x : space k n) => ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

end SchemeProjectiveSpace
