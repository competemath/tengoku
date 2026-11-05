/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Tengoku.Seed.RingTheory.Invariant.Galois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two actual Galois actions on an integral closure

The fraction-ring restriction used by ramification theory and the literal
restriction used by normalization geometry agree on the embedded integral
closure. The comparison follows by applying its injective inclusion into the
common field, where both automorphisms are the original field automorphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R K L : Type u) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsFractionRing R K] [Algebra.IsAlgebraic K L]

/-- Fraction-ring restriction and literal restriction define the same
homomorphism into the automorphisms of the integral closure.
@isnad1 id=eq.0h3v.s12.29220ac9d1e1 from=translated src=- shape=2c6e7b5a vocab=ce680c4c
-/
theorem galRestrict_integralClosure_eq :
    (galRestrict R K L (integralClosure R L)).toMonoidHom =
      (integralClosureAutHom R L).comp (AlgEquiv.restrictScalarsHom R) := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro b
  apply Subtype.ext
  exact algebraMap_galRestrict_apply R σ b

/-- The normalization-ring action in ramification theory is the actual
restriction action on the same integral closure, with no choice of comparison.
@isnad1 id=eq.0h3v.s11.e9373b59101e from=translated src=- shape=86be7739 vocab=fd607f6c
-/
theorem integralClosureGaloisAction_eq :
    IsIntegralClosure.MulSemiringAction R K L (integralClosure R L) =
      MulSemiringAction.compHom (integralClosure R L)
        ((integralClosureAutHom R L).comp (AlgEquiv.restrictScalarsHom R)) := by
  change MulSemiringAction.compHom (integralClosure R L)
    (galRestrict R K L (integralClosure R L)).toMonoidHom = _
  rw [galRestrict_integralClosure_eq R K L]

end EtaleFundamentalGroups.Inertia
