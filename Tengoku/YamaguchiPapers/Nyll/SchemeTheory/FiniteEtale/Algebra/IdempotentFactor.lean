/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Tengoku.Seed.RingTheory.Etale.Basic
public import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
public import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Étale idempotent factors

The quotient imposing `e = 1` for an idempotent `e` is localization at `e`.
Consequently, an idempotent factor of an étale algebra is again étale over
the original base, with the canonical quotient algebra structure.
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- The factor on which an idempotent becomes `1` is étale over the base.
@isnad1 id=etale.1h3v.s7.0c52feba3499 from=translated src=- shape=6905452a vocab=7443aad6
-/
theorem quotient_one_sub_of_isIdempotentElem
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (e : B) (he : IsIdempotentElem e) :
    Algebra.Etale R (B ⧸ Ideal.span {1 - e}) := by
  let : IsLocalization.Away e (B ⧸ Ideal.span {1 - e}) :=
    IsLocalization.away_of_isIdempotentElem he
      (show RingHom.ker (algebraMap B (B ⧸ Ideal.span {1 - e})) =
        Ideal.span {1 - e} from Ideal.mk_ker)
      Ideal.Quotient.mk_surjective
  let : Algebra.Etale B (B ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp R B (B ⧸ Ideal.span {1 - e})

end Algebra.Etale
