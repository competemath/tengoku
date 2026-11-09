/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.DedekindDomain.Different
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Finiteness of ramified primes in Dedekind extensions

In a finite separable extension of Dedekind domains, only finitely many
height-one primes of either the extension ring or the base ring ramify.
-/

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace AlgebraicNumberTheory.Ramification

variable (A B : Type*)
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B]
variable [Module.IsTorsionFree A B] [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

variable {A B}

variable (A B)

/-- Only finitely many height-one primes of a finite separable Dedekind
extension ramify over the base.
@isnad1 id=finite.0h2v.s7.96cf56178186 from=translated src=- shape=a907143a vocab=73dd4452
-/
theorem finite_ramified_heightOne_primes :
    {v : IsDedekindDomain.HeightOneSpectrum B |
        ¬ Algebra.IsUnramifiedAt A v.asIdeal}.Finite := by
  exact
    (Ideal.finite_factors (R := B) (I := differentIdeal A B)
        (differentIdeal_ne_bot (A := A) (B := B))).subset (by
      intro v hv
      exact (dvd_differentIdeal_iff (A := A) (B := B) (P := v.asIdeal)).mpr hv)

end AlgebraicNumberTheory.Ramification
