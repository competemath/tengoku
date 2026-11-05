/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Flat.Stability
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.RamificationInertia.Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ramification under a finite, flat tensor square

Let `S / R` be finite and let `R' / R` be flat.  A prime of
`R' ⊗[R] S` has two contractions, one to `S` and one to `R'`.  If the
second contraction is the scheme-theoretic extension of the contraction
to `R`, then the two horizontal ramification indices agree in residue
characteristic zero.

The point which is not covered by the usual etale base-change lemma is
that `R' / R` need not be etale (the intended application is an adic
completion).  Instead, the proof identifies the localization of the
`S`-fiber at the retained tensor prime with a localization of

`p'.ResidueField ⊗[p.ResidueField] q.ResidueField`.

The latter is a reduced Artinian algebra: finiteness comes from `S / R`,
and separability comes from residue characteristic zero.  Its prime
localizations are therefore fields, which says that the vertical
ramification index is one.  The tensor prime itself, rather than an
independently selected component, is retained throughout.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uS uR'

section ResidueTensor

variable {R : Type uR} {S : Type uS}
  [CommRing R] [CommRing S] [Algebra R S]

end ResidueTensor

section TensorSquare

variable {R : Type uR} {S : Type uS} {R' : Type uR'}
  [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']

/- The canonical right tensor algebra, scalar tower, and inherited flatness
are owned here once.  This prevents each public wrapper from rebuilding the
same instance path. -/
local instance tensorSquareRightAlgebra :
    Algebra S (R' ⊗[R] S) :=
  Algebra.TensorProduct.rightAlgebra

/--
@isnad1 id=isscalar.0h3v.s7.5b2e7817ef63 from=translated src=- shape=fd193388 vocab=b4bfa4d0
-/
local instance tensorSquareRightScalarTower :
    IsScalarTower R S (R' ⊗[R] S) :=
  Algebra.TensorProduct.right_isScalarTower

/--
@isnad1 id=flat.0h3v.s7.ca215e848236 from=translated src=- shape=3ab04e0c vocab=b3375579
-/
local instance tensorSquareRightFlat [Module.Flat R R'] :
    Module.Flat S (R' ⊗[R] S) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv

end TensorSquare

end EtaleFundamentalGroups

end
