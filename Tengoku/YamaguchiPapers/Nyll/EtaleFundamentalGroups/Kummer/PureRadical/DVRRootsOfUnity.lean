/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.DiscreteValuationRing.TFAE
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.PureRadical.IntegralClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Roots of unity in a tame pure-radical DVR extension

This file supplies the non-Henselian roots-of-unity input in the DVR form of
Stacks Project, Lemma 15.115.6 (tag `09EV`).  If a uniformizer acquires an
`n`-th root and `n` is a unit in the base DVR, then every `n`-th root of unity
in the resulting pure-radical field already belongs to the base fraction
field.

The proof uses the canonical power-basis normal form in the root algebra.  A
nonzero element with zero constant coefficient has uniformizer order not
divisible by `n`.  Applying this to the nonconstant part of a root of unity,
the linear term of the binomial expansion has the same order, whereas the
whole expression comes from the base DVR and hence has order divisible by
`n`, a contradiction.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w

end EtaleFundamentalGroups.Kummer
