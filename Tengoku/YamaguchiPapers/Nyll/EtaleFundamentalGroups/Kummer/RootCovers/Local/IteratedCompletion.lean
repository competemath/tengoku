/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Finiteness.Ideal
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenFactor.Core
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete local iterated root covers

A finite iterated positive root cover of closed-point elements is complete for
its own maximal ideal when the Noetherian local base is complete.  Finite-module
completeness first gives completeness for the extended base maximal ideal.  The
two adic filtrations are then compared using integrality and localness: the
upstairs maximal ideal is the radical of the extended ideal, so a positive
power lies in that extended ideal.

All algebraic and local structures are installed only inside the proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u

open ValuationTheory.DiscreteValuationField
open Polynomial

end EtaleFundamentalGroups.Kummer

end
