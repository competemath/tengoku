/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.FiniteLevelCyclotomicInversion
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclotomic inversion for normalization-ideal inertia

Localization identifies ideal-theoretic inertia in a Dedekind normalization
with inertia for the corresponding discrete valuation subring.  Finite-level
cyclotomic inversion therefore gives conjugacy to inversion directly in the
ambient finite Galois group.
-/

noncomputable section

universe uA uB uK uL

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

end TameAbhyankar.SGA1

end
