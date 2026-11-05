/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.IdealCyclotomicInversion
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealResidueComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclotomic inversion from a normalization base residue field

The residue field of a base prime is canonically identified with the
intrinsic decomposition residue field after localization.  Consequently,
geometric integrality stated on the base-prime residue field supplies the
finite-level cyclotomic conjugation theorem for normalization-ideal inertia.
-/

noncomputable section

universe uB uK uL

namespace TameAbhyankar.SGA1

open CategoryTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

end TameAbhyankar.SGA1

end
