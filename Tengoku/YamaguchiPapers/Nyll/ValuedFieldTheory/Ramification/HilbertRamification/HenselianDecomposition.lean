/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Tengoku.Seed.FieldTheory.Galois.Infinite
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decomposition over a Henselian valuation ring

Henselianity identifies the selected extension valuation ring with the
integral closure, so every base-field automorphism preserves it. Consequently
the fixed integers in the residue exact sequence over an intermediate field
come from that intermediate field's actual pulled-back valuation ring.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open scoped Pointwise

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

end RamificationTheory.HilbertRamification.ValuationSubring
