/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting residue automorphisms through a decomposition group

For a chosen valuation on a Galois extension, every automorphism of its
residue field over the residue field of the decomposition field lifts to an
ambient Galois automorphism stabilizing the chosen valuation.  This is the
elementwise form of the residue-action exact sequence.
-/

noncomputable section

universe u v

namespace RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

end RamificationTheory.HilbertRamification.ValuationSubring
