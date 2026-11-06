/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianDecomposition
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.UniqueRing
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.Valuation.Extension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual residue scalars in the Henselian decomposition sequence

The residue field of the fixed integer ring and the actual residue field of
an intermediate field have the same image in the selected residue field.
The comparison is proved on integer representatives. It does not assume
an identification of residue fields or separability of residue extensions.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The selected valuation extends the canonical valuation of its actual
pullback to an intermediate field.-/
theorem intermediateFieldComap_hasExtension
    (A : _root_.ValuationSubring L) (E : IntermediateField K L) :
    (A.comap E.val.toRingHom).valuation.HasExtension A.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, _root_.Valuation.mem_integer_iff,
    _root_.ValuationSubring.valuation_le_one_iff, _root_.ValuationSubring.mem_comap]
  rfl

end RamificationTheory.HilbertRamification.ValuationSubring
