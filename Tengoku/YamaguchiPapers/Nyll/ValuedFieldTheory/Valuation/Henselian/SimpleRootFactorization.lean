/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From simple-root Hensel lifting to valuation factorization

The Henselian ring assumption now supplies the actual coprime factors.
The valuation factorization criterion then extends the monic result to
all primitive polynomials, with the prescribed reductions and degree bounds.
-/

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField

variable {K : Type*} [Field K] (V : ValuationSubring K)
  [HenselianRing V (IsLocalRing.maximalIdeal V)]

/-- The simple-root Henselian condition supplies monic coprime-factor lifting.
@isnad1 id=monicres.0h2v.s6.dc7a139ff9d0 from=translated src=- shape=8a26db5b vocab=78d5675e
-/
theorem monicResidualCoprimeFactorLifting_of_henselianRing :
    MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfac hcop
  obtain ⟨g, h, hg, hh, hgh, _, _, hgmap, hhmap, _⟩ :=
    ValuationTheory.Henselian.exists_coprime_factor_lift
      (I := IsLocalRing.maximalIdeal V) f gbar hbar hf hgbar hhbar hfac hcop
  exact ⟨g, h, hg, hh, hgh, hgmap, hhmap⟩

/-- A Henselian valuation ring satisfies the full primitive factorization
form of Hensel's lemma, without completeness or rank assumptions.
@isnad1 id=henselfa.0h2v.s6.5e9f830d10d6 from=translated src=- shape=8a26db5b vocab=9f6475aa
-/
theorem henselFactorization_of_henselianRing : HenselFactorizationProperty V :=
  henselianValuationExtension V (monicResidualCoprimeFactorLifting_of_henselianRing V)

end DiscreteValuationField
