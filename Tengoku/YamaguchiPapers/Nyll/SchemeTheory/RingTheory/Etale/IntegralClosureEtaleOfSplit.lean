/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.IntegralClosure.IntegralClosureSplitProduct
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Tengoku.Seed.RingTheory.Smooth.IntegralClosure
import Tengoku.Seed.RingTheory.Etale.Descent
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Étale normalization after an actual generic splitting

A splitting over a pointed étale neighborhood gives a split product in a
localization by non-zero-divisors. Local normality of that étale neighborhood
shows it is integrally closed in that localization. Smooth base change of
integral closure and the explicit split-product normalization therefore make
the original integral closure étale after faithfully flat base change. Étale
descent gives the conclusion over the original normal domain.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u v

end SchemeTheory
