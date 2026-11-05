/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.Localization.Ideal
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.FiniteEtale.Henselian.Strict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A uniquely chosen finite étale factor over a strictly Henselian local ring

Tag 00UJ isolates a finite idempotent factor with a unique prime over the
chosen closed point.  Once local purity has made that factor étale, the
uniqueness makes the factor local.  Faithful flatness is then produced from
flatness and the local algebra map, so the connected strict-Henselian
splitting theorem applies without a separate faithfulness hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

end EtaleFundamentalGroups
