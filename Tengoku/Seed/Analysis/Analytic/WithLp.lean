/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Analytic.Linear
public import Tengoku.Seed.Analysis.Normed.Lp.PiLp

/-!
# Analyticity on `WithLp`
-/

public section

open WithLp

open scoped ENNReal

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/--
@isnad1 id=analytic.0h5v.s6.11ee60bf164b from=seed src=0 shape=bfeb01c5 vocab=1eea75ca
-/
lemma analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s :=
  (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

/--
@isnad1 id=analytic.0h5v.s6.d412fd82189c from=seed src=0 shape=c3deed0e vocab=a08f95ce
-/
lemma analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

end WithLp

namespace PiLp

variable {𝕜 ι : Type*} [Fintype ι] {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/--
@isnad1 id=analytic.0h5v.s7.0138a290a71a from=seed src=0 shape=1fed0d7f vocab=2ba422da
-/
lemma analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s :=
  (continuousLinearEquiv p 𝕜 E).analyticOn s

/--
@isnad1 id=analytic.0h5v.s7.bbdeb2abc9a7 from=seed src=0 shape=786ef862 vocab=ede83888
-/
lemma analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s :=
  (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

end PiLp
