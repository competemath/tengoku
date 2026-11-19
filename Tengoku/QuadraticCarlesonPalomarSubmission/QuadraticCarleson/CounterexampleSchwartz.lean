/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Counterexample
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.SchwartzOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The counterexample as a Schwartz function

The paper's finite wave-packet superposition is smooth and compactly
supported, hence belongs to Schwartz space.  Bundling it this way lets the
canonical distributional quadratic Hilbert transform act on it directly.
-/

open scoped ContDiff SchwartzMap

namespace QuadraticCarleson

/--
@isnad1 id=contdiff.0h2v.s5.d784b34898aa from=translated src=- shape=7c676072 vocab=67330efd
-/
theorem contDiff_wavePacket (s t : ℝ) : ContDiff ℝ ∞ (wavePacket s t) := by
  unfold wavePacket
  exact contDiff_const.mul
    (baseBump_smooth.comp ((contDiff_id.sub contDiff_const).div_const t))

/--
@isnad1 id=contdiff.0h1v.s5.713fe48a9462 from=translated src=- shape=1e5679e5 vocab=1f780263
-/
theorem contDiff_packetSum (N : ℕ) : ContDiff ℝ ∞ (packetSum N) := by
  rw [packetSum, Finset.sum_fn]
  exact ContDiff.sum fun j _ ↦ contDiff_wavePacket (j : ℝ) (packetScale N j)

/--
@isnad1 id=contdiff.0h1v.s5.df16d1ac7a2b from=translated src=- shape=1e5679e5 vocab=0e622fd2
-/
theorem contDiff_counterexampleReal (N : ℕ) :
    ContDiff ℝ ∞ (counterexampleReal N) := by
  unfold counterexampleReal
  exact contDiff_const.mul (contDiff_packetSum N)

/--
@isnad1 id=contdiff.0h1v.s5.d2a4a3d43105 from=translated src=- shape=caa53032 vocab=539c33dc
-/
theorem contDiff_counterexample (N : ℕ) : ContDiff ℝ ∞ (counterexample N) := by
  unfold counterexample
  exact Complex.ofRealCLM.contDiff.comp (contDiff_counterexampleReal N)

/-- The counterexample `χ_N` as a complex Schwartz function.-/
noncomputable def counterexampleSchwartz (N : ℕ) : 𝓢(ℝ, ℂ) :=
  (counterexample_hasCompactSupport N).toSchwartzMap (contDiff_counterexample N)

/--
@isnad1 id=eq.0h2v.s5.83d8f69e3b3e from=translated src=- shape=7a784183 vocab=a7e1fb15
-/
@[simp]
theorem counterexampleSchwartz_apply (N : ℕ) (x : ℝ) :
    counterexampleSchwartz N x = counterexample N x :=
  rfl

end QuadraticCarleson
