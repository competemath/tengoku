/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.CographPortalFlags

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointwise domination for portal shuffle convolution

This is a finite-vector corollary only.  It contains no face-poset or Hansen
geometry identification.
-/

namespace HansenCograph

/-- Pointwise domination of two nonnegative bounded portal vectors transfers
to pointwise domination of their shuffle convolutions at every output rank.
@isnad1 id=le.4h7v.s7.3cddeb57aaa5 from=translated src=- shape=6053af9e vocab=636afe0e
-/
theorem portalShuffleConvolution_domination
    {n m : ℕ} {a a' b b' : ℕ → ℝ}
    (ha0 : ∀ k < n + 1, 0 ≤ a k)
    (hb0 : ∀ l < m + 1, 0 ≤ b l)
    (haa' : ∀ k < n + 1, a k ≤ a' k)
    (hbb' : ∀ l < m + 1, b l ≤ b' l) :
    ∀ s : ℕ,
      portalShuffleConvolution n m a b s ≤
        portalShuffleConvolution n m a' b' s := by
  intro s
  exact portalShuffleConvolution_le ha0 hb0 haa' hbb' s

end HansenCograph
