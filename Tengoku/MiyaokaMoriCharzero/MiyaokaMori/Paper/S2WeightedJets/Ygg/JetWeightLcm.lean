import Tengoku.Seed.Algebra.GCDMonoid.Finset
import Tengoku.Seed.Order.Interval.Finset.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The common multiple of the jet weights

`jetWeight k = lcm(1, …, k)` is the common multiple `w_k` of the jet weights `1, …, k`
used in the Veronese polarization of the weighted projectivization
(Lemma 2.2 of the paper).

This file imports only Mathlib, so that it can be used below the project's prelude.
-/
namespace Tengoku.MiyaokaMoriCharzero end Tengoku.MiyaokaMoriCharzero open Tengoku.MiyaokaMoriCharzero
set_option autoImplicit false

noncomputable section

/-- The common multiple `w_k = lcm(1, …, k)` of the jet weights of order `≤ k`.-/
def _root_.Tengoku.MiyaokaMoriCharzero.jetWeight (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

end
-- Tengoku: root names of this library moved to Tengoku.MiyaokaMoriCharzero so they do not collide with other libraries (generated)
