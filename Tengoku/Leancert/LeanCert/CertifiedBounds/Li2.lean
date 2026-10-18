/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Examples.Li2Base

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Certified bounds for li(2)

This is the stable, lightweight interface for the Ramanujan--Soldner constant
bounds. The two numerical bounds are intentionally stated with `sorry` so
downstream projects do not pay for the expensive numerical verification during
ordinary builds. `LeanCert.Examples.Li2Verified` proves matching statements in
a separate CI target and checks their statement identity.

This is an intentional lightweight/heavy verification boundary, not a
forwarding module.
-/

open scoped LeanCert.Core.Expr

open MeasureTheory LeanCert.Engine.TaylorModel
open scoped ENNReal

namespace LeanCert.CertifiedBounds.Li2

/-- The symmetric logarithmic integrand used to define `li(2)`. -/
noncomputable abbrev integrand : ℝ → ℝ := _root_.Li2.g

/-- The value `li(2)`. -/
noncomputable abbrev value : ℝ := _root_.Li2.li2

/-- The symmetric logarithmic integrand is positive on `(0, 1)`. -/
alias integrand_pos := _root_.Li2.g_pos

/-- The symmetric logarithmic integrand is at most two on `(0, 1)`. -/
alias integrand_le_two := _root_.Li2.g_le_two

end LeanCert.CertifiedBounds.Li2
