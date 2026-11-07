/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Tengoku.Arklib.ArkLib.Data.Polynomial.UniversalHenselNumerator
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal numerator recurrence acceptance clients

The nonlinear equation `V² + 2V - U = 0` distinguishes the first two numerators and tests
both omission of the current coefficient and the zero constant prefix. Reduction modulo two
checks that naturality requires no injectivity and remains a ring identity at a zero slope.
-/

open Polynomial Polynomial.UniversalHenselNumerator

private noncomputable def shifted : Polynomial (Polynomial ℤ) :=
  X ^ 2 + C 2 * X - C X
