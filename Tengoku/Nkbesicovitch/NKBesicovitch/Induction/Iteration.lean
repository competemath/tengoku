/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Seed
public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Lift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite iteration of the plate deficit

Starting with zero-dimensional disks in codimension `c > 0`, every lift
divides the deficit by the same fixed `2 < ρ < criticalExponent`. After
`j` lifts the deficit is `c/ρ^j`, and the input exponent remains finite
and at least two. The requested strict dimension range therefore supplies
a lower-dimensional estimate with deficit less than one, ready for the
remaining Fourier terminal step.
-/

public section

open Set

namespace NKBesicovitch.Induction

end NKBesicovitch.Induction
