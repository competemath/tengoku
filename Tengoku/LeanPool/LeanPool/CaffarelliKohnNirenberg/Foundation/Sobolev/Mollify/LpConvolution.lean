/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Tengoku

/-!
# `L^p` bounds for normalized convolution

The proof uses Jensen for `|·|^p`, translation invariance, and Tonelli.  The
result is the contraction estimate needed in the density argument for
mollification.
-/

@[expose] public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution

namespace CKN

noncomputable section

end

end CKN
