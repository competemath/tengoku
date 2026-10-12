/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSlice

/-!
# The slice bound of one field at every cell scale

A cell estimate for the parabolic Morrey class needs the radius factor
`r ^ (5 * (1 - P / κ))`, which a slice bound at one fixed scale cannot produce:
one ball's slice bound, integrated in time, carries no decay in the cell
radius.  What does produce it is the slice estimate applied at each cell's own
radius.

The statement below performs that transfer for one fixed space-time field.  The
field is tied to the pressure by being a weak spatial derivative on a common
open carrier at almost every time of the cell's window; the cell datum is a
slice bound for *some* weak spatial derivative on the cell's own ball.  Almost
everywhere uniqueness of weak partial derivatives then transports the cell's
bound to the one field.  Its conclusion is exactly the slice hypothesis of the
time integration that turns slice bounds into the cell power integral.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

end CKN.Core.Step4
