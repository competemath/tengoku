/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBall
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Tengoku

/-!
# Sobolev Poincare Ball Weak

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

end
end CKN
