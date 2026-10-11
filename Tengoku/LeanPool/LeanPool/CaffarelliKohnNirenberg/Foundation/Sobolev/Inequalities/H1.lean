/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.Product
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormLeVecEuclidean

/-!
# Local Sobolev and interpolation inequalities for `H¹` representatives
The proof first multiplies the representative by the canonical compactly supported cutoff
inside the outer ball.  The product rule gives a global weak gradient for this zero extension;
global mollification then supplies smooth functions, and Fatou's lemma passes the estimate to the
representative.  This preserves the absolute constant from the smooth estimate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Convolution
namespace CKN
noncomputable section
/-- The extended `Lᵖ` seminorm of a chosen weak gradient on a set. -/
def weakGradientLpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (Du : Vec 3 → Vec 3) : ℝ≥0∞ :=
  eLpNorm Du p (volume.restrict s)

end
end CKN
