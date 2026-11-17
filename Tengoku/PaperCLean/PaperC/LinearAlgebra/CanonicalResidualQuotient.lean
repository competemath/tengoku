import Tengoku.PaperCLean.PaperC.Affine.CanonicalRationalCode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical residual quotient

This module records the literal quotient-space interpretation of the
residual dimension from Section 6.  The canonical rational code is already
a submodule of the full relation space, so no ambient-space transport is
needed to form the quotient:

`R(x,y) / S_rat(x,y)`.

Its dimension is exactly `residualTau = ρ - σ`.
-/

namespace PaperC
namespace CanonicalResidualQuotient

open Affine
open Affine.CanonicalRationalCode

noncomputable section

/-- The literal residual quotient `R(x,y) / S_rat(x,y)`.-/
abbrev ResidualQuotient
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :=
  RelationSpace (twoStartSystem M x y L) ⧸
    canonicalRationalCode M A x y L hx hy

/--
The manuscript's residual dimension `τ = ρ - σ` is exactly the dimension
of the quotient of the full relation space by the canonical rational code.
@isnad1 id=eq.2h5v.s11.87d61758d54d from=translated src=- shape=d25cf96d vocab=3e79fe6f
-/
theorem residualTau_eq_finrank_residualQuotient
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    residualTau M A x y L hx hy =
      Module.finrank F₂
        (ResidualQuotient M A x y L hx hy) := by
  rw [Submodule.finrank_quotient]
  rfl

end

end CanonicalResidualQuotient
end PaperC
