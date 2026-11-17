import Tengoku.StringDiagramsLean.StringDiagrams.Examples.FreeDots
import Tengoku.StringDiagramsLean.StringDiagrams.LocalInterpretation
import Tengoku.Seed.Algebra.MvPolynomial.CommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The polynomial representation of free commuting dots

Every object of `FD R` is sent to the polynomial ring `MvPolynomial ℕ R`, and a dot with `i`
strands to its left acts by multiplication by `X i`. This is an interpretation by local
operators with a single module for all objects (`StringDiagrams.LocalInterpretation.uniform`);
there are no defining relations, and the interchange law holds because multiplication
operators commute (`LocalInterpretation.evalW_interchange_eq_zero_of_comm`).

## Main declarations

* `FreeDots.polyLocal R`, `FreeDots.polyRep R : FD R ⥤ ModuleCat R` (an `R`-linear functor),
  with `polyRep_map_x`: a dot on strand `i` acts by multiplication by `X i`.
* Non-vacuity over a nontrivial ring: dots are nonzero (`x_ne_zero`) and dots on distinct
  strands are distinct (`x_ne_x`).
-/

noncomputable section

namespace StringDiagrams.FreeDots

open CategoryTheory MvPolynomial LocalInterpretation

universe u

variable (R : Type u) [CommRing R]

/-- Multiplication by the variable `X i`.-/
def mulX (i : ℕ) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R := LinearMap.mulLeft R (X i)

/--
@isnad1 id=eq.0h3v.s7.277e4d894d8a from=translated src=- shape=1148858c vocab=faf09365
-/
@[simp] theorem mulX_apply (i : ℕ) (f : MvPolynomial ℕ R) : mulX R i f = X i * f := rfl

/-- The operator of a layer: multiplication by the variable indexed by the number of strands
to the left of the dot.-/
def layerOp (L : Layer sig) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R :=
  mulX R L.left.length

/-- The polynomial representation as an interpretation by local operators, with a single
module for all objects.-/
def polyLocal :
    LocalInterpretation sig R (MvPolynomial ℕ R) (fun _ : Unit => MvPolynomial ℕ R) :=
  uniform (layerOp R)

end StringDiagrams.FreeDots

end
