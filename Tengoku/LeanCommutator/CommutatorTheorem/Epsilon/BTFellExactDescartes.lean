import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellTaylorCount
import Tengoku.Seed.Algebra.Polynomial.Inductions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact Descartes count for real-rooted polynomials

For a monic polynomial all of whose roots are real, Descartes' upper bound is
an equality.  The proof combines the localized Rolle sandwiches with the
endpoint parity rule.  A zero constant coefficient is removed by `divX`.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellExactDescartes

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellRolleCount
open CommutatorTheorem.BTFellDescartes
open CommutatorTheorem.BTFellTaylorCount
open CommutatorTheorem.BTFellCrossGap

end CommutatorTheorem.BTFellExactDescartes
