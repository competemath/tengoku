import Tengoku.LanaHeights.Heights.WeierstrassFibers
import Tengoku.LanaHeights.Heights.LatticePointMapNegation
import Tengoku.LanaHeights.Heights.LatticePointMapTopology
import Tengoku.LanaHeights.Heights.LatticeQuotientCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Injectivity of the lattice point map

The fiber theorem for `(℘, ℘′)` proves that the total point-valued
Weierstrass map identifies exactly the complex numbers differing by a period.
It follows immediately that the descended map from `ℂ/L` to the explicit
elliptic curve is injective.

This is one half of set-theoretic uniformization. Combined with the existing
continuity theorem and compact/Hausdorff instances, it also makes the wrapped
descended map a closed topological embedding. Surjectivity, the Weierstrass
addition theorem, group-law compatibility, and an arbitrary-curve
uniformization theorem remain open.
-/

open scoped UpperHalfPlane
noncomputable section
namespace Heights

open Topology

end Heights
