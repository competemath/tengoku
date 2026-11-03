import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.PiRingModuleEquivalence
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedQuiverArrowBimodule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extracting separated-quiver arrows from a balanced action

The coordinate idempotents of `V → K` split an arbitrary top module and
radical module into vertex spaces.  Applying a balanced arrow-bimodule action
to an arrow basis vector then gives the corresponding map from the source top
coordinate to the target radical coordinate.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.SeparatedQuiverArrowExtraction

open QuotientSubmoduleEquidistribution.SeparatedQuiver
open QuotientSubmoduleEquidistribution.SeparatedQuiverArrowBimodule
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedData

universe uK uV v

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V] [Quiver.{v} V]
variable [∀ i j : V, Fintype (i ⟶ j)] [∀ i j : V, DecidableEq (i ⟶ j)]

abbrev CoordinatedSeparatedData :=
  SeparatedData.{max uK uV, max uK uV v, uV}
    (S := V → K) (J := ArrowBimodule K V)

end QuotientSubmoduleEquidistribution.SeparatedQuiverArrowExtraction
