import Tengoku.TuzaLean.Tuza.Construction.FirstCover
import Tengoku.TuzaLean.Tuza.Construction.BookCover
import Tengoku.TuzaLean.Tuza.Construction.ColoredCover
import Tengoku.TuzaLean.Tuza.Basic.Graph
import Tengoku.TuzaLean.Tuza.Construction.RandomCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Four covers of the same graph give the bound 165/59. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

theorem first_cover :
    transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card :=
  FirstCover.transversalNumber_add_typeOne_packing_le c.initial_maximum c.first_maximum.1

end Construction

end Tuza
