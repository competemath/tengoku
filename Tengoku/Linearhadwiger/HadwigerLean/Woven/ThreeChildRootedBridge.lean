import Tengoku.Linearhadwiger.HadwigerLean.Woven.ThreeChildLinkage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linked-complement bridge for the three woven children

The parent roots have two distinct neighbors each. After those roots are
deleted, a `2a`-linked graph connects the neighbors to one selected root
in every child branch. The existing three-child assembly then yields a
rooted `K_a` model at the parent roots.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

end Woven
end HadwigerLean
