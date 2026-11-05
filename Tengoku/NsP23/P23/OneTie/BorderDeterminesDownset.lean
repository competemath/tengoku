import Tengoku.NsP23.P23.OneTie.ThreeBorderGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.OneTie
open P23.Artin
variable {a b c : ℕ} [NeZero a]

/--
@isnad1 id=eq.4h5v.s6.eb594a77425c from=translated src=- shape=710279c2 vocab=cc6a8755
-/
theorem standardSet_eq_of_borderFinset_eq {S T : Finset (Normal a b c)}
    (hS : S.Nonempty) (hT : T.Nonempty) (hd : IsLiveParameterDomain a b c)
    (he : borderFinset S = borderFinset T) : standardSet S = standardSet T := by
  ext p
  rw [standard_iff_no_border_divisor S hS hd,
    standard_iff_no_border_divisor T hT hd,he]

/--
@isnad1 id=eq.4h5v.s6.8c57d12b8040 from=translated src=- shape=616349c1 vocab=16ab07c0
-/
theorem rootFinset_eq_of_standardSet_eq {S T : Finset (Normal a b c)}
    (hd : IsLiveParameterDomain a b c) (hS : IsRootAntichain S)
    (hT : IsRootAntichain T) (he : standardSet S = standardSet T) : S = T :=
  Finset.Subset.antisymm (roots_subset_of_standardSet_eq hd hS he)
    (roots_subset_of_standardSet_eq hd hT he.symm)

end P23.OneTie
