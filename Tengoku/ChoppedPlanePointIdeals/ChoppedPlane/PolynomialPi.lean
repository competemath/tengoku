module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.RankOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section
namespace ChoppedPlane
variable {K ι J V : Type*} [Field K] [Fintype J]
  [AddCommGroup V] [Module K V]

/-- A finite tuple of polynomial vector families is a polynomial family.-/
theorem IsPolynomialFamily.finite_pi {f : (ι → K) → J → V}
    (hf : ∀ j, IsPolynomialFamily (fun a => f a j)) : IsPolynomialFamily f := by
  classical
  have h := IsPolynomialFamily.sum (fun j =>
    (hf j).linear_comp (LinearMap.single K (fun _ : J => V) j))
  convert h using 1
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

end ChoppedPlane
