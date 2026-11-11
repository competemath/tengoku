module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.SingularLinearAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: choosing the singular class in a character component

This file proves the final elementary choice step after component surjectivity:
if the projected target component of `A[p]` is nontrivial, then the matching
projected component of the singular group contains a class with nontrivial
image in `A[p]`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace LinearComponentChoice

variable {R M N : Type*} [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- Linear analogue of the component-lifting lemma.  If a linear map sends a
source submodule onto a nontrivial target submodule, then some element of the
source submodule has nonzero image.-/
theorem exists_lift_of_map_eq_of_ne_bot
    (f : M →ₗ[R] N) (S : Submodule R M) (T : Submodule R N)
    (hmap : S.map f = T) (hT : T ≠ ⊥) :
    ∃ x : S, f x.1 ≠ 0 := by
  have : Nontrivial T := (Submodule.nontrivial_iff_ne_bot).2 hT
  obtain ⟨y, hy_ne⟩ := exists_ne (0 : T)
  have hy_map : y.1 ∈ S.map f := by
    simp [hmap, y.2]
  obtain ⟨x, hxS, hx⟩ := hy_map
  refine ⟨⟨x, hxS⟩, ?_⟩
  intro hx_zero
  exact hy_ne (Subtype.ext <| hx.symm.trans hx_zero)

/-- Elementwise form of the linear component-lifting lemma.-/
theorem exists_mem_lift_with_nonzero_image_of_ne_bot
    (f : M →ₗ[R] N) (S : Submodule R M) (T : Submodule R N)
    (hmap : S.map f = T) (hT : T ≠ ⊥) :
    ∃ x : M, x ∈ S ∧ f x ∈ T ∧ f x ≠ 0 := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot f S T hmap hT
  refine ⟨x.1, x.2, ?_, hx_ne⟩
  rw [← hmap]
  exact ⟨x.1, x.2, rfl⟩

end LinearComponentChoice

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
