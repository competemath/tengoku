import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ClopenPieceFiniteEtaleSol

lemma isFinite_of_isOpenImmersion_of_isClosed_range {V U : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
    (hi : IsClosed (Set.range i.base)) : IsFinite i :=
  have : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i hi
  inferInstance

end ClopenPieceFiniteEtaleSol

open ClopenPieceFiniteEtaleSol in
theorem solution
    {V U X : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (hi : IsClosed (Set.range i.base))
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π] :
    IsFinite (i ≫ π) ∧ AlgebraicGeometry.Etale (i ≫ π) :=
  have : IsFinite i := isFinite_of_isOpenImmersion_of_isClosed_range i hi
  ⟨inferInstance, inferInstance⟩
