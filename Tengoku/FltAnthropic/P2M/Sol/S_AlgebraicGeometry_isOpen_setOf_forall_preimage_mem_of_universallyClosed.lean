import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=isopen.0h6v.s8.0f2100b28d92 from=translated src=- shape=0df932bc vocab=49115f3e
-/
theorem solution
    {Z T Y : Scheme.{u}} (π : Z ⟶ T) [UniversallyClosed π] (φ : Z ⟶ Y) (V : Y.Opens) :
    IsOpen {t : T | ∀ z : Z, π.base z = t → φ.base z ∈ V} := by
  have hset : {t : T | ∀ z : Z, π.base z = t → φ.base z ∈ V} = (π.base '' ((φ.base ⁻¹' (V : Set Y))ᶜ))ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and, SetLike.mem_coe]
    constructor
    · intro h z hz hzt; exact hz (h z hzt)
    · intro h z hzt; by_contra hz; exact h z hz hzt
  rw [hset, isOpen_compl_iff]
  refine π.isClosedMap _ ?_
  exact (V.isOpen.preimage φ.continuous).isClosed_compl
