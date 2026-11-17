import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=ex.3h3v.s8.5e86ce5b6961 from=translated src=- shape=b7995c26 vocab=324d7d1b
-/
theorem solution
    {X : Scheme.{u}} (S : Set X) (hS : S.Finite) (hcl : ∀ s ∈ S, IsClosed ({s} : Set X))
    (x : X) (hx : x ∉ S) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Disjoint (V : Set X) S := by
  classical
  have hSc : IsClosed S := by
    have h : S = ⋃ s ∈ S, ({s} : Set X) := (Set.biUnion_of_singleton S).symm
    rw [h]
    exact hS.isClosed_biUnion fun s hs => hcl s hs
  let U : X.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hxU : x ∈ U := hx
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  exact ⟨V, hV, hxV, Set.disjoint_left.mpr fun z hz hzS => (hVU hz) hzS⟩
