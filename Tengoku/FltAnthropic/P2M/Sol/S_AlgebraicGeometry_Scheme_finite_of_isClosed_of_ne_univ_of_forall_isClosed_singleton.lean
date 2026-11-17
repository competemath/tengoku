import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
@isnad1 id=finite.3h2v.s7.8e344df37fdd from=translated src=- shape=afb00197 vocab=326691c2
-/
theorem solution
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (hdim : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) :
    ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite := by
  intro Z hZ hne
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine Set.Finite.sUnion hSfin fun t ht => ?_

  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hSclosed t ht)
  have hzne : z ≠ genericPoint X := by
    rintro rfl
    apply hne
    apply Set.eq_univ_of_univ_subset
    calc Set.univ = closure ({genericPoint X} : Set X) := (genericPoint_closure X).symm
      _ = t := hz.def
      _ ⊆ ⋃₀ S := Set.subset_sUnion_of_mem ht
  have ht1 : t = {z} := by rw [← hz.def, (hdim z hzne).closure_eq]
  rw [ht1]
  exact Set.finite_singleton z
