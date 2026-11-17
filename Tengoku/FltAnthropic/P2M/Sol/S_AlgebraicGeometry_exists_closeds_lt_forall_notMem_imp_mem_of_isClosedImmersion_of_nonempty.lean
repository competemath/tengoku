import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/--
@isnad1 id=ex.2h5v.s9.ea2338105a34 from=translated src=- shape=f284c3fe vocab=24fbd789
-/
theorem solution
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : Closeds X) (hT : Set.range i.base = (T : Set X))
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' := by
  have hce : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  refine ⟨⟨i.base '' ((U : Set Z)ᶜ), hce.isClosedMap _ U.isOpen.isClosed_compl⟩, ?_, fun z hz => ⟨z, hz, rfl⟩⟩
  rw [SetLike.lt_iff_le_and_exists]
  obtain ⟨u, hu⟩ := hU
  refine ⟨?_, i.base u, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := (Closeds.mem_mk).mp hx
    have : i.base z ∈ (T : Set X) := hT ▸ ⟨z, rfl⟩
    exact this
  · have : i.base u ∈ (T : Set X) := hT ▸ ⟨u, rfl⟩
    exact this
  · intro h
    obtain ⟨z, hz, hzu⟩ := (Closeds.mem_mk).mp h
    exact hz (by rwa [hce.injective hzu])
