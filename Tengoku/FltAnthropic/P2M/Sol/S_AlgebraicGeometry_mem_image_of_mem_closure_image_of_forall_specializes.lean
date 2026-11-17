import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

universe u

/--
@isnad1 id=mem.3h5v.s9.823c64a4b1ef from=translated src=- shape=1e75394c vocab=0f67389c
-/
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C :=
  (f.isConstructible_image hC).mem_of_mem_closure_of_forall_specializes hy
    (by rintro _ ⟨c, hc, rfl⟩; exact hgen c hc)
