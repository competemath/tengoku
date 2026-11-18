import Tengoku.Tiling.Tiling.AxisParallel.SetFormulation.Definitions
import Tengoku.Tiling.Tiling.Geometry.FiniteLocalComplexity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Set formulations of packing, tiling, and periodicity

This module connects predicates on sets to their structured
counterparts. It imports no challenge statements.
-/

set_option autoImplicit false

open Bornology Set
open scoped Pointwise

namespace Tiling.AxisParallel.SetFormulation

/--
@isnad1 id=isopen.1h2v.s4.a97c25d3df6c from=translated src=- shape=93e860ac vocab=f0dbd148
-/
theorem isRegularOpen_isOpen {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsRegularOpen U) : IsOpen U := by
  rw [← hU]
  exact isOpen_interior

/--
@isnad1 id=iff.0h2v.s5.d44efe27c12c from=translated src=- shape=d805fd2a vocab=0e248f1a
-/
theorem isPeriod_iff_mem_periodGroup (A : Set Plane) (p : Plane) :
    IsPeriod A p ↔ p ∈ Tiling.Polygonal.periodGroup A := by
  exact AddAction.mem_stabilizer_iff.symm

/--
@isnad1 id=iff.0h2v.s5.1fbe734e3ffe from=translated src=- shape=7e4ed5d3 vocab=5ee60652
-/
theorem isPeriod_iff_membership (A : Set Plane) (p : Plane) :
    IsPeriod A p ↔ ∀ x, x + p ∈ A ↔ x ∈ A := by
  constructor
  · intro hp x
    have hmem := congrArg (fun S : Set Plane => p + x ∈ S) hp
    simpa [IsPeriod, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm] using hmem.symm
  · intro hp
    apply Set.ext
    intro x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using (hp (-p + x)).symm

/--
@isnad1 id=iff.0h2v.s4.efbffe3c71d9 from=translated src=- shape=18cb2c77 vocab=fe6938f5
-/
theorem hasFiniteLocalComplexity_iff_hasFLC
    {V : Type*} [NormedAddCommGroup V] {T : Set V} :
    HasFiniteLocalComplexity T ↔ Tiling.Polygonal.HasFLC T :=
  Tiling.Polygonal.hasFLC_iff_finite_differences_on_bounded.symm

/--
@isnad1 id=hasfinit.2h3v.s4.3f354a9b02e8 from=translated src=- shape=9ba8899d vocab=50bc2ed0
-/
theorem hasFiniteLocalComplexity_mono
    {V : Type*} [NormedAddCommGroup V] {S T : Set V}
    (hT : HasFiniteLocalComplexity T) (hST : S ⊆ T) :
  HasFiniteLocalComplexity S := by
  intro B hB
  exact (hT B hB).subset
    (inter_subset_inter_left B (Set.sub_subset_sub hST hST))

end Tiling.AxisParallel.SetFormulation
