import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IrreducibleSpace_genericPoint_mem_range_of_denseRange.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IrreducibleSpace_genericPoint_mem_range_of_denseRange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
@isnad1 id=mem.2h3v.s5.fa9ba7d63468 from=translated src=- shape=e99be96c vocab=06cc4c0c
-/
theorem solution
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [QuasiSober X] [QuasiSober Y] [IrreducibleSpace Y] [T0Space Y]
    {f : X → Y} (hf : Continuous f) (hd : DenseRange f) :
    genericPoint Y ∈ Set.range f := by
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents

  have hrange : Set.range f = ⋃ Z ∈ irreducibleComponents X, f '' Z := by
    rw [← Set.image_univ, ← sUnion_irreducibleComponents, Set.image_sUnion, Set.sUnion_image]
  have hcl : closure (Set.range f) = ⋃ Z ∈ irreducibleComponents X, closure (f '' Z) := by
    rw [hrange, hfin.closure_biUnion]

  let t : Finset (Set Y) := hfin.toFinset.image fun Z => closure (f '' Z)
  have hcov : (Set.univ : Set Y) ⊆ ⋃₀ (↑t : Set (Set Y)) := by
    intro y _
    have hy : y ∈ closure (Set.range f) := by rw [hd.closure_range]; trivial
    rw [hcl, Set.mem_iUnion₂] at hy
    obtain ⟨Z, hZ, hyZ⟩ := hy
    refine Set.mem_sUnion.mpr ⟨closure (f '' Z), ?_, hyZ⟩
    simp only [t, Finset.coe_image, Set.Finite.coe_toFinset]
    exact ⟨Z, hZ, rfl⟩
  obtain ⟨z, hz, hz'⟩ := (isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ Y)) t
    (by
      intro z hz
      simp only [t, Finset.mem_image, Set.Finite.mem_toFinset] at hz
      obtain ⟨Z, -, rfl⟩ := hz
      exact isClosed_closure) hcov
  simp only [t, Finset.mem_image, Set.Finite.mem_toFinset] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz

  have hgen : IsGenericPoint (f hZ.1.genericPoint) (closure (f '' Z)) :=
    (hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).image hf
  rw [Set.eq_univ_of_univ_subset hz'] at hgen
  exact ⟨_, hgen.eq (genericPoint_spec Y)⟩
