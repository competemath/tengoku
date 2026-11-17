import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

universe u

/--
@isnad1 id=mem.2h5v.s14.8fc47efe5683 from=translated src=- shape=535b6e8b vocab=faf73bc9
-/
theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Flat f]
    (r : R) (hr : r ∈ nonZeroDivisors R) (U : Y.Opens) (hU : IsAffineOpen U) :
    Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      ∈ nonZeroDivisors Γ(Y, U) := by
  have happ : Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [happ]
  have hflat : (f.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ ⟨U, hU⟩ le_top

  let e : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let φ : R →+* Γ(Y, U) := (f.appLE ⊤ U le_top).hom.comp e.toRingHom
  have hφflat : φ.Flat := (RingHom.Flat.of_bijective e.bijective).comp hflat
  letI := φ.toAlgebra
  haveI : Module.Flat R Γ(Y, U) := hφflat
  have hreg : IsSMulRegular Γ(Y, U) r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have hφr : φ r = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := rfl
  rw [← hφr]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  show r • x = r • (0 : Γ(Y, U))
  rw [smul_zero, Algebra.smul_def]
  show φ r * x = 0
  rw [mul_comm]; exact hx
