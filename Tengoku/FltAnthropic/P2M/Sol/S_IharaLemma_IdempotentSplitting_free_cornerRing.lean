import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.Algebra.Module.Projective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_IdempotentSplitting_free_cornerRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_IdempotentSplitting_free_cornerRing

set_option autoImplicit false

private theorem toCorner_comp_subtype_module {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) (he : IsIdempotentElem e) :
    ((IharaLemma.toCorner (M := V) e).restrictScalars 𝒪).comp
      ((IharaLemma.cornerSubmodule (M := V) e).subtype.restrictScalars 𝒪) = LinearMap.id := by
  ext x
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hy
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.id_coe, id_eq, IharaLemma.toCorner_apply]
  rw [← hy, smul_smul, he.eq]

private theorem finite_cornerSubmodule_of_finite {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) [Module.Finite 𝒪 V] :
    Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by
  have h : (IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪
      = LinearMap.range ((e • (LinearMap.id : V →ₗ[B] V)).restrictScalars 𝒪) := by
    ext v
    simp only [Submodule.restrictScalars_mem, IharaLemma.cornerSubmodule, LinearMap.mem_range,
      LinearMap.coe_restrictScalars]
  rw [show (Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e))
      = Module.Finite 𝒪 ↥((IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪) from rfl, h]
  exact Module.Finite.range _

open IharaLemma in
theorem solution {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [IsLocalRing 𝒪] [Module.Finite 𝒪 B] [Module.Free 𝒪 B] :
    Module.Free 𝒪 (S.CornerRing i) := by
  haveI : Module.Projective 𝒪 ↥(cornerSubmodule (M := B) (S.e i)) :=
    Module.Projective.of_split
      ((cornerSubmodule (M := B) (S.e i)).subtype.restrictScalars 𝒪)
      ((toCorner (M := B) (S.e i)).restrictScalars 𝒪)
      (toCorner_comp_subtype_module (𝒪 := 𝒪) (S.e i) (S.idem i))
  haveI : Module.Finite 𝒪 ↥(cornerSubmodule (M := B) (S.e i)) :=
    finite_cornerSubmodule_of_finite (S.e i)
  haveI : Module.Free 𝒪 ↥(cornerSubmodule (M := B) (S.e i)) :=
    Module.free_of_flat_of_isLocalRing
  exact Module.Free.of_equiv (S.cornerRingLinearEquiv i 𝒪).symm
