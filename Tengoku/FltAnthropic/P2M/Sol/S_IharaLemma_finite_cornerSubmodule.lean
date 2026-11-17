import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.RingTheory.Finiteness.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_finite_cornerSubmodule.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_finite_cornerSubmodule

set_option autoImplicit false

open IharaLemma in
/--
@isnad1 id=finite.0h4v.s8.fe149485653a from=translated src=- shape=35eb52a5 vocab=917e51ca
-/
theorem solution {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
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
