import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_isLocalizedModule_comap_primeCompl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_isLocalizedModule_comap_primeCompl.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=islocali.1h6v.s9.6938d62e3ea0 from=translated src=- shape=856c47de vocab=909faae0
-/
theorem IharaLemma.isLocalizedModule_comap_primeCompl {Λ B : Type*} [CommRing Λ] [CommRing B] [Algebra Λ B]
    (hπ : Function.Surjective (algebraMap Λ B))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N] [Module Λ M] [Module Λ N]
    [IsScalarTower Λ B M] [IsScalarTower Λ B N]
    (f : M →ₗ[B] N) [IsLocalizedModule 𝔭.primeCompl f] :
    IsLocalizedModule (𝔭.comap (algebraMap Λ B)).primeCompl (f.restrictScalars Λ) := by exact @_root_.P2MW.S_IharaLemma_isLocalizedModule_comap_primeCompl.solution Λ B _ _ _ hπ 𝔭 _ M N _ _ _ _ _ _ _ _ f _
