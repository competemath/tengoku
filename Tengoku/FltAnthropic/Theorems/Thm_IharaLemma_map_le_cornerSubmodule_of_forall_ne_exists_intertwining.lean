import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IharaLemma

/--
@isnad1 id=mem.3h10v.s10.aa6f45aaecea from=translated src=- shape=20e112b1 vocab=9bb063fd
-/
theorem IharaLemma.map_le_cornerSubmodule_of_forall_ne_exists_intertwining
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (W : Submodule 𝒪 V) (I : Ideal 𝒪)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ (I ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (hyp : ∀ j' : Fin S'.n, j' ≠ i' →
      ∃ (g : V →ₗ[𝒪] V) (b' : B'), b' ∉ S'.𝔪 j' ∧ (∀ v : V, f (g v) = b' • f v) ∧
        (∀ w ∈ W, g w ∈ W) ∧ (∀ k : ℕ, ∃ n : ℕ, ∀ w ∈ W, (g ^ n) w ∈ (I ^ k • ⊤ : Submodule 𝒪 V))) :
    ∀ w ∈ W, f w ∈ cornerSubmodule (M := V') (S'.e i') := by exact @_root_.P2MW.S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining.solution 𝒪 _ B' _ _ V _ _ V' _ _ _ _ f S' i' W I hsep hyp
