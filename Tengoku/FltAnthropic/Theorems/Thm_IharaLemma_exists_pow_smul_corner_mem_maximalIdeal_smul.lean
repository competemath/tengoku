import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Finiteness.Defs
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IharaLemma

/--
@isnad1 id=ex.1h7v.s9.83d17d5b6f15 from=translated src=- shape=04c72f6a vocab=42a3b58a
-/
theorem IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (S : IdempotentSplitting B) (i : Fin S.n) (b : B) (hb : b ∈ S.𝔪 i)
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V] (k : ℕ) :
    ∃ n : ℕ, ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) →
      (b ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by exact @_root_.P2MW.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul.solution 𝒪 _ _ B _ _ _ S i b hb V _ _ _ _ k
