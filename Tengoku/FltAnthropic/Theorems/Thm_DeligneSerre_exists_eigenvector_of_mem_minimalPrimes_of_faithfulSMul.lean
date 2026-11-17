import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Localization
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Noetherian
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
import Tengoku.FltAnthropic.P2M.Sol.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h4v.s9.504c33a058f5 from=translated src=- shape=7e5263a8 vocab=1f19a018
-/
theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by exact @_root_.P2MW.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.solution K _ _ V _ _ _ T _ _ _ _ 𝔭 h𝔭
