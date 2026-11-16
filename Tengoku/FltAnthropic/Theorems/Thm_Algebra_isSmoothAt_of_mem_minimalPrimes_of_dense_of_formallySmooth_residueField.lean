import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=issmooth.3h4v.s9.4d9a8ae53103 from=translated src=- shape=9e33e2cb vocab=da29cf8b
-/
theorem Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k 𝔮 := by exact @_root_.P2MW.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.solution k _ B _ _ _ _ S hdense hsep 𝔮 _ h𝔮
