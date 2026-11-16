import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=linearin.5h6v.s10.76fdc73a1c9d from=translated src=- shape=7f31ff42 vocab=3598d825
-/
theorem Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      (∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K)) ∧
      Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (s : Finset (Localization.AtPrime 𝔮)) (hs : LinearIndepOn k _root_.id (s : Set (Localization.AtPrime 𝔮))) :
    LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮)) := by exact @_root_.P2MW.S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.solution k _ B _ _ _ _ p hp _ S hdense hsep 𝔮 _ h𝔮 s hs
