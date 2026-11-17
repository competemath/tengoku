import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

/--
@isnad1 id=ex.3h3v.s9.318dac11c129 from=translated src=- shape=67551871 vocab=2324d2ce
-/
theorem WittVector.exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ e : WittVector p k ≃+* 𝓞,
      (algebraMap 𝓞 k).comp e.toRingHom = WittVector.constantCoeff ∧
      ∀ g : WittVector p k →+* 𝓞,
        (algebraMap 𝓞 k).comp g = WittVector.constantCoeff → g = e.toRingHom := by exact @_root_.P2MW.S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete.solution 𝓞 _ p _ hp k _ _ _ _ hk hker _
