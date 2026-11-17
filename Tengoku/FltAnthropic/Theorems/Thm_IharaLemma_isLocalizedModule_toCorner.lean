import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_isLocalizedModule_toCorner

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_isLocalizedModule_toCorner.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IharaLemma.isLocalizedModule_toCorner {B : Type} [CommRing B] {M : Type}
    [AddCommGroup M] [Module B M] {e : B} (he : IsIdempotentElem e) (𝔪 : Ideal B)
    [h𝔪 : 𝔪.IsMaximal] (hem : e ∉ 𝔪) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) :
    IsLocalizedModule 𝔪.primeCompl (IharaLemma.toCorner (M := M) e) := by exact @_root_.P2MW.S_IharaLemma_isLocalizedModule_toCorner.solution B _ M _ _ e he 𝔪 h𝔪 hem hother
