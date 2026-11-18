import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_DeligneRapoport
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=or.7h10v.s10.16c5c5c0e19a from=translated src=- shape=e866e5c0 vocab=c258796a
-/
theorem ModularCurve.mazurPrinciple_toric_exclusion_of_scalar
    {G : Type*} [Group G]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    {q : ℕ} {φ : G} {𝒯 : Submodule R J}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ 𝒯)
    (lam : k) (hscalar : ∀ v : V, φ • v = lam • v)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k)) :
    (q : k) = 0 ∨ (q : k) = 1 := by exact @_root_.P2MW.S_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.solution G _ k _ V _ _ _ _ R _ J _ _ _ q φ 𝒯 hfrob ι hinj hequiv hsub lam hscalar hrank hdet
