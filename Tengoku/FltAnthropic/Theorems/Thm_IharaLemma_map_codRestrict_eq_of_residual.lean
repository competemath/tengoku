import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.LinearAlgebra.Dimension.Torsion.Finite
import Tengoku.Seed.LinearAlgebra.Dimension.RankNullity
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.Seed.RingTheory.Noetherian.Basic
import Tengoku.Seed.LinearAlgebra.FreeModule.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_map_codRestrict_eq_of_residual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_map_codRestrict_eq_of_residual.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.7h9v.s11.2d46e39ab3c7 from=translated src=- shape=3fe92916 vocab=7e318cf0
-/
theorem IharaLemma.map_codRestrict_eq_of_residual {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] {W : Type} [AddCommGroup W] [Module B W] [Module 𝒪 W]
    [IsScalarTower 𝒪 B W] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Module.Finite 𝒪 W] [Module.Free 𝒪 W] {V : Type} [AddCommGroup V] [Module 𝒪 V]
    (i : V →ₗ[𝒪] W) (e : B)
    (hmem : ∀ v : V, i v ∈ (IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)
    (hi : Function.Injective i) {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : V) (x : W), i v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁)
    {A : Submodule 𝒪 V} (hA : ∀ (c : 𝒪) (x : V), c ≠ 0 → c • x ∈ A → x ∈ A)
    {Bc : Submodule 𝒪 ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)}
    (hle : Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A ≤ Bc)
    (hrank : Module.finrank 𝒪 Bc ≤ Module.finrank 𝒪 A) :
    Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A = Bc := by exact @_root_.P2MW.S_IharaLemma_map_codRestrict_eq_of_residual.solution 𝒪 _ B _ _ W _ _ _ _ _ _ _ _ V _ _ i e hmem hi ϖ hϖ hres A hA Bc hle hrank
