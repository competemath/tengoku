import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f g : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.basicOpen 𝒜 (f * g) =
      (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg)) := by exact @_root_.P2MW.S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.solution A σ _ _ _ 𝒜 _ f g m m' f_deg hm g_deg hm'
