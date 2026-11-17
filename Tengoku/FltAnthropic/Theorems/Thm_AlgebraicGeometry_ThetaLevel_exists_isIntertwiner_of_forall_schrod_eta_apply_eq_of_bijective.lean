import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

/--
@isnad1 id=ex.8h10v.s10.cf80fb3daa91 from=translated src=- shape=0e559446 vocab=cabff496
-/
theorem AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (v : HH δ → B) (hv : ∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) v = v)
    (hbij : Function.Bijective fun c : HH δ → B => ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v) :
    ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U := by exact @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective.solution g δ _ d _ hδd B _ hd ζ ω hζ hζu hω n e γ hγ v hv hbij
