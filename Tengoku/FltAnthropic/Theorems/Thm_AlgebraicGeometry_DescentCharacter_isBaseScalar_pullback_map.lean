import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_DescentCharacter
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

/--
@isnad1 id=isbasesc.2h11v.s7.2ef41440884d from=translated src=- shape=f30c4eb0 vocab=0e7e4d27
-/
theorem AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map
    {X X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c) := by exact @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map.solution X X' g R R' _ _ f f' φ hg M σ c hσ
