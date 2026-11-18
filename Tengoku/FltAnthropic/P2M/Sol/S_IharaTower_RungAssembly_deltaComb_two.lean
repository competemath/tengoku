import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeModule_IharaRungDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaTower_RungAssembly_deltaComb_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaTower_RungAssembly_deltaComb_two

set_option autoImplicit false

open IharaTower IharaTower.RungAssembly

/--
@isnad1 id=eq.1h13v.s9.3e68a4f13083 from=translated src=- shape=968affd5 vocab=d1c4d2a4
-/
theorem solution {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    (L : LegDatum (𝒪 := 𝒪) P P' 2) (t₀₀ t₀₁ t₁₀ t₁₁ : T) (htab : L.table = ![![t₀₀, t₀₁], ![t₁₀, t₁₁]]) (c : Fin 2 → T) :
    deltaComb L c = c 0 ^ 2 * t₀₀ + c 0 * c 1 * (t₀₁ + t₁₀) + c 1 ^ 2 * t₁₁ := by
  simp only [deltaComb, htab, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
