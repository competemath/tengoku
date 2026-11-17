import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType
import Tengoku.Seed.RepresentationTheory.Character

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspidalType_character_scalar_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_CuspidalType_character_scalar_mul

set_option autoImplicit false

open CuspidalType

/--
@isnad1 id=eq.1h6v.s10.faa4f6d649cd from=translated src=- shape=3aa12072 vocab=fa75841b
-/
theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (c : (ZMod q)ˣ) (g : GL2 q) :
    ρ.character (scalarElem q c * g) = ρ.character g := by
  simp only [Representation.character, map_mul, hcent c, Module.End.mul_eq_comp, LinearMap.id_comp]
