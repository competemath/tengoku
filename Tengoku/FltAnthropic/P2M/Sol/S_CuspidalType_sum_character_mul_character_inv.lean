import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType
import Tengoku.Seed.RepresentationTheory.Character

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspidalType_sum_character_mul_character_inv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_CuspidalType_sum_character_mul_character_inv

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤) :
    ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q) := by
  classical
  haveI : Representation.IsIrreducible ρ :=
    { exists_pair_ne := ⟨⊥, ⊤, fun h => by
        have h' : (⊥ : Submodule K V) = ⊤ := congrArg Subrepresentation.toSubmodule h
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun W => by
        by_cases h : W.toSubmodule = ⊥
        · exact Or.inl (Subrepresentation.toSubmodule_injective h)
        · exact Or.inr (Subrepresentation.toSubmodule_injective (hirr W h)) }
  have hcard : (Nat.card (GL2 q) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI : Invertible (Nat.card (GL2 q) : K) := invertibleOfNonzero hcard
  have h := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at h
  have h2 := congrArg (fun x => (Nat.card (GL2 q) : K) * x) h
  rwa [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h2
