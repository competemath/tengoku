/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Data.PNat.Defs
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The bounded power describing an automorphism of roots of unity

The image of a primitive root is primitive. Its bounded exponent is therefore
coprime to the order and describes the action on every root at that order.
-/

namespace KummerTheory

/-- A field automorphism acts on all roots at a primitive-root level by
one bounded exponent coprime to that level.
@isnad1 id=ex.1h3v.s8.566689e082c8 from=translated src=- shape=00e76baa vocab=ce1ba360
-/
theorem exists_bounded_coprime_power_action_on_roots
    (K : Type*) [Field K] (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (τ : K ≃+* K) :
    ∃ a : ℕ, a < (n : ℕ) ∧ a.Coprime (n : ℕ) ∧
      ∀ ζ : K, ζ ^ (n : ℕ) = 1 → τ ζ = ζ ^ a := by
  obtain ⟨μ, hμmem⟩ := hmu
  have hμ : IsPrimitiveRoot μ (n : ℕ) := isPrimitiveRoot_of_mem_primitiveRoots hμmem
  obtain ⟨a, ha, hcop, haction⟩ := hμ.isPrimitiveRoot_iff.mp
    (hμ.map_of_injective τ.injective)
  refine ⟨a, ha, hcop, ?_⟩
  intro ζ hζ
  obtain ⟨i, _hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hζ
  rw [map_pow, ← haction, pow_right_comm]

end KummerTheory
