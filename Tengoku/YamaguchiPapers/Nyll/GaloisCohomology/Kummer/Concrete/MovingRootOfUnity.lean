/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Data.PNat.Defs
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moving a root of unity outside the base field

If not all roots of a given order lie in the base field of a finite Galois
extension, a primitive root is moved by an actual Galois automorphism.
-/

namespace KummerTheory

variable (L E : Type*) [Field L] [Field E] [Algebra L E]
  [FiniteDimensional L E] [IsGalois L E]

/-- A primitive root is moved by a Galois automorphism when the roots at its
level do not all come from the base field.
@isnad1 id=ex.2h3v.s8.ec511ec3cdbe from=translated src=- shape=a9fbdb5b vocab=17e6bc70
-/
theorem exists_moving_primitiveRoot_of_not_all_roots_in_base
    (m : ℕ+) (hmu : (primitiveRoots (m : ℕ) E).Nonempty)
    (hnot : ¬ ∀ ξ : E, ξ ^ (m : ℕ) = 1 →
      ξ ∈ Set.range (algebraMap L E)) :
    ∃ (ζ : E) (τ : Gal(E/L)), IsPrimitiveRoot ζ (m : ℕ) ∧ τ ζ ≠ ζ := by
  classical
  obtain ⟨ζ, hζmem⟩ := hmu
  have hζ : IsPrimitiveRoot ζ (m : ℕ) :=
    isPrimitiveRoot_of_mem_primitiveRoots hζmem
  have hout : ζ ∉ Set.range (algebraMap L E) := by
    rintro ⟨z, hz⟩
    apply hnot
    intro ξ hξ
    obtain ⟨i, _hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hξ
    refine ⟨z ^ i, ?_⟩
    rw [map_pow, hz, hpow]
  have hnotfixed : ¬ ∀ τ : Gal(E/L), τ ζ = ζ := by
    intro hfixed
    exact hout ((IsGalois.mem_range_algebraMap_iff_fixed ζ).mpr hfixed)
  obtain ⟨τ, hτ⟩ := not_forall.mp hnotfixed
  exact ⟨ζ, τ, hζ, hτ⟩

end KummerTheory
