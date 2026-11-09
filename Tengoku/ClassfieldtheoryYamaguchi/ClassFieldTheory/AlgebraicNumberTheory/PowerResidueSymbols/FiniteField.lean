/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Group.Subgroup.Finite
import Tengoku.Seed.FieldTheory.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Power-residue symbols over finite fields

For a finite field `k` of cardinality `q` and `n ∣ q - 1`, the tame
power-residue symbol is

`u ↦ u ^ ((q - 1) / n)`.

Its kernel is exactly the subgroup of `n`-th powers.
-/

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

variable (k : Type*) [Field k] [Fintype k]

/-- The finite-field `n`-th power-residue symbol.-/
def finiteFieldPowerResidueSymbol
    (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card k - 1) :
    kˣ →* rootsOfUnity (n : ℕ) k where
  toFun u :=
    ⟨u ^ ((Fintype.card k - 1) / (n : ℕ)), by
      change (u ^ ((Fintype.card k - 1) / (n : ℕ))) ^ (n : ℕ) = 1
      rw [← pow_mul, Nat.div_mul_cancel hn]
      apply Units.ext
      exact FiniteField.pow_card_sub_one_eq_one
        (u : k) (Units.ne_zero u)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp [mul_pow]

/--
@isnad1 id=eq.1h3v.s10.8ee6c245e331 from=translated src=- shape=4e01e35f vocab=49f46c1e
-/
@[simp]
theorem finiteFieldPowerResidueSymbol_apply
    (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card k - 1) (u : kˣ) :
    ((finiteFieldPowerResidueSymbol k n hn u :
        rootsOfUnity (n : ℕ) k) : kˣ) =
      u ^ ((Fintype.card k - 1) / (n : ℕ)) :=
  rfl

end PowerResidueSymbols
end AlgebraicNumberTheory
