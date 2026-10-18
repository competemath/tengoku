/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.ArithTraces
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Markov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Takeuchi's classification of arithmetic `(1;∞)`-groups (necessity)

Let `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2`, so that `Γ = ⟨A, B⟩` is (the preimage in `SL(2, ℝ)`
of) a Fuchsian group of signature `(1;∞)`: the fundamental group of a once-punctured torus, with
the commutator going around the puncture. If `Γ` is arithmetic, then some generating pair
`(A', B')` of `Γ` (obtained from `(A, B)` by Nielsen moves) has squared trace triple

  `(tr² A', tr² B', tr² A'B') ∈ {(9,9,9), (8,8,16), (5,20,25), (6,12,18)}`,

that is, trace triple `(3,3,3)`, `(2√2,2√2,4)`, `(√5,2√5,5)` or `(√6,2√3,3√2)` up to signs.
This is the "only if" half of K. Takeuchi, *Arithmetic Fuchsian groups with signature (1;e)*,
J. Math. Soc. Japan 35 (1983), Thm. 4.1(i), for `e = ∞`. Together with Fricke's theorem that the
trace triple determines the group up to conjugacy, it gives the four arithmetic once-punctured
tori of [CanLift] Prop. 2.7 and [EstIUT] Prop. 2.1.

## Proof

* `OrbicurveCores.IsArithmeticSL.sq_tr_int`: all `tr² γ`, `γ ∈ Γ`, are integers.
* Fricke: `x² + y² + z² = xyz` for `(x, y, z) = (tr A, tr B, tr AB)`.
* Nielsen moves `(A, B) ↦ (B, A)`, `(B, (AB)⁻¹)`, `(A⁻¹, B)` generate the same group and act on
  trace triples by permutations and Vieta flips `z ↦ xy - z`.
* Descent on `x² + y² + z² ∈ ℕ` reaches a reduced triple, which is classified by
  `OrbicurveCores.Markov.reduced_classification`.

The degenerate trace triple `(0, 0, 0)` on the Fricke surface belongs to a quotient of the
quaternion group of order 8 (every element has order dividing 4). It is excluded because an
arithmetic group contains elements of infinite order (`IsArithmeticSL.exists_pow_four_ne_one`).
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The trace triple `(x, y, z)` is *realised* in `Γ` if `Γ = ⟨A, B⟩` with `tr A = x`,
`tr B = y`, `tr AB = z`. -/
def Realizes (Γ : Subgroup SL(2, ℝ)) (x y z : ℝ) : Prop :=
  ∃ A B : SL(2, ℝ), Subgroup.closure {A, B} = Γ ∧ tr A = x ∧ tr B = y ∧ tr (A * B) = z

/-- The four squared trace triples of Takeuchi's arithmetic `(1;∞)`-groups. -/
def TakeuchiSq (x y z : ℝ) : Prop :=
  (x ^ 2 = 9 ∧ y ^ 2 = 9 ∧ z ^ 2 = 9) ∨ (x ^ 2 = 8 ∧ y ^ 2 = 8 ∧ z ^ 2 = 16) ∨
    (x ^ 2 = 5 ∧ y ^ 2 = 20 ∧ z ^ 2 = 25) ∨ (x ^ 2 = 6 ∧ y ^ 2 = 12 ∧ z ^ 2 = 18)

namespace Realizes

variable {Γ : Subgroup SL(2, ℝ)} {x y z : ℝ}

end Realizes

end OrbicurveCores
