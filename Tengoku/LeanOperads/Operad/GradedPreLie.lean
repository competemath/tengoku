/-
# The graded pre-Lie identity

`Operad.PreLie` proves the *ungraded* identity: the associator of `⋆` is symmetric in its last
two arguments. `Operad.DG` introduces the signed product `⋆ₛ` of the operadic suspension. This
file combines them, proving the identity `⋆ₛ` actually satisfies:

`(α ⋆ₛ β) ⋆ₛ γ - α ⋆ₛ (β ⋆ₛ γ) = (-1)^(k l) [(α ⋆ₛ γ) ⋆ₛ β - α ⋆ₛ (γ ⋆ₛ β)]`

where `k` and `l` are the degrees of `β` and `γ`. Two facts make this a decoration of the
ungraded proof rather than a new one.

* Over the **nested** slots the signs cancel identically: the left side carries
  `(-1)^((a+c) l + a k)` and the right needs `(-1)^(a (k+l) + c l)`, and those exponents are
  equal on the nose. So `sum_nested` needs no sign correction at all.
* Over the **disjoint** slots each of the two index bijections contributes exactly `(-1)^(k l)`
  — the same factor in both the "before" and "after" cases.

So the whole sign of the identity is a single global factor, and the combinatorial scaffolding
of `Operad.PreLie` (`nested`, `before`, `after`, `sum_compl_nested`) is reused unchanged.
-/
import Tengoku.LeanOperads.Operad.DG
import Tengoku.LeanOperads.Operad.PreLie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

open NSOperad Finset

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-! ### Sign arithmetic -/

/-! ### Expanding the two bracketings -/

/-! ### The nested slots

Here the signs cancel exactly, so this is `compFin_assoc_seq` with a sign carried along
unchanged. -/

/-- The signed disjoint-slot part of the associator.-/
def disjointPartS {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    P (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ (nested (k := k) i)ᶜ,
    ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
      • compFin (R := R) i' (compFin (R := R) i α β) γ

/-! ### The two signed bijections

Each carries the global factor `(-1)^(k l)`, absorbed here into the exponent of the image term.
In the "before" case the two exponents differ by `2 k l`; in the "after" case they are equal on
the nose, because `(i' - k) l` already absorbs one `k l`. -/

/-! ### The identity -/

/-! ### Two equal arguments of degree one

When `β = γ = T` has degree one, the bijection of `sum_before_eq_s` carries each "before" term to
the "after" term with the same composite and the opposite sign. So the disjoint part vanishes
term by term, with no division by `2`. The graded pre-Lie identity alone would give only
`2 A(α, T, T) = 0`. -/

end Operad
