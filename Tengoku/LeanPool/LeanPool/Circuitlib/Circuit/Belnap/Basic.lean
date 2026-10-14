/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Tengoku.LeanPool.LeanPool.Circuitlib.Circuit.Belnap.Level
public import Tengoku.LeanPool.LeanPool.Circuitlib.Circuit.Wires

/-! # Belnap circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

@[expose] public section

namespace Circuit

namespace Belnap

/-- The AND wire-function on a pair of Belnap-valued wires. -/
@[inline]
def and (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).and (w.get 1)]

/--
@isnad1 id=le.2h4v.s5.213c02669c18 from=translated src=- shape=5676199d vocab=83843295
-/
@[simp]
lemma and_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.and a₂ ≤ b₁.and b₂ := by
  revert a₁ a₂ b₁ b₂
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h0 h1 <;>
    first | exact h0 | exact h1 | rfl

/--
@isnad1 id=monotone.0h0v.s5.7ca2ba386f55 from=translated src=- shape=7790699d vocab=1405b26e
-/
@[simp]
lemma and_monotonic : Monotone and := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact and_leq (hab 0) (hab 1)

/-- The OR wire-function on a pair of Belnap-valued wires. -/
@[inline]
def or (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).or (w.get 1)]

/--
@isnad1 id=le.2h4v.s5.3225d61044e6 from=translated src=- shape=5676199d vocab=1769851e
-/
@[simp]
lemma or_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.or a₂ ≤ b₁.or b₂ := by
  revert a₁ a₂ b₁ b₂
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h0 h1 <;>
    first | exact h0 | exact h1 | rfl

/--
@isnad1 id=monotone.0h0v.s5.0c07a1a6f9a7 from=translated src=- shape=7790699d vocab=d52a7542
-/
@[simp]
lemma or_monotonic : Monotone or := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact or_leq (hab 0) (hab 1)

/-- The NOT wire-function on a single Belnap-valued wire. -/
@[inline]
def not (w : Wires BelnapLevel 1) : Wires BelnapLevel 1 := #v[ (w.get 0).not ]

/--
@isnad1 id=le.1h2v.s4.ac2a8d42d701 from=translated src=- shape=6bee9d27 vocab=5c47f6af
-/
@[simp]
lemma not_leq {x y : BelnapLevel} (h : x ≤ y) : x.not ≤ y.not := by
  revert x y
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h <;> exact h

/--
@isnad1 id=monotone.0h0v.s5.47796278a8ce from=translated src=- shape=7790699d vocab=14ab6832
-/
@[simp]
lemma not_monotonic : Monotone not := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact not_leq (hab 0)

end Belnap

end Circuit
