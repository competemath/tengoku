/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Tengoku

/-! # Belnap levels

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

@[expose] public section

namespace Circuit

/-- The Belnap four-valued logic lattice on `Bool`, with a bottom (no information) and a
top (conflicting information) adjoined. -/
def BelnapLevel := WithBotTop Bool

namespace BelnapLevel

instance : Coe (WithBotTop Bool) (BelnapLevel) where
  coe l := l

instance : Bot BelnapLevel where
  bot := .none

instance : Top BelnapLevel where
  top := .some .none

/-- The information ordering on Belnap levels: `⊥` is below everything, everything is below `⊤`,
and the two classical values are only related to themselves. -/
@[inline]
def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false

/--
@isnad1 id=le.0h1v.s2.eb51dd274356 from=translated src=- shape=b3bac8d8 vocab=e78a6501
-/
lemma le_refl : ∀ (a : BelnapLevel), a.le a := by
  rintro (_ | (_ | (_ | _))) <;> trivial

/--
@isnad1 id=le.2h3v.s4.6413a1a17a97 from=translated src=- shape=0bc0c4a6 vocab=e78a6501
-/
lemma le_trans : ∀ (a b c : BelnapLevel), a.le b → b.le c → a.le c := by
  rintro (_ | (_ | a)) (_ | (_ | b)) (_ | (_ | c)) hab hbc <;> simp_all [le]

instance : Preorder BelnapLevel where
  le
  le_refl
  le_trans

/--
@isnad1 id=eq.2h2v.s4.3d3a08ddb620 from=translated src=- shape=4c719c5d vocab=2e24d8b4
-/
lemma le_antisymm : ∀ (a b : BelnapLevel), a ≤ b → b ≤ a → a = b := by
  rintro (_ | (_ | a)) (_ | (_ | b)) hab hba <;> simp_all [LE.le, le] <;> rfl

/-- The join (least upper bound) on Belnap levels in the information order. -/
def sup : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, x => x
  | x, .none => x
  | .some .none, _ => .some .none
  | _, .some .none => .some .none
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .some .none

/--
@isnad1 id=le.0h2v.s3.f7374a78c0ce from=translated src=- shape=70252ff3 vocab=ccce626f
-/
lemma le_sup_left : ∀ (a b : BelnapLevel), a ≤ a.sup b:= by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> trivial

/--
@isnad1 id=le.0h2v.s3.7aa7840d1e54 from=translated src=- shape=86c6c8ca vocab=ccce626f
-/
lemma le_sup_right : ∀ (a b : BelnapLevel), b ≤ a.sup b := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> trivial

/--
@isnad1 id=le.2h3v.s4.81b24c3d44b6 from=translated src=- shape=343a5309 vocab=ccce626f
-/
lemma sup_le : ∀ (a b c : BelnapLevel), a ≤ c → b ≤ c → a.sup b ≤ c  := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) hac hbc <;> trivial

instance : SemilatticeSup BelnapLevel where
  le_antisymm
  sup
  le_sup_left
  le_sup_right
  sup_le

/-- Logical AND. -/
@[inline]
def and (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some false), _ => false
  | _, .some (.some false) => false
  | .some (.some true), x => x
  | x, .some (.some true) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => false

/-- Logical OR. -/
@[inline]
def or (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some true), _ => true
  | _, .some (.some true) => true
  | .some (.some false), x => x
  | x, .some (.some false) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => true

/-- Logical NOT. -/
@[inline]
def not : BelnapLevel → BelnapLevel
  | .some (.some b) => !b
  | x => x

end BelnapLevel

end Circuit
