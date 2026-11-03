/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.ShiftLeft
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Azurite.Azurite.AzNat.Equiv.ShiftLeft

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

/-- Correctness of `AzInt.shiftLeft`.
@isnad1 id=eq.0h2v.s5.523e45a7e605 from=translated src=- shape=dbe29c72 vocab=32633d9d
-/
theorem toInt_shiftLeft (z : AzInt) (sh : Nat) :
    (shiftLeft z sh).toInt = z.toInt * 2 ^ sh := by
  have h_abs : (z.abs <<< sh).toNat = z.abs.toNat * 2 ^ sh := by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
  show (if z.sign then ((z.abs <<< sh).toNat : Int) else -((z.abs <<< sh).toNat : Int))
       = z.toInt * 2 ^ sh
  rw [h_abs]
  show (if z.sign then ((z.abs.toNat * 2 ^ sh : Nat) : Int)
         else -((z.abs.toNat * 2 ^ sh : Nat) : Int))
       = z.toInt * 2 ^ sh
  cases hs : z.sign
  · have hz : z.toInt = -(z.abs.toNat : Int) := by
      change (if z.sign then _ else _) = _
      rw [hs]; simp
    rw [hz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    push_cast; ring
  · have hz : z.toInt = (z.abs.toNat : Int) := by
      change (if z.sign then _ else _) = _
      rw [hs]; simp
    rw [hz]
    simp only [↓reduceIte]
    push_cast; ring

/-- Compatibility of `HShiftLeft` notation with `shiftLeft`.
@isnad1 id=eq.0h2v.s4.a1a1c9588af2 from=translated src=- shape=62f8b022 vocab=3583e233
-/
@[simp] lemma hShiftLeft_eq (z : AzInt) (sh : Nat) : z <<< sh = shiftLeft z sh := rfl

/-- `toInt` respects left shift.
@isnad1 id=eq.0h2v.s5.5a41f51f0c96 from=translated src=- shape=b538a972 vocab=e3e762ed
-/
theorem toInt_hShiftLeft (z : AzInt) (sh : Nat) :
    (z <<< sh).toInt = z.toInt * 2 ^ sh := by
  rw [hShiftLeft_eq, toInt_shiftLeft]

/-- `ofInt`-version of `toInt_shiftLeft`.
@isnad1 id=eq.0h2v.s5.2b2a1ded291c from=translated src=- shape=5027fddb vocab=b89bd508
-/
theorem ofInt_shiftLeft (i : Int) (sh : Nat) :
    ofInt (i * 2 ^ sh) = (ofInt i) <<< sh := by
  have h : (ofInt (i * 2 ^ sh)).toInt = ((ofInt i) <<< sh).toInt := by
    rw [toInt_ofInt, toInt_hShiftLeft, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
