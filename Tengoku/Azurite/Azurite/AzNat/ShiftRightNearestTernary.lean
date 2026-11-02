/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzNat.ShiftRight
import Tengoku.Azurite.Azurite.AzNat.ShiftLeft
import Tengoku.Azurite.Azurite.AzNat.ModPow2
import Tengoku.Azurite.Azurite.AzNat.Compare
import Tengoku.Azurite.Azurite.AzNat.Parity
import Tengoku.Azurite.Azurite.AzNat.Add
import Tengoku.Azurite.Azurite.AzInt.Add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Right shift rounded to nearest with a ternary tie-break

`shiftRightNearestTernary n o sh` is `n / 2^sh` rounded to the nearest integer, where an exact
half is resolved by `o`, the comparison of `n / 2^sh` with the true value it stands for: `.lt`
(the true value is larger) rounds up, `.gt` rounds down, `.eq` (a genuine tie) rounds to even.
This is the second rounding of a *double rounding*: a value already rounded to a fine grid with a
known ternary is re-rounded to a coarser grid without the double-rounding error
(`Azurite/Rounding/IntNearest.lean`, `toInt_round_nearest_of_ternary`).  The `AzInt` version
applies it to the magnitude, swapping the ternary for negative values.
-/

namespace Azurite

/-- `n / 2^sh` to the nearest integer, exact halves by the ternary `o`.-/
def AzNat.shiftRightNearestTernary (n : AzNat) (o : Ordering) (sh : Nat) : AzNat :=
  if sh = 0 then n
  else
    let q := n.shiftRight sh
    match AzNat.compare (n.modPow2 sh) ((AzNat.ofNat 1).shiftLeft (sh - 1)) with
    | .lt => q
    | .gt => q.addUInt64 1
    | .eq =>
      match o with
      | .lt => q.addUInt64 1
      | .gt => q
      | .eq => if q.isOdd then q.addUInt64 1 else q

/-- `z / 2^sh` to the nearest integer, exact halves by the ternary `o` (which compares `z / 2^sh`
with the true value; for a negative `z` the magnitude sees the swapped ternary).-/
def AzInt.shiftRightNearestTernary (z : AzInt) (o : Ordering) (sh : Nat) : AzInt :=
  AzInt.mkNorm z.sign (z.abs.shiftRightNearestTernary (if z.sign then o else o.swap) sh)

end Azurite
