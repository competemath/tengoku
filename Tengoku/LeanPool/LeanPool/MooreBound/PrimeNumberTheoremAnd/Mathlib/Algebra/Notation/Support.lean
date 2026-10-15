/-
Copyright (c) 2026 PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrimeNumberTheoremAnd contributors
-/

module

public import Tengoku

/-!
Ported for Lean Pool from PrimeNumberTheoremAnd commit
0c7abf7be7765dc5ffd21afc1c37b018199ec3c9, via wewantmoore commit
d59bd80ea93fabb9faf769e790ab47692645e022 (both Apache-2.0).
The port adds the MooreBound namespace and updates Mathlib APIs and proof style.
Wiener and Consequences retain the PNT and prime-interval dependency closure;
unrelated later developments and LeanArchitect annotations are omitted.
-/

@[expose] public section

namespace MooreBound

namespace Function

open _root_.Function

variable {α : Type*} [Zero α]

/--
@isnad1 id=eq.0h1v.s4.dd0f82b68aa3 from=translated src=- shape=c4682940 vocab=93f48021
-/
theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

/--
@isnad1 id=eq.0h1v.s5.257db8984d3f from=translated src=- shape=99d5931f vocab=8326bbea
-/
theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end MooreBound
