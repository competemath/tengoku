/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

/-!
# LeanPool.LeanPolyABC.Lib.Max3

Imported Lean Pool material for `LeanPool.LeanPolyABC.Lib.Max3`.
-/

@[expose] public section

namespace Nat

/-- The maximum of three natural numbers, `max (max a b) c`. -/
def max₃ (a b c : Nat) : Nat :=
  max (max a b) c

/--
@isnad1 id=eq.0h4v.s5.d17cce48e430 from=translated src=- shape=aa6d7680 vocab=1f332550
-/
theorem max₃_mul_distrib_left (a b c d : Nat) : a * max₃ b c d = max₃ (a * b) (a * c) (a * d) := by
  rw [max₃, max₃, Nat.mul_max_mul_left, Nat.mul_max_mul_left]

/--
@isnad1 id=eq.0h4v.s5.8c3e2549ea69 from=translated src=- shape=f1e1cac5 vocab=d7810cff
-/
theorem max₃_add_distrib_left (a b c d : Nat) : d + max₃ a b c = max₃ (d + a) (d + b) (d + c) := by
  rw [max₃, max₃, Nat.add_max_add_left, Nat.add_max_add_left]

/--
@isnad1 id=eq.0h4v.s5.3d7be09f68aa from=translated src=- shape=5d797e47 vocab=d7810cff
-/
theorem max₃_add_distrib_right (a b c d : Nat) : max₃ a b c + d = max₃ (a + d) (b + d) (c + d) := by
  rw [max₃, max₃, Nat.add_max_add_right, Nat.add_max_add_right]

/--
@isnad1 id=le.0h3v.s3.082b264c2dac from=translated src=- shape=b745d4cc vocab=7b24d372
-/
theorem le_max₃_left (a b c : Nat) : a ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ _)

/--
@isnad1 id=le.0h3v.s3.2e1cd2ad6bdd from=translated src=- shape=df17f624 vocab=7b24d372
-/
theorem le_max₃_middle (a b c : Nat) : b ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ _)

/--
@isnad1 id=le.0h3v.s3.719c80bfc8b6 from=translated src=- shape=65f3bd0e vocab=7b24d372
-/
theorem le_max₃_right (a b c : Nat) : c ≤ max₃ a b c :=
  Nat.le_max_right _ c

/--
@isnad1 id=iff.0h4v.s5.e1f671e084b8 from=translated src=- shape=351d7602 vocab=20bcbb81
-/
theorem max₃_lt {a b c d : Nat} : max₃ a b c < d ↔ a < d ∧ b < d ∧ c < d := by
  rw [max₃, Nat.max_lt, Nat.max_lt, and_assoc]

/--
@isnad1 id=iff.0h4v.s5.aaedba408ed5 from=translated src=- shape=351d7602 vocab=7b24d372
-/
theorem max₃_le {a b c d : Nat} : max₃ a b c ≤ d ↔ a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  rw [max₃, Nat.max_le, Nat.max_le, and_assoc]

end Nat
