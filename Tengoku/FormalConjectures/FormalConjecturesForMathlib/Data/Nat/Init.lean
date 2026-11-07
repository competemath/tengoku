/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

namespace Nat
variable {a b c : ℕ}

/--
@isnad1 id=iff.0h3v.s5.6ef872767e7a from=translated src=- shape=8dc4d04d vocab=e4d01d9c
-/
@[simp] protected lemma dvd_add_mul_self : a ∣ b + c * a ↔ a ∣ b := by
  rw [Nat.dvd_add_left (Nat.dvd_mul_left _ _)]

/--
@isnad1 id=iff.0h3v.s5.736a2ef1626a from=translated src=- shape=29a97b2a vocab=e4d01d9c
-/
@[simp] protected lemma dvd_add_self_mul : a ∣ b + a * c ↔ a ∣ b := by
  rw [Nat.mul_comm, Nat.dvd_add_mul_self]

/--
@isnad1 id=iff.0h3v.s5.3129f217e61b from=translated src=- shape=e0b8dc8b vocab=e4d01d9c
-/
@[simp] protected lemma dvd_mul_self_add : a ∣ b * a + c ↔ a ∣ c := by
  rw [Nat.add_comm, Nat.dvd_add_mul_self]

/--
@isnad1 id=iff.0h3v.s5.a6ded012d990 from=translated src=- shape=98d31f0e vocab=e4d01d9c
-/
@[simp] protected lemma dvd_self_mul_add : a ∣ a * b + c ↔ a ∣ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_add]

/--
@isnad1 id=iff.1h3v.s5.8803717a9887 from=translated src=- shape=4a4f03a3 vocab=e8159d92
-/
@[simp] lemma dvd_sub_iff_right' (hab : a ∣ b) : a ∣ b - c ↔ a ∣ c ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_right, Nat.le_antisymm hcb, *]

/--
@isnad1 id=iff.1h3v.s5.5be4f71231d4 from=translated src=- shape=b11492cd vocab=e8159d92
-/
@[simp] lemma dvd_sub_iff_left' (hac : a ∣ c) : a ∣ b - c ↔ a ∣ b ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_left, ← Nat.le_antisymm hcb, *]

/--
@isnad1 id=iff.0h3v.s5.9ab09492ea61 from=translated src=- shape=615ee6a1 vocab=c8f33e18
-/
@[simp] protected lemma dvd_sub_mul_self : a ∣ b - c * a ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.dvd_sub_iff_left' (Nat.dvd_mul_left _ _)]

/--
@isnad1 id=iff.0h3v.s5.b71236be899b from=translated src=- shape=b4cf56dc vocab=c8f33e18
-/
@[simp] protected lemma dvd_sub_self_mul : a ∣ b - a * c ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.mul_comm, Nat.dvd_sub_mul_self]

/--
@isnad1 id=iff.0h3v.s5.08b926c4ddef from=translated src=- shape=c5b1e277 vocab=c8f33e18
-/
@[simp] protected lemma dvd_mul_self_sub : a ∣ b * a - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.dvd_sub_iff_right' (Nat.dvd_mul_left _ _)]

/--
@isnad1 id=iff.0h3v.s5.21230903b9a8 from=translated src=- shape=42bdc174 vocab=c8f33e18
-/
@[simp] protected lemma dvd_self_mul_sub : a ∣ a * b - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_sub]

end Nat
