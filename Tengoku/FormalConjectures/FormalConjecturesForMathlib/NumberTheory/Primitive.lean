/-
Copyright 2026 The Formal Conjectures Authors.

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

/-!
# Primitive elements of a set with respect to divisibility

An element `n` is *primitive* in a set `S ⊆ ℕ` if `n ∈ S` and no proper divisor of `n` is in `S`.

This concept appears naturally when studying sequences closed under "divisor inheritance" -
if every member `n` of a sequence has the property that `m * n` is also in the sequence
for coprime `m`, then the primitive elements generate the entire sequence.

## Main definitions

* `Set.IsPrimitive`: A natural number `n` is primitive in `S` if `n ∈ S` and
  `n.properDivisors` is disjoint from `S`.
* `Set.primitives`: The set of primitive elements of `S`.

## Main results

* `Set.IsPrimitive.mem`: A primitive element is in the set.
* `Set.IsPrimitive.not_mem_of_properDivisor`: Proper divisors of a primitive element are not
  in the set.
* `Set.one_isPrimitive_iff`: `1` is primitive in `S` iff `1 ∈ S`.
* `Set.prime_isPrimitive_iff`: A prime `p` is primitive in `S` iff `p ∈ S` and `1 ∉ S`.
-/

namespace Set

/-- An element `n` is *primitive* in a set `S ⊆ ℕ` if `n ∈ S` and no proper divisor of `n`
is in `S`.-/
def IsPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

/-- The set of primitive elements of `S`.-/
def primitives (S : Set ℕ) : Set ℕ :=
  {n | S.IsPrimitive n}

/--
@isnad1 id=mem.1h2v.s4.0d7d8e9cc5df from=translated src=- shape=6aec9637 vocab=01d30f36
-/
theorem IsPrimitive.mem {S : Set ℕ} {n : ℕ} (h : S.IsPrimitive n) : n ∈ S := h.1

/--
@isnad1 id=disjoint.1h2v.s5.f619f9ce5f20 from=translated src=- shape=107121a0 vocab=23d6a55d
-/
theorem IsPrimitive.disjoint_properDivisors {S : Set ℕ} {n : ℕ} (h : S.IsPrimitive n) :
    Disjoint (n.properDivisors : Set ℕ) S := h.2

/--
@isnad1 id=not.2h3v.s5.4b46a13f913a from=translated src=- shape=2518386c vocab=d12c681f
-/
theorem IsPrimitive.not_mem_of_properDivisor {S : Set ℕ} {n d : ℕ} (h : S.IsPrimitive n)
    (hd : d ∈ n.properDivisors) : d ∉ S :=
  Set.disjoint_left.mp h.2 hd

/--
@isnad1 id=not.3h3v.s5.2e5a8fa9e1b0 from=translated src=- shape=431ce4e1 vocab=df17cc82
-/
theorem IsPrimitive.not_mem_of_dvd_of_lt {S : Set ℕ} {n d : ℕ} (h : S.IsPrimitive n)
    (hdvd : d ∣ n) (hlt : d < n) : d ∉ S :=
  h.not_mem_of_properDivisor (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩)

/--
@isnad1 id=iff.0h2v.s5.bdb48fe19a0a from=translated src=- shape=8d5e64ee vocab=d12c681f
-/
theorem isPrimitive_iff {S : Set ℕ} {n : ℕ} :
    S.IsPrimitive n ↔ n ∈ S ∧ ∀ d ∈ n.properDivisors, d ∉ S := by
  simp only [IsPrimitive, Set.disjoint_left, Finset.mem_coe]

/--
@isnad1 id=iff.1h2v.s5.6b3cf7048116 from=translated src=- shape=2bc5f611 vocab=df17cc82
-/
theorem isPrimitive_iff' {S : Set ℕ} {n : ℕ} (_hn : 0 < n) :
    S.IsPrimitive n ↔ n ∈ S ∧ ∀ d, d ∣ n → d < n → d ∉ S := by
  rw [isPrimitive_iff]
  constructor <;> intro ⟨hmem, hdiv⟩
  · exact ⟨hmem, fun d hd hlt => hdiv d (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)⟩
  · exact ⟨hmem, fun d hd => hdiv d (Nat.mem_properDivisors.mp hd).1 (Nat.mem_properDivisors.mp hd).2⟩

/--
@isnad1 id=iff.0h2v.s4.29b789c721d1 from=translated src=- shape=0fc14d99 vocab=b53f6e41
-/
theorem mem_primitives_iff {S : Set ℕ} {n : ℕ} : n ∈ S.primitives ↔ S.IsPrimitive n := Iff.rfl

/--
@isnad1 id=le.0h1v.s3.0b9742d5f936 from=translated src=- shape=76c97b8b vocab=9e99b4b3
-/
@[simp]
theorem primitives_subset {S : Set ℕ} : S.primitives ⊆ S := fun _ h => h.mem

/--
@isnad1 id=iff.0h1v.s4.caa52a35d893 from=translated src=- shape=d3ae4161 vocab=01d30f36
-/
theorem one_isPrimitive_iff {S : Set ℕ} : S.IsPrimitive 1 ↔ 1 ∈ S := by
  simp [isPrimitive_iff, Nat.properDivisors_one]

/--
@isnad1 id=iff.1h2v.s5.4e45154da748 from=translated src=- shape=80ff3be0 vocab=c3a4fb75
-/
theorem prime_isPrimitive_iff {S : Set ℕ} {p : ℕ} (hp : p.Prime) :
    S.IsPrimitive p ↔ p ∈ S ∧ 1 ∉ S := by
  simp [isPrimitive_iff, hp.properDivisors]

end Set
