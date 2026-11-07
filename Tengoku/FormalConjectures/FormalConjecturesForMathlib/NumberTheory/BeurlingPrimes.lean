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
# Beurling primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Beurling_zeta_function)
 - [Beurling Zeta Functions, Generalised Primes, and Fractal Membranes](https://arxiv.org/abs/math/0410270)
-/

open Filter

/-- A sequence of real numbers `1 < a 0 < a 1 < ...` is called a set of Beurling prime numbers if
it tends to infinity.-/
noncomputable def IsBeurlingPrimes (a : ℕ → ℝ) : Prop :=
  1 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop

/-- A Beurling integer is a number of the form `∏ i, (a i) ^ (k i)` for a given sequence `a` and a
finitely-supported sequence of naturals `k`.-/
def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ := k.prod fun x y ↦ (a x) ^ y

/--
@isnad1 id=eq.0h2v.s5.d2e5997e02b1 from=translated src=- shape=a23c48c0 vocab=97de660e
-/
@[simp] theorem beurlingInteger_def (a k) : beurlingInteger a k =  k.prod fun x y ↦ (a x) ^ y := rfl

/-- The set of Beurling integers are numbers of the form `∏ i, (a i) ^ (k i)`, where `k` has
finite support.-/
def BeurlingIntegers (a : ℕ → ℝ) : Set ℝ := .range (beurlingInteger a)

/--
@isnad1 id=mem.0h2v.s4.4df0d6de646c from=translated src=- shape=1ed61ac6 vocab=0734aa22
-/
theorem beurlingInteger_mem (a k) : beurlingInteger a k ∈ BeurlingIntegers a := by
  simpa using ⟨k, rfl⟩

/-- Every element of the sequence `a` is a Beurling integer.
@isnad1 id=mem.0h2v.s4.77243d5b1305 from=translated src=- shape=745a1135 vocab=2c137f77
-/
lemma generator_mem_beurling (a : ℕ → ℝ) (i : ℕ) : a i ∈ BeurlingIntegers a :=
  ⟨Finsupp.single i 1, by aesop⟩

/-- The set of Beurling integers is closed under multiplication.
@isnad1 id=mem.2h3v.s5.af00829aed98 from=translated src=- shape=b42f7e80 vocab=d854ab6e
-/
lemma mul_mem_beurling {a : ℕ → ℝ} {x y : ℝ} (hx : x ∈ BeurlingIntegers a)
    (hy : y ∈ BeurlingIntegers a) : x * y ∈ BeurlingIntegers a := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  exact ⟨k + l, by simp [Finsupp.prod_add_index', pow_add]⟩

/-- The set of Beurling integers is closed under taking powers.
@isnad1 id=mem.1h3v.s5.01b35cc50b54 from=translated src=- shape=f29f8c6a vocab=a1537861
-/
lemma pow_mem_beurling {a : ℕ → ℝ} {x : ℝ} (k : ℕ) (hx : x ∈ BeurlingIntegers a) :
    x ^ k ∈ BeurlingIntegers a := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih => simpa [pow_succ'] using mul_mem_beurling hx ih
