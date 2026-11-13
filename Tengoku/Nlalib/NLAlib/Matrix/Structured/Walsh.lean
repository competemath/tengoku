/-
Copyright (c) 2026 Diar Heidary.

Ported and adapted from Rerandomized-Subsampled-Trigonometric-Transforms,
SRHT/Walsh.lean, commit 929653a019eb4910fc6efb9cb34cc3c3c2f949d4.

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.LinearAlgebra.Matrix.HadamardMatrix
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete normalized Walsh–Hadamard matrices

The transform on `(ZMod 2)^b` has order `2^b`, constant-magnitude
entries and orthonormal rows and columns. Only Walsh algebra is ported;
the classical one-sign SRHT law is constructed separately. supports atlas `srht-ose`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The binary group indexing a Walsh matrix of order `2^b`.-/
abbrev WalshIndex (b : ℕ) := Fin b → ZMod 2

/-- The Walsh row and column index set has `2^b` elements.
@isnad1 id=eq.0h1v.s5.b6fad659b757 from=translated src=- shape=5b09d1d5 vocab=a474ea92
-/
@[simp] theorem card_walshIndex (b : ℕ) : Fintype.card (WalshIndex b) = 2 ^ b := by
  simp [WalshIndex]

/-- The real sign associated to one binary bit.
Source: Walsh character construction; supports `srht-ose`.-/
def walshBitSign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- Addition of bits multiplies their real signs.
Source: Walsh character construction; supports `srht-ose`.
@isnad1 id=eq.0h2v.s6.44b344d20c01 from=translated src=- shape=b67944bb vocab=a85950cd
-/
theorem walshBitSign_add (a b : ZMod 2) :
    walshBitSign (a + b) = walshBitSign a * walshBitSign b := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;>
    simp [walshBitSign, hone]

/-- Every bit sign has squared value one.
Source: Walsh character construction; supports `srht-ose`.
@isnad1 id=eq.0h1v.s5.17527519cc95 from=translated src=- shape=1bb5949c vocab=2194eafa
-/
@[simp] theorem walshBitSign_sq (a : ZMod 2) : walshBitSign a ^ 2 = 1 := by
  unfold walshBitSign
  split_ifs <;> norm_num

/-- Summing a Walsh bit character vanishes unless its frequency is zero.
Source: Walsh character orthogonality; supports `srht-ose`.
@isnad1 id=eq.0h1v.s7.c6a4996709f5 from=translated src=- shape=3073a9d1 vocab=24675185
-/
theorem sum_walshBitSign_mul (a : ZMod 2) :
    (∑ b : ZMod 2, walshBitSign (a * b)) = if a = 0 then 2 else 0 := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc a with rfl | rfl
  · simp [walshBitSign]
  · rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    norm_num [walshBitSign]

/-- The unnormalized real Walsh character.-/
def walshCharacter {b : ℕ} (a c : WalshIndex b) : ℝ :=
  ∏ i, walshBitSign (a i * c i)

/-- Walsh characters are symmetric in the row and column labels.
Source: Walsh construction; supports `srht-ose`.
@isnad1 id=eq.0h3v.s4.930132e256fc from=translated src=- shape=7a5478ec vocab=d6ae7e16
-/
theorem walshCharacter_comm {b : ℕ} (a c : WalshIndex b) :
    walshCharacter a c = walshCharacter c a := by simp [walshCharacter, mul_comm]

/-- Addition of row labels multiplies Walsh characters.
Source: Walsh construction; supports `srht-ose`.
@isnad1 id=eq.0h4v.s6.f4fda663543b from=translated src=- shape=6a42c977 vocab=9b48ecde
-/
theorem walshCharacter_add_left {b : ℕ} (a c z : WalshIndex b) :
    walshCharacter (a + c) z = walshCharacter a z * walshCharacter c z := by
  simp only [walshCharacter, Pi.add_apply, add_mul, walshBitSign_add, Finset.prod_mul_distrib]

/-- Every Walsh character has squared value one.
Source: Walsh construction; supports `srht-ose`.
@isnad1 id=eq.0h3v.s5.8298d596182a from=translated src=- shape=f8527af6 vocab=cd6de7ff
-/
@[simp] theorem walshCharacter_sq {b : ℕ} (a c : WalshIndex b) : walshCharacter a c ^ 2 = 1 := by
  simp [walshCharacter, ← Finset.prod_pow]

/-- Binary-vector addition is zero precisely when its two inputs agree.
Source: Walsh character orthogonality; supports `srht-ose`.
@isnad1 id=iff.0h3v.s7.5bed527c6842 from=translated src=- shape=99cfb232 vocab=7461c00c
-/
theorem walshIndex_add_eq_zero_iff {b : ℕ} (a c : WalshIndex b) : a + c = 0 ↔ a = c := by
  have hc : ∀ z : WalshIndex b, z + z = 0 := by
    intro z
    ext i
    exact CharTwo.add_self_eq_zero (z i)
  constructor
  · intro h
    have hh := congrArg (fun z : WalshIndex b => z + c) h
    simpa only [add_assoc, hc, add_zero, zero_add] using hh
  · rintro rfl
    exact hc a

/-- The sum of a Walsh character is zero at every nonzero frequency.
Source: Walsh character orthogonality; supports `srht-ose`.
@isnad1 id=eq.0h2v.s7.aa0b96181cef from=translated src=- shape=f493944d vocab=2ddc3fb3
-/
theorem sum_walshCharacter {b : ℕ} (a : WalshIndex b) :
    (∑ c, walshCharacter a c) = if a = 0 then (Fintype.card (WalshIndex b) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, walshCharacter, walshBitSign]
  · rw [ite_eq_right ha]
    unfold walshCharacter
    rw [← Fintype.prod_sum (fun i : Fin b => fun c : ZMod 2 => walshBitSign (a i * c))]
    simp_rw [sum_walshBitSign_mul]
    have hex : ∃ i, a i ≠ 0 := by
      by_contra hh
      push Not at hh
      exact ha (funext hh)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Distinct Walsh characters are orthogonal over the binary group.
Source: Walsh construction; supports `srht-ose`.
@isnad1 id=eq.0h3v.s7.d7e40b1076f3 from=translated src=- shape=f1c8f5b0 vocab=435f47ac
-/
theorem sum_mul_walshCharacter {b : ℕ} (a c : WalshIndex b) :
    (∑ z, walshCharacter a z * walshCharacter c z) =
      if a = c then (Fintype.card (WalshIndex b) : ℝ) else 0 := by
  simp_rw [← walshCharacter_add_left]
  rw [sum_walshCharacter]
  simp only [walshIndex_add_eq_zero_iff]

/-- The normalized symmetric Walsh–Hadamard matrix.-/
def walshMatrix (b : ℕ) : Matrix (WalshIndex b) (WalshIndex b) ℝ := fun a c =>
  (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter a c

/-- The normalized Walsh matrix is symmetric.
Source: Walsh construction; supports `srht-ose`.
@isnad1 id=eq.0h1v.s4.a3eefde9648b from=translated src=- shape=ba899254 vocab=5cbb34e9
-/
@[simp] theorem walshMatrix_transpose (b : ℕ) : (walshMatrix b)ᵀ = walshMatrix b := by
  ext a c
  exact congrArg ((Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * ·) (walshCharacter_comm c a)

/-- The normalized Walsh matrix is an involution.
Source: Walsh orthogonality; supports `srht-ose`.
@isnad1 id=eq.0h1v.s6.c273435350bb from=translated src=- shape=097af835 vocab=76e950a5
-/
theorem walshMatrix_mul_self (b : ℕ) : walshMatrix b * walshMatrix b = 1 := by
  classical
  have hn : (0 : ℝ) < Fintype.card (WalshIndex b) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card (WalshIndex b) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  ext a c
  simp only [Matrix.mul_apply, walshMatrix, Matrix.one_apply]
  have hsum : (∑ z,
      (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter a z *
        ((Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter z c)) =
      (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ ^ 2 *
        ∑ z, walshCharacter a z * walshCharacter c z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [walshCharacter_comm z c]
    ring
  rw [hsum, sum_mul_walshCharacter]
  split_ifs
  · have hs2 := Real.sq_sqrt hn.le
    field_simp
    exact hs2.symm
  · simp

/-- The normalized Walsh matrix has orthonormal columns.
@isnad1 id=eq.0h1v.s6.9a822f019410 from=translated src=- shape=adeff4e9 vocab=9e3430b0
-/
@[simp] theorem walshMatrix_transpose_mul_self (b : ℕ) : (walshMatrix b)ᵀ * walshMatrix b = 1 := by
  rw [walshMatrix_transpose, walshMatrix_mul_self]

/-- Every normalized Walsh entry has squared magnitude `1/2^b`. the literal flatness hypothesis.
@isnad1 id=eq.0h3v.s6.57d46728a33f from=translated src=- shape=138061f3 vocab=71c29a53
-/
theorem walshMatrix_apply_sq (b : ℕ) (a c : WalshIndex b) :
    walshMatrix b a c ^ 2 = 1 / (2 ^ b : ℝ) := by
  rw [walshMatrix, mul_pow, walshCharacter_sq, mul_one, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), card_walshIndex]
  simp

end NLAlib
