/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Fixed-width binary encodings of natural numbers

Big-endian, fixed-width binary encoding `Nat.toBits` with its exact decoder
`Nat.fromBits`, plus the little-endian views `Nat.toBitsLE` and
`Nat.fromBitsLE` used by local Turing-machine arithmetic. Both conventions
have exact length, truncation, round-trip, and fixed-width injectivity lemmas.
Values wider than the target width are truncated modulo `2 ^ w`.
The final layer packages these bits into a canonical ceiling-logarithmic codec
for `Fin n`, including exact rejection conditions for malformed inputs.

This file lives in `Complexitylib/Mathlib/` because it extends a Mathlib
type in its home (root) namespace — the sanctioned exception to the
`Complexity` root-namespace rule. Its contents are candidates for
upstreaming to Mathlib.
-/

@[expose] public section

/-- Encode a natural number as a big-endian binary list of exactly `w` bits.
    Numbers larger than `2^w - 1` are truncated (mod 2^w). -/
def Nat.toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, val => (val / 2 ^ w % 2 == 1) :: Nat.toBits w val

/--
@isnad1 id=eq.0h2v.s3.d044297c5c74 from=translated src=- shape=aadcd40e vocab=df0b7f74
-/
theorem Nat.length_toBits : ∀ (w val : ℕ), (Nat.toBits w val).length = w
  | 0, _ => rfl
  | w + 1, val => by simp [Nat.toBits, Nat.length_toBits w]

/-- Decode a big-endian binary list to a natural number. -/
def Nat.fromBits : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 2 ^ rest.length + Nat.fromBits rest

/-- Decoded values are bounded by `2 ^ length`.
@isnad1 id=lt.0h1v.s4.60d96dd915d3 from=translated src=- shape=00b51492 vocab=222a39eb
-/
theorem Nat.fromBits_lt_pow_length : ∀ (l : List Bool), Nat.fromBits l < 2 ^ l.length
  | [] => by simp [Nat.fromBits]
  | b :: rest => by
    have ih := Nat.fromBits_lt_pow_length rest
    simp only [Nat.fromBits, List.length_cons, pow_succ]
    rcases b with _ | _ <;> simp <;> omega

/-- `fromBits ∘ toBits w` reduces any input modulo `2 ^ w`.
@isnad1 id=eq.0h2v.s5.46a4ebb3c12e from=translated src=- shape=d6fecd78 vocab=cf8217d3
-/
theorem Nat.fromBits_toBits_mod : ∀ (w val : ℕ),
    Nat.fromBits (Nat.toBits w val) = val % 2 ^ w
  | 0, val => by simp [Nat.toBits, Nat.fromBits, Nat.mod_one]
  | w + 1, val => by
    have ih := Nat.fromBits_toBits_mod w val
    simp only [Nat.toBits, Nat.fromBits, Nat.length_toBits, ih]
    have hbit : (val / 2 ^ w) % 2 = if (val / 2 ^ w % 2 == 1) then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one (val / 2 ^ w) with h | h <;> simp [h]
    have hpow : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
    have hkey : val % 2 ^ (w + 1) = (val / 2 ^ w) % 2 * 2 ^ w + val % 2 ^ w := by
      rw [hpow, Nat.mod_mul, Nat.mul_comm (2^w) _, Nat.add_comm]
    rw [hkey, ← hbit]

/-- `Nat.fromBits` is a left inverse of `Nat.toBits` on values below `2 ^ w`.
@isnad1 id=eq.1h2v.s5.b1a4921477a4 from=translated src=- shape=352716ff vocab=85650d78
-/
theorem Nat.fromBits_toBits {w val : ℕ} (hv : val < 2 ^ w) :
    Nat.fromBits (Nat.toBits w val) = val := by
  rw [Nat.fromBits_toBits_mod, Nat.mod_eq_of_lt hv]

/-- Adding a multiple of `2^w` does not change the low `w` encoded bits.
@isnad1 id=eq.0h3v.s5.ed5e263d28f3 from=translated src=- shape=b4c6e0b2 vocab=7467c802
-/
theorem Nat.toBits_add_pow_mul : ∀ (w val c : ℕ),
    Nat.toBits w (val + c * 2 ^ w) = Nat.toBits w val
  | 0, _, _ => rfl
  | w + 1, val, c => by
    have hrw : val + c * 2 ^ (w + 1) = val + c * 2 * 2 ^ w := by
      rw [pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc]
    have hdiv : (val + c * 2 * 2 ^ w) / 2 ^ w = val / 2 ^ w + c * 2 :=
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos w)
    simp only [hrw, Nat.toBits, hdiv, List.cons.injEq]
    constructor
    · rw [Nat.add_mul_mod_self_right]
    · exact Nat.toBits_add_pow_mul w val (c * 2)

/-- Fixed-width encoding recovers every bit list from its decoded value.
@isnad1 id=eq.0h1v.s3.1ad36890ad7c from=translated src=- shape=52529072 vocab=9cae240c
-/
theorem Nat.toBits_fromBits : ∀ bits : List Bool,
    Nat.toBits bits.length (Nat.fromBits bits) = bits
  | [] => rfl
  | bit :: rest => by
    have hlt := Nat.fromBits_lt_pow_length rest
    have hval : Nat.fromBits (bit :: rest) =
        Nat.fromBits rest + (if bit then 1 else 0) * 2 ^ rest.length := by
      simp only [Nat.fromBits]
      exact Nat.add_comm _ _
    simp only [List.length_cons, Nat.toBits, List.cons.injEq]
    constructor
    · rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
      cases bit <;> simp
    · rw [hval, Nat.toBits_add_pow_mul, Nat.toBits_fromBits rest]

/-- Decoding is injective among bit lists of the same width.
@isnad1 id=eq.2h2v.s4.c0f332be0312 from=translated src=- shape=58789302 vocab=9124342b
-/
theorem Nat.fromBits_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Nat.fromBits first = Nat.fromBits second) : first = second := by
  have hfirst := Nat.toBits_fromBits first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Nat.toBits_fromBits second]

/-- Little-endian fixed-width bits, with the least significant bit first. -/
def Nat.toBitsLE (width value : ℕ) : List Bool :=
  (Nat.toBits width value).reverse

/-- Decode a little-endian bit list. -/
def Nat.fromBitsLE (bits : List Bool) : ℕ :=
  Nat.fromBits bits.reverse

/-- Little-endian encoding has exactly the requested width.
@isnad1 id=eq.0h2v.s3.b75964b2ef3d from=translated src=- shape=aadcd40e vocab=50da4407
-/
@[simp] theorem Nat.length_toBitsLE (width value : ℕ) :
    (Nat.toBitsLE width value).length = width := by
  simp [Nat.toBitsLE, Nat.length_toBits]

/-- Little-endian decoding of a fixed-width encoding truncates modulo `2^width`.
@isnad1 id=eq.0h2v.s5.160be556c3c8 from=translated src=- shape=d6fecd78 vocab=a57b4359
-/
theorem Nat.fromBitsLE_toBitsLE_mod (width value : ℕ) :
    Nat.fromBitsLE (Nat.toBitsLE width value) = value % 2 ^ width := by
  simp [Nat.fromBitsLE, Nat.toBitsLE, Nat.fromBits_toBits_mod]

/-- Little-endian encoding exactly round-trips values that fit the width.
@isnad1 id=eq.1h2v.s5.335bd0f70504 from=translated src=- shape=352716ff vocab=5250d8b5
-/
theorem Nat.fromBitsLE_toBitsLE {width value : ℕ} (hvalue : value < 2 ^ width) :
    Nat.fromBitsLE (Nat.toBitsLE width value) = value := by
  rw [Nat.fromBitsLE_toBitsLE_mod, Nat.mod_eq_of_lt hvalue]

/-- Every little-endian list is recovered at its own fixed width.
@isnad1 id=eq.0h1v.s3.6fefec2bbd0e from=translated src=- shape=52529072 vocab=924954a7
-/
theorem Nat.toBitsLE_fromBitsLE (bits : List Bool) :
    Nat.toBitsLE bits.length (Nat.fromBitsLE bits) = bits := by
  unfold Nat.toBitsLE Nat.fromBitsLE
  rw [show bits.length = bits.reverse.length by simp,
    Nat.toBits_fromBits, List.reverse_reverse]

/-- A little-endian list decodes below `2` raised to its width.
@isnad1 id=lt.0h1v.s4.67b4c16b41d8 from=translated src=- shape=00b51492 vocab=16c575e0
-/
theorem Nat.fromBitsLE_lt_pow_length (bits : List Bool) :
    Nat.fromBitsLE bits < 2 ^ bits.length := by
  unfold Nat.fromBitsLE
  simpa using Nat.fromBits_lt_pow_length bits.reverse

/-- Little-endian decoding is injective at a fixed width.
@isnad1 id=eq.2h2v.s4.d73e52907250 from=translated src=- shape=58789302 vocab=40673f92
-/
theorem Nat.fromBitsLE_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Nat.fromBitsLE first = Nat.fromBitsLE second) : first = second := by
  have hfirst := Nat.toBitsLE_fromBitsLE first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Nat.toBitsLE_fromBitsLE second]

private theorem Nat.fromBits_append_singleton :
    ∀ (bits : List Bool) (bit : Bool),
      Nat.fromBits (bits ++ [bit]) =
        2 * Nat.fromBits bits + (if bit then 1 else 0)
  | [], bit => by cases bit <;> simp [Nat.fromBits]
  | first :: rest, bit => by
      rw [List.cons_append, Nat.fromBits,
        Nat.fromBits_append_singleton rest bit]
      simp only [List.length_append, List.length_singleton, pow_succ]
      cases first <;> simp [Nat.fromBits]
      omega

/-- Little-endian decoding exposes its least-significant head bit.
@isnad1 id=eq.0h2v.s5.8a0d58187a78 from=translated src=- shape=3388abe9 vocab=2b4b831e
-/
theorem Nat.fromBitsLE_cons (bit : Bool) (bits : List Bool) :
    Nat.fromBitsLE (bit :: bits) =
      (if bit then 1 else 0) + 2 * Nat.fromBitsLE bits := by
  simp only [Nat.fromBitsLE, List.reverse_cons]
  rw [Nat.fromBits_append_singleton]
  omega

/-- Decoding the canonical variable-width little-endian bits recovers the
original natural number.
@isnad1 id=eq.0h1v.s3.011d1cbbed21 from=translated src=- shape=47dcad53 vocab=474de83e
-/
theorem Nat.fromBitsLE_bits : ∀ value : ℕ,
    Nat.fromBitsLE value.bits = value := by
  intro value
  induction value using Nat.binaryRec' with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue,
        Nat.fromBitsLE_cons, ih]
      cases bit <;> simp [Nat.bit]
      omega

/-- The minimal fixed-width little-endian encoding is exactly the canonical
variable-width bit list.
@isnad1 id=eq.0h1v.s3.2d373decb6ee from=translated src=- shape=ed2799c8 vocab=11d4578a
-/
theorem Nat.toBitsLE_size (value : ℕ) :
    Nat.toBitsLE value.size value = value.bits := by
  calc
    Nat.toBitsLE value.size value =
        Nat.toBitsLE value.bits.length (Nat.fromBitsLE value.bits) := by
      congr 1
      · exact (Nat.size_eq_bits_len value).symm
      · exact (Nat.fromBitsLE_bits value).symm
    _ = value.bits := Nat.toBitsLE_fromBitsLE value.bits

/-- Binary digit width is at most floor-log base two plus one.
@isnad1 id=le.0h1v.s4.8d7bc8beea07 from=translated src=- shape=1d4866ef vocab=c1c198e4
-/
theorem Nat.size_le_log_two_add_one (value : ℕ) :
    value.size ≤ Nat.log 2 value + 1 := by
  rw [Nat.size_le]
  simpa only [Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (b := 2) (by omega) value

/-- Every positive natural has binary digit width exactly floor-log base two
plus one.
@isnad1 id=eq.1h1v.s5.f38fdd6bc50d from=translated src=- shape=2a5c2614 vocab=54314080
-/
theorem Nat.size_eq_log_two_add_one {value : ℕ} (hvalue : value ≠ 0) :
    value.size = Nat.log 2 value + 1 := by
  apply le_antisymm (Nat.size_le_log_two_add_one value)
  have hlower : Nat.log 2 value < value.size := by
    rw [Nat.lt_size]
    exact Nat.pow_log_le_self 2 hvalue
  omega

/-- Ceiling-logarithmic width sufficient to encode an element of `Fin size`. -/
def Fin.bitWidth (size : ℕ) : ℕ :=
  Nat.clog 2 size

/-- Encode a finite index using the canonical ceiling-logarithmic width. -/
def Fin.toBits {size : ℕ} (index : Fin size) : List Bool :=
  Nat.toBits (Fin.bitWidth size) index

/-- Decode an exactly sized finite-index encoding, rejecting out-of-range
values. -/
def Fin.fromBits? (size : ℕ) (bits : List Bool) : Option (Fin size) :=
  if _hlength : bits.length = Fin.bitWidth size then
    if hvalue : Nat.fromBits bits < size then
      some ⟨Nat.fromBits bits, hvalue⟩
    else
      none
  else
    none

/-- Finite-index encoding has exactly the canonical ceiling-logarithmic
width.
@isnad1 id=eq.0h2v.s3.4de940f3a762 from=translated src=- shape=97f23171 vocab=3513ec21
-/
@[simp] theorem Fin.length_toBits {size : ℕ} (index : Fin size) :
    index.toBits.length = Fin.bitWidth size := by
  simp [Fin.toBits, Fin.bitWidth, Nat.length_toBits]

/-- Canonical finite-index encoding round-trips exactly.
@isnad1 id=eq.0h2v.s4.798fcfaedeb5 from=translated src=- shape=e515e695 vocab=8258d4a9
-/
@[simp] theorem Fin.fromBits?_toBits {size : ℕ} (index : Fin size) :
    Fin.fromBits? size index.toBits = some index := by
  have hfits : index.val < 2 ^ Fin.bitWidth size :=
    lt_of_lt_of_le index.isLt
      (Nat.le_pow_clog Nat.one_lt_two size)
  unfold Fin.fromBits?
  rw [Fin.length_toBits, dite_eq_left rfl]
  simp only [Fin.toBits]
  simp [Nat.fromBits_toBits hfits, index.isLt]

/-- Successful finite-index decoding recovers the exact fixed-width input.
@isnad1 id=eq.1h3v.s4.2347eece7b4e from=translated src=- shape=7eefc02f vocab=0ee8b94b
-/
theorem Fin.toBits_eq_of_fromBits?_eq_some
    {size : ℕ} {bits : List Bool} {index : Fin size}
    (hdecode : Fin.fromBits? size bits = some index) :
    index.toBits = bits := by
  unfold Fin.fromBits? at hdecode
  split at hdecode
  · rename_i hlength
    split at hdecode
    · cases hdecode
      simp only [Fin.toBits]
      rw [← hlength]
      exact Nat.toBits_fromBits bits
    · simp at hdecode
  · simp at hdecode

/-- Finite-index decoding fails exactly on a malformed width or an
out-of-range decoded value.
@isnad1 id=iff.0h2v.s4.f4fd6ae6769c from=translated src=- shape=dc90c311 vocab=3b95c476
-/
theorem Fin.fromBits?_eq_none_iff (size : ℕ) (bits : List Bool) :
    Fin.fromBits? size bits = none ↔
      bits.length ≠ Fin.bitWidth size ∨ size ≤ Nat.fromBits bits := by
  by_cases hlength : bits.length = Fin.bitWidth size
  · simp [Fin.fromBits?, hlength]
  · simp [Fin.fromBits?, hlength]
