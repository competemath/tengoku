/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Repetition.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Repetition.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Internal

/-!
# Boolean repetition codes

This is the first concrete finite linear code in the metacomplexity coding
layer. Repeating every message bit `copies > 0` times multiplies every Hamming
distance by exactly `copies`, giving a minimum-distance lower bound of `copies`,
unique decoding below half that distance, and a specialized finite packing
inequality.
-/

public section

namespace Complexity

namespace BooleanCode

/-- Repetition encoding at a canonical product coordinate reads the selected
message bit.
@isnad1 id=eq.0h4v.s7.b9620fc3660e from=translated src=- shape=68baf0bf vocab=47d005f7
-/
@[simp] theorem repetitionEncode_apply {messageLength copies : ℕ}
    (message : BooleanHamming.Word messageLength)
    (coordinate : Fin (messageLength * copies)) :
    repetitionEncode messageLength copies message coordinate =
      message (finProdFinEquiv.symm coordinate).1 :=
  repetitionEncode_apply_internal message coordinate

/-- Positive-copy repetition encoding is injective.
@isnad1 id=injectiv.1h2v.s4.eac5c207dcea from=translated src=- shape=6c8b7ae2 vocab=3fa2a8e6
-/
theorem repetitionEncode_injective {messageLength copies : ℕ}
    (hcopies : 0 < copies) :
    Function.Injective (repetitionEncode messageLength copies) :=
  repetitionEncode_injective_internal hcopies

/-- Repetition multiplies absolute Hamming distance by the copy count.
@isnad1 id=eq.0h4v.s5.6383a5cfbf76 from=translated src=- shape=390d8e0c vocab=c6bde152
-/
theorem distance_repetitionEncode {messageLength copies : ℕ}
    (left right : BooleanHamming.Word messageLength) :
    BooleanHamming.distance
      (repetitionEncode messageLength copies left)
      (repetitionEncode messageLength copies right) =
        BooleanHamming.distance left right * copies :=
  distance_repetitionEncode_internal left right

/-- The repetition encoder preserves zero and coordinatewise XOR.
@isnad1 id=and.0h2v.s6.34fed7a4ff03 from=translated src=- shape=2b70dc0b vocab=f518381c
-/
theorem repetitionEncode_isLinear {messageLength copies : ℕ} :
    repetitionEncode messageLength copies (zeroWord messageLength) =
        zeroWord (messageLength * copies) ∧
      ∀ left right,
        repetitionEncode messageLength copies (xorWords left right) =
          xorWords (repetitionEncode messageLength copies left)
            (repetitionEncode messageLength copies right) :=
  repetitionEncode_isLinear_internal

/-- Concrete positive-copy repetition code. -/
def repetitionCode (messageLength copies : ℕ) (hcopies : 0 < copies) :
    BooleanCode messageLength (messageLength * copies) where
  encode := repetitionEncode messageLength copies
  encode_injective := repetitionEncode_injective hcopies

/-- The concrete repetition code is linear over `GF(2)`.
@isnad1 id=islinear.1h2v.s4.cc6ed0872e29 from=translated src=- shape=36ac3950 vocab=14f1fbfc
-/
theorem repetitionCode_isLinear {messageLength copies : ℕ}
    (hcopies : 0 < copies) :
    (repetitionCode messageLength copies hcopies).IsLinear :=
  repetitionEncode_isLinear

/-- At positive message length and copy count, the repetition-code rate is
exactly the reciprocal of the copy count.
@isnad1 id=eq.2h2v.s5.8ce18ec85a94 from=translated src=- shape=0796df3c vocab=05bfee39
-/
theorem repetitionCode_rate {messageLength copies : ℕ}
    (hmessageLength : 0 < messageLength) (hcopies : 0 < copies) :
    rate messageLength (messageLength * copies) = 1 / copies := by
  unfold rate
  push_cast
  have hmessageLength' : (messageLength : ℚ) ≠ 0 := by
    exact_mod_cast hmessageLength.ne'
  have hcopies' : (copies : ℚ) ≠ 0 := by
    exact_mod_cast hcopies.ne'
  field_simp

/-- A positive-copy repetition code has minimum distance at least `copies`.
@isnad1 id=hasminim.1h2v.s4.6825046617b3 from=translated src=- shape=004a93ad vocab=ff7cda34
-/
theorem repetitionCode_hasMinimumDistance {messageLength copies : ℕ}
    (hcopies : 0 < copies) :
    (repetitionCode messageLength copies hcopies).HasMinimumDistance copies := by
  intro left right hne
  rw [repetitionCode, distance_repetitionEncode]
  have hdistance : 1 ≤ BooleanHamming.distance left right := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    exact hne <|
      (BooleanHamming.distance_eq_zero_iff_internal left right).mp hzero
  simpa using Nat.mul_le_mul_right copies hdistance

/-- Repetition decoding recovers a message from every received word within a
radius strictly below half the copy count.
@isnad1 id=eq.3h5v.s6.56a85ae9df9b from=translated src=- shape=f1b8d166 vocab=1aa95c3d
-/
theorem repetitionCode_decodeUnique?_eq_some_of_close
    {messageLength copies radius : ℕ} (hcopies : 0 < copies)
    (hradius : 2 * radius < copies)
    (received : BooleanHamming.Word (messageLength * copies))
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance
      ((repetitionCode messageLength copies hcopies).encode message)
      received ≤ radius) :
    (repetitionCode messageLength copies hcopies).decodeUnique?
      received radius = some message :=
  decodeUnique?_eq_some_of_close_internal
    (repetitionCode_hasMinimumDistance hcopies) hradius
      received message hclose

/-- Specialized packing inequality for the concrete repetition code.
@isnad1 id=le.2h3v.s6.f72a22f35b30 from=translated src=- shape=d92e7d02 vocab=a3aa5935
-/
theorem repetitionCode_packing_bound
    {messageLength copies radius : ℕ} (hcopies : 0 < copies)
    (hradius : 2 * radius < copies) :
    2 ^ messageLength *
        BooleanHamming.volume (messageLength * copies) radius ≤
      2 ^ (messageLength * copies) :=
  packing_bound_internal (repetitionCode_hasMinimumDistance hcopies) hradius

end BooleanCode

end Complexity
