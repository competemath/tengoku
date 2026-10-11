import Tengoku.BtcVerified.BtcVerified.Serialize.Codec
/-!
  # Width-indexed byte strings

  Some Bitcoin fields are uninterpreted byte strings whose width is part of
  their wire format. `Bytes n` records that width in the type while retaining
  the repository's specification-level `List UInt8` representation. The
  checked constructors are the boundary from untrusted variable-length bytes;
  after one succeeds, downstream definitions cannot forget the width.

  The codec consumes exactly `n` bytes. Its round-trip and canonicality laws
  make width-indexed byte strings available as a primitive for larger codecs.

  Checked claims:

  * each checked constructor is characterized by its exact acceptance condition
    and returned byte list;
  * reversal preserves width, is involutive, and exchanges left-oriented
    padding and truncation with right-oriented operations on the reversed input;
  * padding and truncation success depend only on input width, not direction;
  * successful padding has the stated padding region and boundary byte, and
    same-side truncation back to the original width recovers the input;
  * for either direction, exactly one list constructor succeeds: padding when
    the input is short, exact conversion when widths agree, or truncation when
    the input is long;
  * `instCodecBytes`: width-indexed bytes round-trip and every accepted parse
    consumes exactly their canonical `n`-byte encoding.
-/

namespace BtcVerified

/-- A byte string whose width is fixed at `n`. -/
abbrev Bytes (n : Nat) := { bytes : List UInt8 // bytes.length = n }

/-- The underlying bytes, in their original order. -/
@[reducible] def Bytes.bytes {n : Nat} (bs : Bytes n) : List UInt8 := bs.1

/-- Reverse byte order while preserving width. -/
def Bytes.reverse {n : Nat} (bs : Bytes n) : Bytes n :=
  ⟨bs.1.reverse, by simpa only [List.length_reverse] using bs.2⟩

/-- Reversal acts on the underlying byte list.
@isnad1 id=eq.0h2v.s5.03f795a608e7 from=translated src=- shape=b0aecebb vocab=72430137
-/
@[simp] theorem Bytes.val_reverse {n : Nat} (bs : Bytes n) :
    bs.reverse.val = bs.val.reverse := rfl

/-- Reversing a width-indexed byte string twice returns the original value.
@isnad1 id=eq.0h2v.s3.52ce458f81d0 from=translated src=- shape=6ddf6d3e vocab=2f1214e7
-/
@[simp] theorem Bytes.reverse_reverse {n : Nat} (bs : Bytes n) :
    bs.reverse.reverse = bs := by
  exact Subtype.ext (List.reverse_reverse bs.val)

/-- Refine a list when it has exactly the required width. -/
def Bytes.ofListExact? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : bs.length = n then some ⟨bs, h⟩ else none

/-- Exact conversion succeeds with `out` precisely when the width agrees and
`out` contains the original bytes.
@isnad1 id=iff.0h3v.s5.78a89a8c7489 from=translated src=- shape=4d72d2b0 vocab=19b1b81c
-/
theorem Bytes.ofListExact?_eq_some_iff {n : Nat} (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListExact? bs = some out ↔ bs.length = n ∧ out.val = bs := by
  simp [Bytes.ofListExact?, Subtype.ext_iff, eq_comm]

/-- Exact conversion succeeds exactly at the required width.
@isnad1 id=iff.0h2v.s4.895b5f84dccc from=translated src=- shape=58f7dc24 vocab=92c7fa86
-/
@[simp] theorem Bytes.ofListExact?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListExact? (n := n) bs).isSome ↔ bs.length = n := by
  simp [Bytes.ofListExact?]

/-- Exact conversion rejects exactly the lists of the wrong width.
@isnad1 id=iff.0h2v.s4.dd89fcd9a454 from=translated src=- shape=cebec7eb vocab=d18a8389
-/
@[simp] theorem Bytes.ofListExact?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListExact? (n := n) bs = none ↔ bs.length ≠ n := by
  simpa only [Option.not_isSome_iff_eq_none] using
    not_congr (Bytes.ofListExact?_isSome_iff bs)

/-- Refining the underlying list of width-indexed bytes recovers the original value.
@isnad1 id=eq.0h2v.s4.d466ad3b709f from=translated src=- shape=252b1777 vocab=19b1b81c
-/
@[simp] theorem Bytes.ofListExact?_val {n : Nat} (bs : Bytes n) :
    Bytes.ofListExact? bs.val = some bs := by
  exact (Bytes.ofListExact?_eq_some_iff bs.val bs).2 ⟨bs.property, rfl⟩

/-- Exact conversion commutes with reversal.
@isnad1 id=eq.0h2v.s4.2e908b1b9fad from=translated src=- shape=72047af9 vocab=f5bd402e
-/
theorem Bytes.ofListExact?_map_reverse {n : Nat} (bs : List UInt8) :
    (Bytes.ofListExact? (n := n) bs).map Bytes.reverse =
      Bytes.ofListExact? (n := n) bs.reverse := by
  by_cases h : bs.length = n <;> simp [Bytes.ofListExact?, Bytes.reverse, h]

/-- Pad a list on the left to the required width. Succeeds only when the input
is strictly shorter; the padding byte is explicit. -/
def Bytes.ofListPadLeft? {n : Nat} (padding : UInt8) (bs : List UInt8) :
    Option (Bytes n) :=
  if h : bs.length < n then
    some ⟨List.replicate (n - bs.length) padding ++ bs,
      by simpa using Nat.sub_add_cancel (Nat.le_of_lt h)⟩
  else none

/-- Pad a list on the right to the required width. Succeeds only when the input
is strictly shorter; the padding byte is explicit. -/
def Bytes.ofListPadRight? {n : Nat} (padding : UInt8) (bs : List UInt8) :
    Option (Bytes n) :=
  if h : bs.length < n then
    some ⟨bs ++ List.replicate (n - bs.length) padding,
      by simpa using Nat.add_sub_of_le (Nat.le_of_lt h)⟩
  else none

/-- Left padding succeeds with `out` precisely when the input is short and
`out` is the required padding prefix followed by the original bytes.
@isnad1 id=iff.0h4v.s6.18392c32c119 from=translated src=- shape=3a53e416 vocab=7a9a76d7
-/
theorem Bytes.ofListPadLeft?_eq_some_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListPadLeft? padding bs = some out ↔
      bs.length < n ∧
        out.val = List.replicate (n - bs.length) padding ++ bs := by
  simp [Bytes.ofListPadLeft?, Subtype.ext_iff, eq_comm]

/-- Right padding succeeds with `out` precisely when the input is short and
`out` is the original bytes followed by the required padding suffix.
@isnad1 id=iff.0h4v.s6.a7c08fd53940 from=translated src=- shape=89f385a0 vocab=94adccc5
-/
theorem Bytes.ofListPadRight?_eq_some_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListPadRight? padding bs = some out ↔
      bs.length < n ∧
        out.val = bs ++ List.replicate (n - bs.length) padding := by
  simp [Bytes.ofListPadRight?, Subtype.ext_iff, eq_comm]

/-- Left padding succeeds exactly for inputs shorter than the target width.
@isnad1 id=iff.0h3v.s4.e196da904111 from=translated src=- shape=7966f4af vocab=709194ba
-/
@[simp] theorem Bytes.ofListPadLeft?_isSome_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).isSome ↔ bs.length < n := by
  simp [Bytes.ofListPadLeft?]

/-- Right padding succeeds exactly for inputs shorter than the target width.
@isnad1 id=iff.0h3v.s4.2857800c6926 from=translated src=- shape=7966f4af vocab=d3174180
-/
@[simp] theorem Bytes.ofListPadRight?_isSome_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    (Bytes.ofListPadRight? (n := n) padding bs).isSome ↔ bs.length < n := by
  simp [Bytes.ofListPadRight?]

/-- Left padding rejects exactly the inputs at least as wide as the target.
@isnad1 id=iff.0h3v.s4.8b9d01f03e98 from=translated src=- shape=1bdd28f9 vocab=1cdf1aff
-/
@[simp] theorem Bytes.ofListPadLeft?_eq_none_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    Bytes.ofListPadLeft? (n := n) padding bs = none ↔ n ≤ bs.length := by
  simpa only [Option.not_isSome_iff_eq_none, Nat.not_lt] using
    not_congr (Bytes.ofListPadLeft?_isSome_iff padding bs)

/-- Right padding rejects exactly the inputs at least as wide as the target.
@isnad1 id=iff.0h3v.s4.6ad17d56cd1a from=translated src=- shape=1bdd28f9 vocab=4a25aff3
-/
@[simp] theorem Bytes.ofListPadRight?_eq_none_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    Bytes.ofListPadRight? (n := n) padding bs = none ↔ n ≤ bs.length := by
  simpa only [Option.not_isSome_iff_eq_none, Nat.not_lt] using
    not_congr (Bytes.ofListPadRight?_isSome_iff padding bs)

/-- A successful left padding consists of exactly the inserted padding prefix
followed by the original input.
@isnad1 id=and.1h4v.s6.db3f94a9737a from=translated src=- shape=d3c45cec vocab=e58fa8c9
-/
theorem Bytes.parts_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    out.val.take (n - bs.length) = List.replicate (n - bs.length) padding ∧
      out.val.drop (n - bs.length) = bs := by
  simp [(Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h |>.2]

/-- A successful right padding consists of the original input followed by
exactly the inserted padding suffix.
@isnad1 id=and.1h4v.s6.532d5cefbff1 from=translated src=- shape=10bab350 vocab=ca81de2e
-/
theorem Bytes.parts_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    out.val.take bs.length = bs ∧
      out.val.drop bs.length = List.replicate (n - bs.length) padding := by
  simp [(Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h |>.2]

/-- Successful left padding places the padding byte first.
@isnad1 id=eq.1h4v.s5.5307b1ab044b from=translated src=- shape=6b79d22c vocab=e85d9c22
-/
theorem Bytes.head?_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    out.val.head? = some padding := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h
  simp [hout, List.head?_replicate, (Nat.sub_ne_zero_iff_lt).2 hlen]

/-- Successful right padding places the padding byte last.
@isnad1 id=eq.1h4v.s5.0f70fab7d857 from=translated src=- shape=6b79d22c vocab=4909848c
-/
theorem Bytes.getLast?_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    out.val.getLast? = some padding := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h
  simp [hout, List.getLast?_replicate, (Nat.sub_ne_zero_iff_lt).2 hlen]

/-- Reversing a left-padded result is right padding of the reversed input.
@isnad1 id=eq.0h3v.s4.06a17f09ff54 from=translated src=- shape=fc6fc8a2 vocab=e224ad55
-/
theorem Bytes.ofListPadLeft?_map_reverse {n : Nat} (padding : UInt8) (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).map Bytes.reverse =
      Bytes.ofListPadRight? (n := n) padding bs.reverse := by
  by_cases h : bs.length < n <;>
    simp [Bytes.ofListPadLeft?, Bytes.ofListPadRight?, Bytes.reverse, h]

/-- Truncate a list on the left to the required width: drop its prefix and keep
the rightmost `n` bytes. Succeeds only when the input is strictly longer. -/
def Bytes.ofListTruncateLeft? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : n < bs.length then
    some ⟨bs.drop (bs.length - n), by simpa using Nat.sub_sub_self (Nat.le_of_lt h)⟩
  else none

/-- Truncate a list on the right to the required width: drop its suffix and
keep the leftmost `n` bytes. Succeeds only when the input is strictly longer. -/
def Bytes.ofListTruncateRight? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : n < bs.length then
    some ⟨bs.take n, List.length_take_of_le (Nat.le_of_lt h)⟩
  else none

/-- Left truncation succeeds with `out` precisely when the input is long and
`out` contains its rightmost `n` bytes.
@isnad1 id=iff.0h3v.s5.96c202b7d0e7 from=translated src=- shape=a34dc1ec vocab=654a1766
-/
theorem Bytes.ofListTruncateLeft?_eq_some_iff {n : Nat} (bs : List UInt8)
    (out : Bytes n) :
    Bytes.ofListTruncateLeft? bs = some out ↔
      n < bs.length ∧ out.val = bs.drop (bs.length - n) := by
  simp [Bytes.ofListTruncateLeft?, Subtype.ext_iff, eq_comm]

/-- Right truncation succeeds with `out` precisely when the input is long and
`out` contains its leftmost `n` bytes.
@isnad1 id=iff.0h3v.s5.94d09d1a6a4a from=translated src=- shape=6ebff8bf vocab=fcdf4e1d
-/
theorem Bytes.ofListTruncateRight?_eq_some_iff {n : Nat} (bs : List UInt8)
    (out : Bytes n) :
    Bytes.ofListTruncateRight? bs = some out ↔
      n < bs.length ∧ out.val = bs.take n := by
  simp [Bytes.ofListTruncateRight?, Subtype.ext_iff, eq_comm]

/-- Left truncation succeeds exactly for inputs longer than the target width.
@isnad1 id=iff.0h2v.s4.4f35cf8e93cf from=translated src=- shape=706b0352 vocab=323346fc
-/
@[simp] theorem Bytes.ofListTruncateLeft?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).isSome ↔ n < bs.length := by
  simp [Bytes.ofListTruncateLeft?]

/-- Right truncation succeeds exactly for inputs longer than the target width.
@isnad1 id=iff.0h2v.s4.97ca7cb9eb74 from=translated src=- shape=706b0352 vocab=08a13019
-/
@[simp] theorem Bytes.ofListTruncateRight?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateRight? (n := n) bs).isSome ↔ n < bs.length := by
  simp [Bytes.ofListTruncateRight?]

/-- Left truncation rejects exactly the inputs no longer than the target.
@isnad1 id=iff.0h2v.s4.767037538225 from=translated src=- shape=cebec7eb vocab=1c8afd0f
-/
@[simp] theorem Bytes.ofListTruncateLeft?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListTruncateLeft? (n := n) bs = none ↔ bs.length ≤ n := by
  simpa only [Option.not_isSome_iff_eq_none, Nat.not_lt] using
    not_congr (Bytes.ofListTruncateLeft?_isSome_iff bs)

/-- Right truncation rejects exactly the inputs no longer than the target.
@isnad1 id=iff.0h2v.s4.3d73963be4a9 from=translated src=- shape=cebec7eb vocab=284ae41c
-/
@[simp] theorem Bytes.ofListTruncateRight?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListTruncateRight? (n := n) bs = none ↔ bs.length ≤ n := by
  simpa only [Option.not_isSome_iff_eq_none, Nat.not_lt] using
    not_congr (Bytes.ofListTruncateRight?_isSome_iff bs)

/-- Reversing a left-truncated result is right truncation of the reversed input.
@isnad1 id=eq.0h2v.s4.73c2279525f4 from=translated src=- shape=155a8e68 vocab=0dfbef09
-/
theorem Bytes.ofListTruncateLeft?_map_reverse {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).map Bytes.reverse =
      Bytes.ofListTruncateRight? (n := n) bs.reverse := by
  by_cases h : n < bs.length
  · simp [Bytes.ofListTruncateLeft?, Bytes.ofListTruncateRight?, Bytes.reverse, h,
      List.reverse_drop, Nat.sub_sub_self (Nat.le_of_lt h)]
  · simp [Bytes.ofListTruncateLeft?, Bytes.ofListTruncateRight?, h]

/-- Truncating a successful left padding back to the input width recovers the
exact conversion of the original input.
@isnad1 id=eq.1h4v.s5.f05dffe02d44 from=translated src=- shape=719f9f5d vocab=50de4a9e
-/
theorem Bytes.ofListTruncateLeft?_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    Bytes.ofListTruncateLeft? (n := bs.length) out.val =
      Bytes.ofListExact? (n := bs.length) bs := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h
  simp [hout, Bytes.ofListTruncateLeft?, Bytes.ofListExact?, Nat.sub_pos_of_lt hlen]

/-- Truncating a successful right padding back to the input width recovers the
exact conversion of the original input.
@isnad1 id=eq.1h4v.s5.a433991874b9 from=translated src=- shape=719f9f5d vocab=3b4a4be0
-/
theorem Bytes.ofListTruncateRight?_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    Bytes.ofListTruncateRight? (n := bs.length) out.val =
      Bytes.ofListExact? (n := bs.length) bs := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h
  simp [hout, Bytes.ofListTruncateRight?, Bytes.ofListExact?, Nat.sub_pos_of_lt hlen]

/-- Left and right padding succeed on exactly the same inputs.
@isnad1 id=eq.0h3v.s4.ea9bbf795f79 from=translated src=- shape=385e42e9 vocab=4493b295
-/
theorem Bytes.ofListPad_isSome_eq {n : Nat} (padding : UInt8) (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).isSome =
      (Bytes.ofListPadRight? (n := n) padding bs).isSome := by
  exact Bool.eq_iff_iff.mpr <| (Bytes.ofListPadLeft?_isSome_iff padding bs).trans
    (Bytes.ofListPadRight?_isSome_iff padding bs).symm

/-- Left and right truncation succeed on exactly the same inputs.
@isnad1 id=eq.0h2v.s4.d6c0fb873b30 from=translated src=- shape=7d47cc24 vocab=8bcc3188
-/
theorem Bytes.ofListTruncate_isSome_eq {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).isSome =
      (Bytes.ofListTruncateRight? (n := n) bs).isSome := by
  exact Bool.eq_iff_iff.mpr <| (Bytes.ofListTruncateLeft?_isSome_iff bs).trans
    (Bytes.ofListTruncateRight?_isSome_iff bs).symm

/-- For left-oriented conversion, exactly one of padding, exact conversion,
and truncation succeeds.
@isnad1 id=eq.0h3v.s5.0c5a0f4d79f1 from=translated src=- shape=21c4b242 vocab=2db5dee0
-/
theorem Bytes.ofList_left_exactly_one {n : Nat} (padding : UInt8) (bs : List UInt8) :
    [(Bytes.ofListPadLeft? (n := n) padding bs).isSome,
      (Bytes.ofListExact? (n := n) bs).isSome,
      (Bytes.ofListTruncateLeft? (n := n) bs).isSome].count true = 1 := by
  rcases Nat.lt_trichotomy bs.length n with h | h | h
  · have ⟨hne, hnlt⟩ : bs.length ≠ n ∧ ¬ n < bs.length := by omega
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?, h, hne, hnlt]
  · subst n
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?]
  · have ⟨hnlt, hne⟩ : ¬ bs.length < n ∧ bs.length ≠ n := by omega
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?, h, hnlt, hne]

/-- For right-oriented conversion, exactly one of padding, exact conversion,
and truncation succeeds.
@isnad1 id=eq.0h3v.s5.dd924526af67 from=translated src=- shape=21c4b242 vocab=a56ebc17
-/
theorem Bytes.ofList_right_exactly_one {n : Nat} (padding : UInt8) (bs : List UInt8) :
    [(Bytes.ofListPadRight? (n := n) padding bs).isSome,
      (Bytes.ofListExact? (n := n) bs).isSome,
      (Bytes.ofListTruncateRight? (n := n) bs).isSome].count true = 1 := by
  simpa only [← Bytes.ofListPad_isSome_eq padding bs,
    ← Bytes.ofListTruncate_isSome_eq bs] using Bytes.ofList_left_exactly_one padding bs

/-- A width-indexed byte string has the width recorded in its type.
@isnad1 id=eq.0h2v.s4.526fd7e33e91 from=translated src=- shape=00911053 vocab=dbcc8def
-/
@[local simp] theorem Bytes.length_val {n : Nat} (bs : Bytes n) : bs.1.length = n := bs.2

namespace Serialize

/-- Decode exactly `n` bytes from the front of the input. -/
def decodeBytes (n : Nat) (bs : List UInt8) : Option (Bytes n × List UInt8) :=
  if h : n ≤ bs.length then
    some (⟨bs.take n, List.length_take_of_le h⟩, bs.drop n)
  else none

/-- Width-indexed bytes serialize as themselves and decode by consuming exactly
the width recorded in their type. -/
instance instCodecBytes (n : Nat) : Codec (Bytes n) where
  encode bs := bs.1
  decode := decodeBytes n
  decode_encode bs rest := by
    simp [decodeBytes]
  decode_canonical bs value rest hdec := by
    simp only [decodeBytes] at hdec
    split at hdec
    · simp only [Option.some.injEq, Prod.mk.injEq, Subtype.ext_iff] at hdec
      rw [← hdec.2, ← hdec.1, List.take_append_drop]
    · simp at hdec

/-- Width-indexed bytes encode to exactly the width recorded in their type.
@isnad1 id=eq.0h2v.s4.6b84dbb118fc from=translated src=- shape=99cf8acf vocab=cc719e2b
-/
theorem Bytes.encode_length {n : Nat} (bs : Bytes n) :
    (Codec.encode bs).length = n := Bytes.length_val bs

end Serialize

end BtcVerified
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
