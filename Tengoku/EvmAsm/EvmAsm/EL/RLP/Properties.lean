/-
  EvmAsm.EL.RLP.Properties

  Round-trip correctness: `decode (encode item) = some (item, [])`.
-/
-- `Decode` transitively imports `Basic`.
module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Decode
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.PrefixDecode
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.ReadLength
public import Tengoku.EvmAsm.EvmAsm.EL.RLP.FullDecode
public import Tengoku.Seed.Data.List.Induction
public import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

public section

namespace EvmAsm.EL.RLP

/-! ## Nat.toBytesBE / fromBytesBE properties -/

/--
@isnad1 id=eq.0h0v.s3.f1b9180c4653 from=translated src=- shape=58b8d025 vocab=7c42bde3
-/
theorem Nat.toBytesBE_zero : Nat.toBytesBE 0 = [] := by
  simp [Nat.toBytesBE]

/--
@isnad1 id=eq.0h0v.s3.e77e1d30782f from=translated src=- shape=35225b15 vocab=8b5f9eca
-/
theorem Nat.fromBytesBE_nil : Nat.fromBytesBE [] = 0 := by
  simp [Nat.fromBytesBE]

/-- The big-endian decode of `bs` is bounded by `256 ^ bs.length`: each byte is
    `< 256`, so an `n`-byte sequence decodes to a value `< 256 ^ n`.
@isnad1 id=lt.0h1v.s4.8f5ef4a76aeb from=translated src=- shape=00b51492 vocab=d75fc8ec
-/
theorem Nat.fromBytesBE_lt (bs : List Byte) :
    Nat.fromBytesBE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [Nat.fromBytesBE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := by have := b.isLt; omega
    have e : Nat.fromBytesBE (b :: bs)
        = b.toNat * 256 ^ bs.length + Nat.fromBytesBE bs := rfl
    have hsucc : b.toNat * 256 ^ bs.length + 256 ^ bs.length
        = (b.toNat + 1) * 256 ^ bs.length := (Nat.succ_mul _ _).symm
    have hle : (b.toNat + 1) * 256 ^ bs.length ≤ 256 * 256 ^ bs.length :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have hpow : 256 * 256 ^ bs.length = 256 ^ (b :: bs).length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm]
    -- `ih : fromBytesBE bs < 256 ^ bs.length`, with the linear facts above,
    -- omega chains: fromBytesBE (b::bs) < (b+1)·256^L ≤ 256·256^L = 256^(L+1).
    omega

/-- One-step unfold of `Nat.toBytesBE` at a successor: the low byte is appended
    last (least significant), with the higher digits encoded recursively.
@isnad1 id=eq.0h1v.s6.99159e1461ce from=translated src=- shape=ce8d92ce vocab=dcb4d784
-/
theorem Nat.toBytesBE_succ (n : Nat) :
    Nat.toBytesBE (n + 1)
      = Nat.toBytesBE ((n + 1) / 256) ++ [BitVec.ofNat 8 ((n + 1) % 256)] := by
  rw [Nat.toBytesBE]

/-- Big-endian decode of a snoc list: appending a low-order byte `b` shifts the
    decoded value up by one base-256 digit. `fromBytesBE` recurses on the head,
    so this is proved by induction on the prefix `xs`.
@isnad1 id=eq.0h2v.s5.7283b950afe2 from=translated src=- shape=e45e13d6 vocab=08c7ba7b
-/
theorem Nat.fromBytesBE_snoc (xs : List Byte) (b : Byte) :
    Nat.fromBytesBE (xs ++ [b]) = Nat.fromBytesBE xs * 256 + b.toNat := by
  induction xs with
  | nil => simp [Nat.fromBytesBE]
  | cons c cs ih =>
    have hlen : (cs ++ [b]).length = cs.length + 1 := by simp
    have key : Nat.fromBytesBE ((c :: cs) ++ [b])
        = c.toNat * 256 ^ (cs ++ [b]).length + Nat.fromBytesBE (cs ++ [b]) := rfl
    have hcons : Nat.fromBytesBE (c :: cs)
        = c.toNat * 256 ^ cs.length + Nat.fromBytesBE cs := rfl
    have hassoc : c.toNat * (256 ^ cs.length * 256)
        = c.toNat * 256 ^ cs.length * 256 := (Nat.mul_assoc _ _ _).symm
    rw [key, ih, hlen, Nat.pow_succ, hcons, Nat.add_mul, hassoc]
    omega

/-- Big-endian round-trip: decoding the minimal big-endian encoding of `n`
    recovers `n`. Induction follows `toBytesBE`'s own division recursion
    (`Nat.toBytesBE.induct`), using `fromBytesBE_snoc` for the appended low byte
    and `Nat.div_add_mod` (via `omega`) to reassemble `n`.
@isnad1 id=eq.0h1v.s3.43d9e141c2d3 from=translated src=- shape=47dcad53 vocab=4d9600f0
-/
theorem Nat.fromBytesBE_toBytesBE (n : Nat) :
    Nat.fromBytesBE (Nat.toBytesBE n) = n := by
  induction n using Nat.toBytesBE.induct with
  | case1 => simp [Nat.toBytesBE, Nat.fromBytesBE]
  | case2 m _hlt ih =>
    rw [Nat.toBytesBE_succ, Nat.fromBytesBE_snoc, ih]
    have hr : (BitVec.ofNat 8 ((m + 1) % 256)).toNat = (m + 1) % 256 := by
      simp only [BitVec.toNat_ofNat]; omega
    rw [hr]
    omega

/-- **Big-endian zero is length-insensitive**: a big-endian byte string decodes
    to `0` exactly when every one of its bytes is zero — for *any* length, so
    non-canonical zero encodings (`0x00`, `0x00 0x00`, …) all decode to `0`
    alongside the empty string.

    Consumed by #11346: the guest's EIP-161 nonce/balance test is the lenient
    "every content byte is zero" (`beAccum_eq_zero_iff`), and this says the
    reference's `bytesBEtoNat` is lenient in exactly the same way.  That makes
    the agreement a proved fact rather than a coincidence worth a comment.
@isnad1 id=iff.0h1v.s5.ab1e27fe552c from=translated src=- shape=4cf0bb53 vocab=5a931d04
-/
theorem Nat.fromBytesBE_eq_zero_iff : ∀ (bs : List Byte),
    Nat.fromBytesBE bs = 0 ↔ ∀ b ∈ bs, b = 0
  | [] => by simp [Nat.fromBytesBE]
  | b :: bs => by
      have hpow : 256 ^ bs.length ≠ 0 := by positivity
      show b.toNat * 256 ^ bs.length + Nat.fromBytesBE bs = 0 ↔ _
      constructor
      · intro h
        obtain ⟨hmul, hrec⟩ := Nat.add_eq_zero_iff.mp h
        have hb0 : b.toNat = 0 := (Nat.mul_eq_zero.mp hmul).resolve_right hpow
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact BitVec.eq_of_toNat_eq (by simp [hb0])
        · exact (Nat.fromBytesBE_eq_zero_iff bs).mp hrec x hx'
      · intro h
        have hb : b = 0 := h b (List.mem_cons_self ..)
        have hrec : Nat.fromBytesBE bs = 0 :=
          (Nat.fromBytesBE_eq_zero_iff bs).mpr fun x hx => h x (List.mem_cons_of_mem _ hx)
        rw [hb, hrec]
        simp

/-- 8-bit `ofNat ∘ toNat` is the identity.-/
private theorem ofNat8_toNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt]

/-- The big-endian decode of a list with a nonzero leading byte is positive.
@isnad1 id=lt.1h2v.s5.19361c4aac34 from=translated src=- shape=259d24df vocab=1bfbc6fa
-/
theorem Nat.fromBytesBE_pos_of_head_ne_zero (b : Byte) (tl : List Byte)
    (hb : b ≠ 0) : 0 < Nat.fromBytesBE (b :: tl) := by
  have hbn : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h) hb
    · exact h
  have hmul : 0 < b.toNat * 256 ^ tl.length := Nat.mul_pos hbn (by positivity)
  have he : Nat.fromBytesBE (b :: tl)
      = b.toNat * 256 ^ tl.length + Nat.fromBytesBE tl := rfl
  omega

/-- Canonical inverse of the big-endian bijection: a byte list with a nonzero
    leading byte (no leading zeros) is recovered by `toBytesBE ∘ fromBytesBE`.
    `headD 1` makes `[]` vacuously canonical (`toBytesBE (fromBytesBE []) = []`).
    Reverse (snoc) induction (`List.reverseRecOn`) matches `toBytesBE`'s
    low-byte-last recursion.
@isnad1 id=eq.1h1v.s5.0c180d92cedb from=translated src=- shape=74f90f7e vocab=cd74cd77
-/
theorem Nat.toBytesBE_fromBytesBE_of_canonical :
    ∀ (bs : List Byte), bs.headD 1 ≠ 0 → Nat.toBytesBE (Nat.fromBytesBE bs) = bs := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => intro _; simp [Nat.fromBytesBE, Nat.toBytesBE]
  | append_singleton xs b ih =>
    intro h
    have hxs : xs.headD 1 ≠ 0 := by
      cases xs with
      | nil => simp
      | cons y ys => simpa using h
    have ihxs := ih hxs
    have hblt : b.toNat < 256 := by simpa using b.isLt
    rw [Nat.fromBytesBE_snoc]
    have hk0 : Nat.fromBytesBE xs * 256 + b.toNat ≠ 0 := by
      cases xs with
      | nil =>
        simp only [List.nil_append] at h
        have hb0 : b.toNat ≠ 0 := fun hh =>
          h (BitVec.eq_of_toNat_eq (by simpa using hh))
        simp only [Nat.fromBytesBE]; omega
      | cons y ys =>
        have hy : y ≠ 0 := by simpa using h
        have := Nat.fromBytesBE_pos_of_head_ne_zero y ys hy
        omega
    obtain ⟨k', hk'⟩ : ∃ k', Nat.fromBytesBE xs * 256 + b.toNat = k' + 1 :=
      ⟨Nat.fromBytesBE xs * 256 + b.toNat - 1, by omega⟩
    rw [hk', Nat.toBytesBE_succ, ← hk']
    have hdiv : (Nat.fromBytesBE xs * 256 + b.toNat) / 256
        = Nat.fromBytesBE xs := by omega
    have hmod : (Nat.fromBytesBE xs * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [hdiv, hmod, ihxs, ofNat8_toNat]

/-- Leading zero bytes do not change the big-endian value: each contributes
    `0 * 256 ^ _`. This is the *non-canonical* companion to
    `toBytesBE_fromBytesBE_of_canonical` — that lemma needs a non-zero head, this
    one is about exactly the case it excludes.

    Motivation (#11574): EIP-2537 transmits a BLS12-381 base-field element as a
    **64-byte** wire felt whose first 16 bytes are zero, while the guest's
    `blsg_lt_p` scan reads only the **48** compact bytes. Without this lemma the
    two sides are different lists and any bridge between them would relate
    different objects while typechecking cleanly.
@isnad1 id=eq.1h2v.s5.6506cfd7e234 from=translated src=- shape=ccdd95b1 vocab=bbe462ec
-/
theorem Nat.fromBytesBE_zero_prefix :
    ∀ (zs xs : List Byte), (∀ z ∈ zs, z = 0) →
      Nat.fromBytesBE (zs ++ xs) = Nat.fromBytesBE xs
  | [], _, _ => by simp
  | z :: zs, xs, hz => by
    have hz0 : z = 0 := hz z (List.mem_cons_self ..)
    have he : Nat.fromBytesBE ((z :: zs) ++ xs)
        = z.toNat * 256 ^ (zs ++ xs).length + Nat.fromBytesBE (zs ++ xs) := rfl
    have hrec : Nat.fromBytesBE (zs ++ xs) = Nat.fromBytesBE xs :=
      Nat.fromBytesBE_zero_prefix zs xs fun x hx => hz x (List.mem_cons_of_mem _ hx)
    rw [he, hrec, hz0]
    simp

/-! ## takeBytes properties -/

/-- Taking 0 bytes always succeeds with an empty prefix and the original list.
@isnad1 id=eq.0h1v.s4.b5d3d8edecfe from=translated src=- shape=0a38b706 vocab=6abf2cc2
-/
theorem takeBytes_zero (bs : List Byte) :
    takeBytes bs 0 = some ([], bs) := by
  simp [takeBytes]

/-- Taking more bytes than the list contains returns `none`.
@isnad1 id=eq.1h2v.s4.ed0a06260163 from=translated src=- shape=2f72c818 vocab=9ad5b608
-/
theorem takeBytes_length_lt {bs : List Byte} {n : Nat} (h : bs.length < n) :
    takeBytes bs n = none := by
  simp [takeBytes, Nat.not_le_of_lt h]

/-- When the list is at least `n` bytes long, `takeBytes` returns the obvious split.
@isnad1 id=eq.1h2v.s5.7967e46b6e11 from=translated src=- shape=b8e53196 vocab=6e33294d
-/
theorem takeBytes_length_ge {bs : List Byte} {n : Nat} (h : n ≤ bs.length) :
    takeBytes bs n = some (bs.take n, bs.drop n) := by
  simp [takeBytes, h]

/-- A successful `takeBytes` splits the input into the consumed prefix (of the
    requested length) and the remainder.
@isnad1 id=and.1h4v.s5.0b87217ab7ab from=translated src=- shape=eea11c56 vocab=511bfeba
-/
theorem takeBytes_eq_some_imp {xs a b : List Byte} {k : Nat}
    (h : takeBytes xs k = some (a, b)) : xs = a ++ b ∧ a.length = k := by
  unfold takeBytes at h
  split at h
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ha, hb⟩ := h
    subst ha; subst hb
    exact ⟨(List.take_append_drop k xs).symm, by rw [List.length_take]; omega⟩
  · exact absurd h (by simp)

/-! ## readLength properties -/

/-- Reading zero length-bytes always succeeds with length 0 and the input
    list unchanged.
@isnad1 id=eq.0h1v.s4.65dbf83f86ea from=translated src=- shape=55197f6f vocab=685fbde2
-/
theorem readLength_zero (bs : List Byte) :
    readLength bs 0 = some (0, bs) := by
  simp [readLength, takeBytes]

/-- Reading more length-bytes than the input contains returns `none`.
@isnad1 id=eq.1h2v.s4.d78b9a5b17b4 from=translated src=- shape=d0a36956 vocab=f4b73246
-/
theorem readLength_length_lt {bs : List Byte} {n : Nat} (h : bs.length < n) :
    readLength bs n = none := by
  simp [readLength, takeBytes, Nat.not_le_of_lt h]

/-- A successful `readLength` exposes the canonical length field it consumed:
    the `k` length bytes form a prefix that big-endian-decodes to `v`, and (for
    `v > 0`) re-encodes to exactly those bytes (no leading zeros).
@isnad1 id=ex.1h4v.s6.00a58aba2df4 from=translated src=- shape=76bc17e5 vocab=5a3006eb
-/
theorem readLength_eq_some_imp {xs r : List Byte} {k v : Nat}
    (h : readLength xs k = some (v, r)) :
    ∃ lenBytes, xs = lenBytes ++ r ∧ lenBytes.length = k
      ∧ Nat.fromBytesBE lenBytes = v ∧ (0 < v → Nat.toBytesBE v = lenBytes) := by
  cases htk : takeBytes xs k with
  | none => rw [readLength_none_of_takeBytes_none htk] at h; exact absurd h (by simp)
  | some pair =>
    obtain ⟨lenBytes, rest⟩ := pair
    obtain ⟨hsplit, hlen⟩ := takeBytes_eq_some_imp htk
    rw [readLength_eq_of_takeBytes htk] at h
    cases lenBytes with
    | nil =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst hr; subst hv
      exact ⟨[], hsplit, hlen, rfl, fun hpos => absurd hpos (by simp)⟩
    | cons b tl =>
      simp only at h
      by_cases hc : ((b :: tl).length > 1 && b == 0) = true
      · rw [ite_eq_left hc] at h; exact absurd h (by simp)
      · rw [ite_eq_right hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hr
        refine ⟨b :: tl, hsplit, hlen, hv, ?_⟩
        intro hpos
        have hbne : b ≠ 0 := by
          intro hb0
          subst hb0
          simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq] at hc
          have htl : tl = [] := by
            rcases tl with _ | ⟨c, cs⟩
            · rfl
            · simp [List.length_cons] at hc
          subst htl
          rw [← hv] at hpos
          simp [Nat.fromBytesBE] at hpos
        have hcanon := Nat.toBytesBE_fromBytesBE_of_canonical (b :: tl) (by simpa using hbne)
        rw [hv] at hcanon
        exact hcanon

/-! ## decodeAux trivial cases -/

/-- `decodeAux 0` always returns `none` (no nDepth).
@isnad1 id=eq.0h1v.s4.d95af89df661 from=translated src=- shape=69fa0be2 vocab=378a49c3
-/
theorem decodeAux_zero_fuel (bs : List Byte) :
    decodeAux 0 bs = none := by
  simp [decodeAux]

/-- `decodeAux` on an empty stream returns `none` regardless of nDepth.
@isnad1 id=eq.0h1v.s4.02f505e4df10 from=translated src=- shape=4fd92873 vocab=2f9c80da
-/
theorem decodeAux_nil (nDepth : Nat) :
    decodeAux nDepth [] = none := by
  cases nDepth <;> simp [decodeAux]

/-- Single-byte items: when the prefix `p` satisfies `p < 0x80`, `decodeAux`
    succeeds and returns `(.bytes [p], rest)` consuming one byte.
@isnad1 id=eq.1h3v.s5.55901c8f3be9 from=translated src=- shape=5c466480 vocab=d1b081d0
-/
theorem decodeAux_single_byte (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h : pfx.toNat < 0x80) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes [pfx], rest) := by
  simp [decodeAux, h]

/-- Empty short byte string (prefix `0x80`): `decodeAux` returns `(.bytes [], rest)`
    consuming only the prefix byte.
@isnad1 id=eq.0h2v.s5.e9275a04bfc1 from=translated src=- shape=6441c92c vocab=e260c232
-/
theorem decodeAux_empty_string (nDepth : Nat) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0x80 : Byte) :: rest) = some (.bytes [], rest) := by
  simp [decodeAux, takeBytes]

/-- Empty list (prefix `0xC0`): `decodeAux` returns `(.list [], rest)`
    consuming exactly the prefix byte. The short-list branch fires with
    `len = 0`, so `takeBytes rest 0 = some ([], rest)` and the recursive
    `decodeItems nDepth []` returns `some ([], [])` which has empty
    leftover.
@isnad1 id=eq.0h2v.s5.28c6b2e28486 from=translated src=- shape=e530f958 vocab=c3f30349
-/
theorem decodeAux_empty_list (nDepth : Nat) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0xC0 : Byte) :: rest) = some (.list [], rest) := by
  simp [decodeAux, takeBytes, decodeItems]

/-- Two-byte short string (prefix `0x82`): `decodeAux` returns
    `(.bytes [b1, b2], rest)` consuming three bytes (prefix + 2 payload).
    The two-byte payload is multi-byte, so the canonical-form check
    (which only fires for single-byte strings) is bypassed.
@isnad1 id=eq.0h4v.s6.fa69a5e59509 from=translated src=- shape=896ddfce vocab=e260c232
-/
theorem decodeAux_two_byte_string (nDepth : Nat) (b1 b2 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0x82 : Byte) :: b1 :: b2 :: rest) =
      some (.bytes [b1, b2], rest) := by
  simp [decodeAux, takeBytes]

/-- Three-byte short string (prefix `0x83`): `decodeAux` returns
    `(.bytes [b1, b2, b3], rest)` consuming four bytes (prefix + 3
    payload). Multi-byte payload bypasses the canonical-form check.
@isnad1 id=eq.0h5v.s6.640c8126ed21 from=translated src=- shape=30a22b72 vocab=e260c232
-/
theorem decodeAux_three_byte_string
    (nDepth : Nat) (b1 b2 b3 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0x83 : Byte) :: b1 :: b2 :: b3 :: rest) =
      some (.bytes [b1, b2, b3], rest) := by
  simp [decodeAux, takeBytes]

/-- Four-byte short string (prefix `0x84`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h6v.s6.2d58867158da from=translated src=- shape=a412f781 vocab=e260c232
-/
theorem decodeAux_four_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0x84 : Byte) :: b1 :: b2 :: b3 :: b4 :: rest) =
      some (.bytes [b1, b2, b3, b4], rest) := by
  simp [decodeAux, takeBytes]

/-- Five-byte short string (prefix `0x85`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h7v.s6.8eac739574b8 from=translated src=- shape=1d46f049 vocab=e260c232
-/
theorem decodeAux_five_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1) ((0x85 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5], rest) := by
  simp [decodeAux, takeBytes]

/-- Six-byte short string (prefix `0x86`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h8v.s6.800577eab4cf from=translated src=- shape=5c971bbf vocab=e260c232
-/
theorem decodeAux_six_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x86 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6], rest) := by
  simp [decodeAux, takeBytes]

/-- Seven-byte short string (prefix `0x87`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h9v.s6.0d0733edec6a from=translated src=- shape=35b70ec3 vocab=e260c232
-/
theorem decodeAux_seven_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x87 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7], rest) := by
  simp [decodeAux, takeBytes]

/-- Eight-byte short string (prefix `0x88`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h10v.s6.40cb4a5ff783 from=translated src=- shape=ec0bbb0e vocab=e260c232
-/
theorem decodeAux_eight_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x88 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8], rest) := by
  simp [decodeAux, takeBytes]

/-- Nine-byte short string (prefix `0x89`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h11v.s6.7f31bc9ead76 from=translated src=- shape=44259d97 vocab=e260c232
-/
theorem decodeAux_nine_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x89 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9], rest) := by
  simp [decodeAux, takeBytes]

/-- Ten-byte short string (prefix `0x8A`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h12v.s7.19805b3be95f from=translated src=- shape=2c9af806 vocab=e260c232
-/
theorem decodeAux_ten_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10], rest) := by
  simp [decodeAux, takeBytes]

/-- Eleven-byte short string (prefix `0x8B`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h13v.s7.7c2357a1ab02 from=translated src=- shape=100e56a0 vocab=e260c232
-/
theorem decodeAux_eleven_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Byte) (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11], rest) := by
  simp [decodeAux, takeBytes]

/-- Twelve-byte short string (prefix `0x8C`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h14v.s7.ae000b6323b9 from=translated src=- shape=8ac4f211 vocab=e260c232
-/
theorem decodeAux_twelve_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], rest) := by
  simp [decodeAux, takeBytes]

/-- Thirteen-byte short string (prefix `0x8D`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h15v.s7.6da6cfa75821 from=translated src=- shape=0b096ebe vocab=e260c232
-/
theorem decodeAux_thirteen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13], rest) := by
  simp [decodeAux, takeBytes]

/-- Fourteen-byte short string (prefix `0x8E`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h16v.s7.d3f31c1399f8 from=translated src=- shape=a2ee78c8 vocab=e260c232
-/
theorem decodeAux_fourteen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifteen-byte short string (prefix `0x8F`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h17v.s7.77f43825daca from=translated src=- shape=939005c5 vocab=e260c232
-/
theorem decodeAux_fifteen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x8F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Sixteen-byte short string (prefix `0x90`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h18v.s7.61243f88870c from=translated src=- shape=e3d27fb5 vocab=e260c232
-/
theorem decodeAux_sixteen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x90 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Seventeen-byte short string (prefix `0x91`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h19v.s7.ec929a033bba from=translated src=- shape=b8b469a1 vocab=e260c232
-/
theorem decodeAux_seventeen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x91 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Eighteen-byte short string (prefix `0x92`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h20v.s7.aca6b8d0c50e from=translated src=- shape=d342a3ec vocab=e260c232
-/
theorem decodeAux_eighteen_byte_string
    (nDepth : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x92 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Nineteen-byte short string (prefix `0x93`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h21v.s7.046817217757 from=translated src=- shape=e3b0c955 vocab=e260c232
-/
theorem decodeAux_nineteen_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x93 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-byte short string (prefix `0x94`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h22v.s7.3d3222b85e92 from=translated src=- shape=a060a759 vocab=e260c232
-/
theorem decodeAux_twenty_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x94 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-one-byte short string (prefix `0x95`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h23v.s7.a5ecbb829007 from=translated src=- shape=bdc774d4 vocab=e260c232
-/
theorem decodeAux_twenty_one_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x95 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-two-byte short string (prefix `0x96`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h24v.s7.516ff616f031 from=translated src=- shape=6adb7d30 vocab=e260c232
-/
theorem decodeAux_twenty_two_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x96 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-three-byte short string (prefix `0x97`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h25v.s7.ebc103cc7c92 from=translated src=- shape=fe4ec3d0 vocab=e260c232
-/
theorem decodeAux_twenty_three_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x97 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-four-byte short string (prefix `0x98`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h26v.s7.34e200d4b0aa from=translated src=- shape=fb4bad48 vocab=e260c232
-/
theorem decodeAux_twenty_four_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x98 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-five-byte short string (prefix `0x99`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h27v.s7.e26fcac5a8f7 from=translated src=- shape=30b47bb5 vocab=e260c232
-/
theorem decodeAux_twenty_five_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x99 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-six-byte short string (prefix `0x9A`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h28v.s8.4406442cdbb2 from=translated src=- shape=171eab40 vocab=e260c232
-/
theorem decodeAux_twenty_six_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-seven-byte short string (prefix `0x9B`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h29v.s8.4cd255c11cbd from=translated src=- shape=3593e66b vocab=e260c232
-/
theorem decodeAux_twenty_seven_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-eight-byte short string (prefix `0x9C`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h30v.s8.29628900f729 from=translated src=- shape=61f28420 vocab=e260c232
-/
theorem decodeAux_twenty_eight_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-nine-byte short string (prefix `0x9D`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h31v.s8.80f5dbc45cc5 from=translated src=- shape=0a000fb1 vocab=e260c232
-/
theorem decodeAux_twenty_nine_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-byte short string (prefix `0x9E`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h32v.s8.fff90f4cc1d9 from=translated src=- shape=57d6538f vocab=e260c232
-/
theorem decodeAux_thirty_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-one-byte short string (prefix `0x9F`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h33v.s8.73f64915b33c from=translated src=- shape=5cb27254 vocab=e260c232
-/
theorem decodeAux_thirty_one_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0x9F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-two-byte short string (prefix `0xA0`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h34v.s8.a1f966f546c4 from=translated src=- shape=339c5f8e vocab=e260c232
-/
theorem decodeAux_thirty_two_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA0 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-three-byte short string (prefix `0xA1`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h35v.s8.e5728eb3a44e from=translated src=- shape=04d0e81f vocab=e260c232
-/
theorem decodeAux_thirty_three_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA1 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-four-byte short string (prefix `0xA2`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h36v.s8.f593971ae17c from=translated src=- shape=584fb841 vocab=e260c232
-/
theorem decodeAux_thirty_four_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA2 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-five-byte short string (prefix `0xA3`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h37v.s8.6772b66713e8 from=translated src=- shape=3988781b vocab=e260c232
-/
theorem decodeAux_thirty_five_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA3 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-six-byte short string (prefix `0xA4`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h38v.s8.e8a07ea91862 from=translated src=- shape=82c59169 vocab=e260c232
-/
theorem decodeAux_thirty_six_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA4 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-seven-byte short string (prefix `0xA5`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h39v.s8.cae7b27b5804 from=translated src=- shape=ad240d26 vocab=e260c232
-/
theorem decodeAux_thirty_seven_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA5 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-eight-byte short string (prefix `0xA6`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h40v.s8.7816098c5a02 from=translated src=- shape=4a252a0f vocab=e260c232
-/
theorem decodeAux_thirty_eight_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA6 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-nine-byte short string (prefix `0xA7`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h41v.s8.306e9c7b9245 from=translated src=- shape=5499167b vocab=e260c232
-/
theorem decodeAux_thirty_nine_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA7 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-byte short string (prefix `0xA8`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h42v.s8.d36b9d80b0c6 from=translated src=- shape=295eff47 vocab=e260c232
-/
theorem decodeAux_forty_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 :
      Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA8 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-one-byte short string (prefix `0xA9`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h43v.s8.c5bd3c1d1545 from=translated src=- shape=818b0f1a vocab=e260c232
-/
theorem decodeAux_forty_one_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 :
      Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xA9 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-two-byte short string (prefix `0xAA`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h44v.s8.24ab3722c867 from=translated src=- shape=061b8877 vocab=e260c232
-/
theorem decodeAux_forty_two_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 :
      Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xAA : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-three-byte short string (prefix `0xAB`). Multi-byte payload
    bypasses the canonical-form check.
@isnad1 id=eq.0h45v.s8.08628c32dbaa from=translated src=- shape=68a38e92 vocab=e260c232
-/
theorem decodeAux_forty_three_byte_string
    (nDepth : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 : Byte)
    (rest : List Byte) :
    decodeAux (nDepth + 1)
        ((0xAB : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Canonical-form rejection: prefix `0x81` followed by a byte `b`
    with `b.toNat < 0x80` is non-canonical (the byte should have
    been encoded as itself, not under prefix `0x81`), so `decodeAux`
    returns `none`.
@isnad1 id=eq.1h3v.s6.0d33e09c4453 from=translated src=- shape=2012e092 vocab=b3f234a2
-/
theorem decodeAux_canonical_rejection_single
    (nDepth : Nat) (b : Byte) (rest : List Byte) (h : b.toNat < 0x80) :
    decodeAux (nDepth + 1) ((0x81 : Byte) :: b :: rest) = none := by
  simp [decodeAux, takeBytes, h]

/-- Singleton list containing one small byte: top-level `decode` of
    `[0xC1, b]` with `b < 0x80` returns `.list [.bytes [b]]`. The
    short-list branch fires with payload length 1, the inner byte is
    recognized as a single-byte item, and the list closes cleanly.
@isnad1 id=eq.1h1v.s6.b06614a21f22 from=translated src=- shape=6028ec88 vocab=8feed756
-/
theorem decode_singleton_list_small_byte (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC1 : Byte), b] = some (.list [.bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Singleton list containing the empty byte string:
    `decode [0xC1, 0x80] = some (.list [.bytes []], [])`. The
    short-list branch fires with payload length 1, the inner `0x80`
    is recognized as the empty short-string, and the list closes
    cleanly.
@isnad1 id=eq.0h0v.s5.d0a5ba146d9b from=translated src=- shape=11ba7337 vocab=f87fcdca
-/
theorem decode_singleton_list_empty_string :
    decode [(0xC1 : Byte), (0x80 : Byte)] = some (.list [.bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing the empty list:
    `decode [0xC1, 0xC0] = some (.list [.list []], [])`. The
    short-list branch fires with payload length 1, the inner `0xC0`
    is recognized as the empty list, and the outer list closes.
@isnad1 id=eq.0h0v.s5.c08ac773b671 from=translated src=- shape=dfbdd538 vocab=c3e3d526
-/
theorem decode_singleton_list_empty_list :
    decode [(0xC1 : Byte), (0xC0 : Byte)] = some (.list [.list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing a single large byte: `decode [0xC2, 0x81, b]`
    with `b ≥ 0x80` returns `.list [.bytes [b]]`. The outer short-list
    branch fires with payload length 2, the inner `[0x81, b]` decodes
    as a single-byte short string (canonical form, since `b ≥ 0x80`),
    and the outer list closes.
@isnad1 id=eq.1h1v.s6.954a3a05bf2c from=translated src=- shape=283bea61 vocab=8feed756
-/
theorem decode_singleton_list_large_byte (b : Byte) (h : ¬ b.toNat < 0x80) :
    decode [(0xC2 : Byte), (0x81 : Byte), b] =
      some (.list [.bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Two-element list of small bytes:
    `decode [0xC2, b1, b2] = some (.list [.bytes [b1], .bytes [b2]], [])`
    when both `b1, b2 < 0x80`. Short-list branch fires with payload
    length 2, two single-byte items decoded in sequence, then closes.
@isnad1 id=eq.2h2v.s6.ad5909fccfea from=translated src=- shape=05876240 vocab=8feed756
-/
theorem decode_pair_list_small_bytes
    (b1 b2 : Byte) (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80) :
    decode [(0xC2 : Byte), b1, b2] =
      some (.list [.bytes [b1], .bytes [b2]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2]

/-- Three-element list of small bytes:
    `decode [0xC3, b1, b2, b3] = some (.list [.bytes [b1], .bytes [b2], .bytes [b3]], [])`
    when all `b1, b2, b3 < 0x80`. Short-list branch fires with payload
    length 3, three single-byte items decoded in sequence, then closes.
@isnad1 id=eq.3h3v.s6.739ef38e758f from=translated src=- shape=94120c0a vocab=8feed756
-/
theorem decode_triple_list_small_bytes
    (b1 b2 b3 : Byte)
    (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80) (h3 : b3.toNat < 0x80) :
    decode [(0xC3 : Byte), b1, b2, b3] =
      some (.list [.bytes [b1], .bytes [b2], .bytes [b3]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2, h3]

/-- Four-element list of small bytes:
    `decode [0xC4, b1, b2, b3, b4] = some (.list [.bytes [b1], .bytes [b2], .bytes [b3], .bytes [b4]], [])`
    when all `b1, b2, b3, b4 < 0x80`. Short-list branch fires with
    payload length 4, four single-byte items decoded in sequence, then
    closes.
@isnad1 id=eq.4h4v.s7.368f8299eb28 from=translated src=- shape=d030d60a vocab=8feed756
-/
theorem decode_quad_list_small_bytes
    (b1 b2 b3 b4 : Byte)
    (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80)
    (h3 : b3.toNat < 0x80) (h4 : b4.toNat < 0x80) :
    decode [(0xC4 : Byte), b1, b2, b3, b4] =
      some (.list [.bytes [b1], .bytes [b2], .bytes [b3], .bytes [b4]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2, h3, h4]

/-- Two-element list of empty lists:
    `decode [0xC2, 0xC0, 0xC0] = some (.list [.list [], .list []], [])`.
    The outer short-list branch fires with payload length 2, two empty
    inner lists are decoded in sequence, then the outer closes.
@isnad1 id=eq.0h0v.s6.cc7b93eeb442 from=translated src=- shape=14b2d9c0 vocab=c3e3d526
-/
theorem decode_pair_list_empty_lists :
    decode [(0xC2 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Two-element list of empty byte strings:
    `decode [0xC2, 0x80, 0x80] = some (.list [.bytes [], .bytes []], [])`.
    The outer short-list branch fires with payload length 2, two empty
    inner byte strings are decoded in sequence, then the outer closes.
@isnad1 id=eq.0h0v.s6.d86615611a95 from=translated src=- shape=cdfdad71 vocab=f87fcdca
-/
theorem decode_pair_list_empty_strings :
    decode [(0xC2 : Byte), (0x80 : Byte), (0x80 : Byte)] =
      some (.list [.bytes [], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Three-element list of empty lists:
    `decode [0xC3, 0xC0, 0xC0, 0xC0] = some (.list [.list [], .list [], .list []], [])`.
    The outer short-list branch fires with payload length 3, three empty
    inner lists are decoded in sequence, then the outer closes.
@isnad1 id=eq.0h0v.s6.0d593588156b from=translated src=- shape=55f5e4a5 vocab=c3e3d526
-/
theorem decode_triple_list_empty_lists :
    decode [(0xC3 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Three-element list of empty byte strings:
    `decode [0xC3, 0x80, 0x80, 0x80] = some (.list [.bytes [], .bytes [], .bytes []], [])`.
    The outer short-list branch fires with payload length 3, three empty
    inner byte strings are decoded in sequence, then the outer closes.
@isnad1 id=eq.0h0v.s6.c5bdfc910e10 from=translated src=- shape=53dc5253 vocab=f87fcdca
-/
theorem decode_triple_list_empty_strings :
    decode [(0xC3 : Byte), (0x80 : Byte), (0x80 : Byte), (0x80 : Byte)] =
      some (.list [.bytes [], .bytes [], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Four-element list of empty lists:
    `decode [0xC4, 0xC0, 0xC0, 0xC0, 0xC0] = some (.list [.list [], .list [], .list [], .list []], [])`.
    The outer short-list branch fires with payload length 4, four empty
    inner lists are decoded in sequence, then the outer closes.
@isnad1 id=eq.0h0v.s6.b317bcae3189 from=translated src=- shape=b09a617c vocab=c3e3d526
-/
theorem decode_quad_list_empty_lists :
    decode [(0xC4 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list [], .list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Mixed-content two-element list: a small byte followed by an empty
    string. `decode [0xC2, b, 0x80] = some (.list [.bytes [b], .bytes []], [])`
    when `b < 0x80`.
@isnad1 id=eq.1h1v.s6.af8e249f40ed from=translated src=- shape=e07176a9 vocab=8feed756
-/
theorem decode_pair_list_byte_then_empty_string
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), b, (0x80 : Byte)] =
      some (.list [.bytes [b], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Mixed-content two-element list: an empty list followed by a small
    byte. `decode [0xC2, 0xC0, b] = some (.list [.list [], .bytes [b]], [])`
    when `b < 0x80`.
@isnad1 id=eq.1h1v.s6.40be951e0284 from=translated src=- shape=33627cd9 vocab=8feed756
-/
theorem decode_pair_list_empty_list_then_byte
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), (0xC0 : Byte), b] =
      some (.list [.list [], .bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Mixed-content two-element list: a small byte followed by an empty
    list. `decode [0xC2, b, 0xC0] = some (.list [.bytes [b], .list []], [])`
    when `b < 0x80`. Companion to `decode_pair_list_empty_list_then_byte`
    in the reverse order.
@isnad1 id=eq.1h1v.s6.523cff66c415 from=translated src=- shape=2c3f2d75 vocab=8feed756
-/
theorem decode_pair_list_byte_then_empty_list
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), b, (0xC0 : Byte)] =
      some (.list [.bytes [b], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Two-element list with one large byte and one small byte:
    `decode [0xC3, 0x81, b_large, b_small] = some (.list [.bytes [b_large], .bytes [b_small]], [])`
    when `b_large ≥ 0x80` and `b_small < 0x80`. The outer short-list
    branch fires with payload length 3, the inner large-byte string is
    decoded under canonical form (0x81 prefix), then the small-byte
    item, then the outer closes.
@isnad1 id=eq.2h2v.s6.4cc1aa9d7b05 from=translated src=- shape=d44ecdc4 vocab=8feed756
-/
theorem decode_pair_list_large_then_small_byte
    (b_large b_small : Byte)
    (h_l : ¬ b_large.toNat < 0x80) (h_s : b_small.toNat < 0x80) :
    decode [(0xC3 : Byte), (0x81 : Byte), b_large, b_small] =
      some (.list [.bytes [b_large], .bytes [b_small]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h_l, h_s]

/-- Two-element list with one small byte and one large byte
    (the mirror of `decode_pair_list_large_then_small_byte`):
    `decode [0xC3, b_small, 0x81, b_large] = some (.list [.bytes [b_small], .bytes [b_large]], [])`
    when `b_small < 0x80` and `b_large ≥ 0x80`. The outer short-list
    branch fires with payload length 3, the small-byte item is decoded
    first as a single-byte string, then the inner `[0x81, b_large]` is
    decoded as a one-byte short string under canonical form.
@isnad1 id=eq.2h2v.s6.663444361a0c from=translated src=- shape=b8d454d7 vocab=8feed756
-/
theorem decode_pair_list_small_then_large_byte
    (b_small b_large : Byte)
    (h_s : b_small.toNat < 0x80) (h_l : ¬ b_large.toNat < 0x80) :
    decode [(0xC3 : Byte), b_small, (0x81 : Byte), b_large] =
      some (.list [.bytes [b_small], .bytes [b_large]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h_s, h_l]

/-- Singleton list containing a two-byte short string:
    `decode [0xC3, 0x82, b1, b2] = some (.list [.bytes [b1, b2]], [])`.
    The outer short-list branch fires with payload length 3, the inner
    `[0x82, b1, b2]` decodes as a two-byte short string, and the outer
    list closes.
@isnad1 id=eq.0h2v.s6.f71ba7019f12 from=translated src=- shape=26f57de5 vocab=f87fcdca
-/
theorem decode_singleton_list_two_byte_string (b1 b2 : Byte) :
    decode [(0xC3 : Byte), (0x82 : Byte), b1, b2] =
      some (.list [.bytes [b1, b2]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing a three-byte short string:
    `decode [0xC4, 0x83, b1, b2, b3] = some (.list [.bytes [b1, b2, b3]], [])`.
    The outer short-list branch fires with payload length 4, the inner
    `[0x83, b1, b2, b3]` decodes as a three-byte short string.
@isnad1 id=eq.0h3v.s6.dbdf09feb9cf from=translated src=- shape=4b95d636 vocab=f87fcdca
-/
theorem decode_singleton_list_three_byte_string (b1 b2 b3 : Byte) :
    decode [(0xC4 : Byte), (0x83 : Byte), b1, b2, b3] =
      some (.list [.bytes [b1, b2, b3]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-! ## decode (top-level wrapper) trivial cases -/

/-- `decode []` returns `none` because `decodeAux 0 []` returns `none`.
@isnad1 id=eq.0h0v.s3.ee3ccf39dfff from=translated src=- shape=0a38a3c6 vocab=147c46b4
-/
theorem decode_nil : decode ([] : List Byte) = none := by
  simp [decode, decodeAux]

/-- `decode [pfx]` returns `(.bytes [pfx], [])` whenever `pfx < 0x80`.
    Specializes `decodeAux_single_byte` at the top-level nDepth.
@isnad1 id=eq.1h1v.s5.de927046b48e from=translated src=- shape=1b3c8e04 vocab=e9c26ddc
-/
theorem decode_single_byte (pfx : Byte) (h : pfx.toNat < 0x80) :
    decode [pfx] = some (.bytes [pfx], []) := by
  simp [decode, decodeAux, h]

/-- `decode [0x80] = some (.bytes [], [])` — the canonical empty-string
    encoding. Specializes `decodeAux_empty_string` at the top-level nDepth.
@isnad1 id=eq.0h0v.s5.7dc65daa0376 from=translated src=- shape=28566def vocab=75d59e58
-/
theorem decode_empty_string : decode [(0x80 : Byte)] = some (.bytes [], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xC0] = some (.list [], [])` — the canonical empty-list
    encoding. Specializes `decodeAux_empty_list` at the top-level nDepth.
@isnad1 id=eq.0h0v.s5.25937ead78b3 from=translated src=- shape=c3889a71 vocab=c3e3d526
-/
theorem decode_empty_list : decode [(0xC0 : Byte)] = some (.list [], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Canonical-form rejection at the top level: `decode [0x81, b]`
    returns `none` whenever `b.toNat < 0x80`. Specializes
    `decodeAux_canonical_rejection_single`.
@isnad1 id=eq.1h1v.s5.62f96b4b3a1f from=translated src=- shape=db2d1e2a vocab=4d695cce
-/
theorem decode_canonical_rejection_single (b : Byte) (h : b.toNat < 0x80) :
    decode [(0x81 : Byte), b] = none := by
  simp [decode, decodeAux, takeBytes, h]

/-- `decode [0x82, b1, b2] = some (.bytes [b1, b2], [])` — the canonical
    two-byte short-string encoding.
@isnad1 id=eq.0h2v.s5.545983a69a11 from=translated src=- shape=b6c33354 vocab=75d59e58
-/
theorem decode_two_byte_string (b1 b2 : Byte) :
    decode [(0x82 : Byte), b1, b2] = some (.bytes [b1, b2], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x83, b1, b2, b3] = some (.bytes [b1, b2, b3], [])` — the
    canonical three-byte short-string encoding.
@isnad1 id=eq.0h3v.s5.9e96fd60440d from=translated src=- shape=50e4714a vocab=75d59e58
-/
theorem decode_three_byte_string (b1 b2 b3 : Byte) :
    decode [(0x83 : Byte), b1, b2, b3] = some (.bytes [b1, b2, b3], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x84, b1, b2, b3, b4] = some (.bytes [b1, b2, b3, b4], [])`
    — the canonical four-byte short-string encoding.
@isnad1 id=eq.0h4v.s6.86338e72163e from=translated src=- shape=0c010458 vocab=75d59e58
-/
theorem decode_four_byte_string (b1 b2 b3 b4 : Byte) :
    decode [(0x84 : Byte), b1, b2, b3, b4] =
      some (.bytes [b1, b2, b3, b4], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x85, b1, b2, b3, b4, b5] = some (.bytes [b1..b5], [])`
    — the canonical five-byte short-string encoding.
@isnad1 id=eq.0h5v.s6.fc1370492994 from=translated src=- shape=40329737 vocab=75d59e58
-/
theorem decode_five_byte_string (b1 b2 b3 b4 b5 : Byte) :
    decode [(0x85 : Byte), b1, b2, b3, b4, b5] =
      some (.bytes [b1, b2, b3, b4, b5], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x86, b1..b6] = some (.bytes [b1..b6], [])` — the
    canonical six-byte short-string encoding.
@isnad1 id=eq.0h6v.s6.2fcde18db65f from=translated src=- shape=65e4e3b6 vocab=75d59e58
-/
theorem decode_six_byte_string (b1 b2 b3 b4 b5 b6 : Byte) :
    decode [(0x86 : Byte), b1, b2, b3, b4, b5, b6] =
      some (.bytes [b1, b2, b3, b4, b5, b6], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x87, b1..b7] = some (.bytes [b1..b7], [])` — the
    canonical seven-byte short-string encoding.
@isnad1 id=eq.0h7v.s6.0157f48f288f from=translated src=- shape=ffe4f083 vocab=75d59e58
-/
theorem decode_seven_byte_string (b1 b2 b3 b4 b5 b6 b7 : Byte) :
    decode [(0x87 : Byte), b1, b2, b3, b4, b5, b6, b7] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x88, b1..b8] = some (.bytes [b1..b8], [])` — the
    canonical eight-byte short-string encoding.
@isnad1 id=eq.0h8v.s6.7f3a591ca481 from=translated src=- shape=9117f4da vocab=75d59e58
-/
theorem decode_eight_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 : Byte) :
    decode [(0x88 : Byte), b1, b2, b3, b4, b5, b6, b7, b8] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x89, b1..b9] = some (.bytes [b1..b9], [])` — the
    canonical nine-byte short-string encoding.
@isnad1 id=eq.0h9v.s6.8fccb6d3308b from=translated src=- shape=91be7a27 vocab=75d59e58
-/
theorem decode_nine_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Byte) :
    decode [(0x89 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8A, b1..b10] = some (.bytes [b1..b10], [])` — the
    canonical ten-byte short-string encoding.
@isnad1 id=eq.0h10v.s6.57322086d4ae from=translated src=- shape=bbbdf3b2 vocab=75d59e58
-/
theorem decode_ten_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Byte) :
    decode [(0x8A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8B, b1..b11] = some (.bytes [b1..b11], [])` — the
    canonical eleven-byte short-string encoding.
@isnad1 id=eq.0h11v.s6.4a5b1ba2ac65 from=translated src=- shape=1f7f6466 vocab=75d59e58
-/
theorem decode_eleven_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Byte) :
    decode [(0x8B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8C, b1..b12] = some (.bytes [b1..b12], [])` — the
    canonical twelve-byte short-string encoding.
@isnad1 id=eq.0h12v.s7.7db3b5ae84e7 from=translated src=- shape=0bba8b66 vocab=75d59e58
-/
theorem decode_twelve_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Byte) :
    decode [(0x8C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8D, b1..b13] = some (.bytes [b1..b13], [])` — the
    canonical thirteen-byte short-string encoding.
@isnad1 id=eq.0h13v.s7.de3aeb730a28 from=translated src=- shape=52425615 vocab=75d59e58
-/
theorem decode_thirteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Byte) :
    decode [(0x8D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8E, b1..b14] = some (.bytes [b1..b14], [])` — the
    canonical fourteen-byte short-string encoding.
@isnad1 id=eq.0h14v.s7.d0f155f1c552 from=translated src=- shape=a36cb582 vocab=75d59e58
-/
theorem decode_fourteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Byte) :
    decode [(0x8E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8F, b1..b15] = some (.bytes [b1..b15], [])` — the
    canonical fifteen-byte short-string encoding.
@isnad1 id=eq.0h15v.s7.8e3506d32458 from=translated src=- shape=6fb49996 vocab=75d59e58
-/
theorem decode_fifteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte) :
    decode [(0x8F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x90, b1..b16] = some (.bytes [b1..b16], [])` — the
    canonical sixteen-byte short-string encoding.
@isnad1 id=eq.0h16v.s7.e56556766473 from=translated src=- shape=6023adeb vocab=75d59e58
-/
theorem decode_sixteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Byte) :
    decode [(0x90 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x91, b1..b17] = some (.bytes [b1..b17], [])` — the
    canonical seventeen-byte short-string encoding.
@isnad1 id=eq.0h17v.s7.35469fc5c16d from=translated src=- shape=7a3a8c59 vocab=75d59e58
-/
theorem decode_seventeen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 : Byte) :
    decode [(0x91 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x92, b1..b18] = some (.bytes [b1..b18], [])` — the
    canonical eighteen-byte short-string encoding.
@isnad1 id=eq.0h18v.s7.80b124ebf749 from=translated src=- shape=829faaad vocab=75d59e58
-/
theorem decode_eighteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Byte) :
    decode [(0x92 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x93, b1..b19] = some (.bytes [b1..b19], [])` — the
    canonical nineteen-byte short-string encoding.
@isnad1 id=eq.0h19v.s7.1553b5991a03 from=translated src=- shape=b77c97af vocab=75d59e58
-/
theorem decode_nineteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Byte) :
    decode [(0x93 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x94, b1..b20] = some (.bytes [b1..b20], [])` — the
    canonical twenty-byte short-string encoding.
@isnad1 id=eq.0h20v.s7.deb0463c1b84 from=translated src=- shape=7fe3d56d vocab=75d59e58
-/
theorem decode_twenty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : Byte) :
    decode [(0x94 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x95, b1..b21] = some (.bytes [b1..b21], [])` — the
    canonical twenty-one-byte short-string encoding.
@isnad1 id=eq.0h21v.s7.1a6e31e0919f from=translated src=- shape=cb56b8c5 vocab=75d59e58
-/
theorem decode_twenty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 : Byte) :
    decode [(0x95 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x96, b1..b22] = some (.bytes [b1..b22], [])` — the
    canonical twenty-two-byte short-string encoding.
@isnad1 id=eq.0h22v.s7.8b117b5a3b9c from=translated src=- shape=faf61649 vocab=75d59e58
-/
theorem decode_twenty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      Byte) :
    decode [(0x96 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x97, b1..b23] = some (.bytes [b1..b23], [])` — the
    canonical twenty-three-byte short-string encoding.
@isnad1 id=eq.0h23v.s7.68ecc5baa1e5 from=translated src=- shape=ab670c2c vocab=75d59e58
-/
theorem decode_twenty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 : Byte) :
    decode [(0x97 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x98, b1..b24] = some (.bytes [b1..b24], [])` — the
    canonical twenty-four-byte short-string encoding.
@isnad1 id=eq.0h24v.s7.fd1d8f5f22a9 from=translated src=- shape=d3afc014 vocab=75d59e58
-/
theorem decode_twenty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 : Byte) :
    decode [(0x98 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x99, b1..b25] = some (.bytes [b1..b25], [])` — the
    canonical twenty-five-byte short-string encoding.
@isnad1 id=eq.0h25v.s7.e6ba090e6670 from=translated src=- shape=fca8c8ea vocab=75d59e58
-/
theorem decode_twenty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 : Byte) :
    decode [(0x99 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9A, b1..b26] = some (.bytes [b1..b26], [])` — the
    canonical twenty-six-byte short-string encoding.
@isnad1 id=eq.0h26v.s7.5ea7637de100 from=translated src=- shape=0af0e4b1 vocab=75d59e58
-/
theorem decode_twenty_six_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 : Byte) :
    decode [(0x9A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9B, b1..b27] = some (.bytes [b1..b27], [])` — the
    canonical twenty-seven-byte short-string encoding.
@isnad1 id=eq.0h27v.s7.885f25228ea6 from=translated src=- shape=fdcbcbfe vocab=75d59e58
-/
theorem decode_twenty_seven_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 : Byte) :
    decode [(0x9B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9C, b1..b28] = some (.bytes [b1..b28], [])` — the
    canonical twenty-eight-byte short-string encoding.
@isnad1 id=eq.0h28v.s8.e22dd2c6ed2b from=translated src=- shape=8a782a94 vocab=75d59e58
-/
theorem decode_twenty_eight_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 : Byte) :
    decode [(0x9C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9D, b1..b29] = some (.bytes [b1..b29], [])` — the
    canonical twenty-nine-byte short-string encoding.
@isnad1 id=eq.0h29v.s8.31597355ff84 from=translated src=- shape=773c20c2 vocab=75d59e58
-/
theorem decode_twenty_nine_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 : Byte) :
    decode [(0x9D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9E, b1..b30] = some (.bytes [b1..b30], [])` — the
    canonical thirty-byte short-string encoding.
@isnad1 id=eq.0h30v.s8.ffa0dc954b5c from=translated src=- shape=29f273b6 vocab=75d59e58
-/
theorem decode_thirty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 : Byte) :
    decode [(0x9E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9F, b1..b31] = some (.bytes [b1..b31], [])` — the
    canonical thirty-one-byte short-string encoding.
@isnad1 id=eq.0h31v.s8.21d5b6f5bcd0 from=translated src=- shape=d48c8b74 vocab=75d59e58
-/
theorem decode_thirty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 : Byte) :
    decode [(0x9F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA0, b1..b32] = some (.bytes [b1..b32], [])` — the
    canonical thirty-two-byte short-string encoding.
@isnad1 id=eq.0h32v.s8.e93daad8e216 from=translated src=- shape=b7830334 vocab=75d59e58
-/
theorem decode_thirty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 : Byte) :
    decode [(0xA0 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA1, b1..b33] = some (.bytes [b1..b33], [])` — the
    canonical thirty-three-byte short-string encoding.
@isnad1 id=eq.0h33v.s8.58cb0f67b18d from=translated src=- shape=9619ff54 vocab=75d59e58
-/
theorem decode_thirty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 : Byte) :
    decode [(0xA1 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA2, b1..b34] = some (.bytes [b1..b34], [])` — the
    canonical thirty-four-byte short-string encoding.
@isnad1 id=eq.0h34v.s8.cd138257e21a from=translated src=- shape=f9cc206f vocab=75d59e58
-/
theorem decode_thirty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 : Byte) :
    decode [(0xA2 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA3, b1..b35] = some (.bytes [b1..b35], [])` — the
    canonical thirty-five-byte short-string encoding.
@isnad1 id=eq.0h35v.s8.478dc43ba804 from=translated src=- shape=6e0c9965 vocab=75d59e58
-/
theorem decode_thirty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 : Byte) :
    decode [(0xA3 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA4, b1..b36] = some (.bytes [b1..b36], [])` — the
    canonical thirty-six-byte short-string encoding.
@isnad1 id=eq.0h36v.s8.7b257bec4a5d from=translated src=- shape=6aad0a84 vocab=75d59e58
-/
theorem decode_thirty_six_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 : Byte) :
    decode [(0xA4 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA5, b1..b37] = some (.bytes [b1..b37], [])` — the
    canonical thirty-seven-byte short-string encoding.
@isnad1 id=eq.0h37v.s8.91414512339f from=translated src=- shape=9d83c1d3 vocab=75d59e58
-/
theorem decode_thirty_seven_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 : Byte) :
    decode [(0xA5 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA6, b1..b38] = some (.bytes [b1..b38], [])` — the
    canonical thirty-eight-byte short-string encoding.
@isnad1 id=eq.0h38v.s8.85f8ed1466eb from=translated src=- shape=44f945a5 vocab=75d59e58
-/
theorem decode_thirty_eight_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 : Byte) :
    decode [(0xA6 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA7, b1..b39] = some (.bytes [b1..b39], [])` — the
    canonical thirty-nine-byte short-string encoding.
@isnad1 id=eq.0h39v.s8.6dc4e906307b from=translated src=- shape=45dd253f vocab=75d59e58
-/
theorem decode_thirty_nine_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 : Byte) :
    decode [(0xA7 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA8, b1..b40] = some (.bytes [b1..b40], [])` — the
    canonical forty-byte short-string encoding.
@isnad1 id=eq.0h40v.s8.e2e220966783 from=translated src=- shape=6a0e30da vocab=75d59e58
-/
theorem decode_forty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 :
      Byte) :
    decode [(0xA8 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA9, b1..b41] = some (.bytes [b1..b41], [])` — the
    canonical forty-one-byte short-string encoding.
@isnad1 id=eq.0h41v.s8.728558658916 from=translated src=- shape=4b27e0db vocab=75d59e58
-/
theorem decode_forty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 :
      Byte) :
    decode [(0xA9 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAA, b1..b42] = some (.bytes [b1..b42], [])` — the
    canonical forty-two-byte short-string encoding.
@isnad1 id=eq.0h42v.s8.2622b1aa0a7c from=translated src=- shape=032c0054 vocab=75d59e58
-/
theorem decode_forty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 :
      Byte) :
    decode [(0xAA : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAB, b1..b43] = some (.bytes [b1..b43], [])` — the
    canonical forty-three-byte short-string encoding.
@isnad1 id=eq.0h43v.s8.b6d54130cced from=translated src=- shape=48e9de96 vocab=75d59e58
-/
theorem decode_forty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 : Byte) :
    decode [(0xAB : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-! ## encodeBytes characterizations -/

/-- Empty byte string encodes to the single prefix `[0x80]`.
@isnad1 id=eq.0h0v.s4.e74b40b20287 from=translated src=- shape=0f8b4316 vocab=0ec3488c
-/
theorem encodeBytes_nil : encodeBytes [] = [BitVec.ofNat 8 0x80] := by
  simp [encodeBytes]

/-- Single small byte (`b < 0x80`): the byte is its own encoding.
@isnad1 id=eq.1h1v.s5.e51c6d8514bc from=translated src=- shape=b5465817 vocab=2179be26
-/
theorem encodeBytes_single_small (b : Byte) (h : b.toNat < 0x80) :
    encodeBytes [b] = [b] := by
  simp [encodeBytes, h]

/-- Single large byte (`b ≥ 0x80`): encoded as `[0x81, b]`.
@isnad1 id=eq.1h1v.s5.f680217f8145 from=translated src=- shape=4255141d vocab=d62f073e
-/
theorem encodeBytes_single_large (b : Byte) (h : ¬ b.toNat < 0x80) :
    encodeBytes [b] = [BitVec.ofNat 8 0x81, b] := by
  simp [encodeBytes, h]

/-- Two-byte short string: `encodeBytes [a, b] = [0x82, a, b]`.
    No canonical-form branching applies; `data.length = 2 > 1` skips
    the single-byte path, and `2 ≤ 55` selects the short-string form.
@isnad1 id=eq.0h2v.s5.9f41ab4bf2f7 from=translated src=- shape=7fea04b5 vocab=0ec3488c
-/
theorem encodeBytes_pair (a b : Byte) :
    encodeBytes [a, b] = [BitVec.ofNat 8 0x82, a, b] := by
  simp [encodeBytes]

/-- Three-byte short string: `encodeBytes [a, b, c] = [0x83, a, b, c]`.
@isnad1 id=eq.0h3v.s6.af143fd79375 from=translated src=- shape=2546b8a3 vocab=0ec3488c
-/
theorem encodeBytes_triple (a b c : Byte) :
    encodeBytes [a, b, c] = [BitVec.ofNat 8 0x83, a, b, c] := by
  simp [encodeBytes]

/-- Four-byte short string: `encodeBytes [a, b, c, d] = [0x84, a, b, c, d]`.
@isnad1 id=eq.0h4v.s6.35b031483b16 from=translated src=- shape=3e0f679a vocab=0ec3488c
-/
theorem encodeBytes_quad (a b c d : Byte) :
    encodeBytes [a, b, c, d] = [BitVec.ofNat 8 0x84, a, b, c, d] := by
  simp [encodeBytes]

/-- Five-byte short string:
    `encodeBytes [a, b, c, d, e] = [0x85, a, b, c, d, e]`.
@isnad1 id=eq.0h5v.s6.452839488ced from=translated src=- shape=7cfafdf4 vocab=0ec3488c
-/
theorem encodeBytes_quint (a b c d e : Byte) :
    encodeBytes [a, b, c, d, e] = [BitVec.ofNat 8 0x85, a, b, c, d, e] := by
  simp [encodeBytes]

/-- Six-byte short string:
    `encodeBytes [a, b, c, d, e, f] = [0x86, a, b, c, d, e, f]`.
@isnad1 id=eq.0h6v.s6.9a1ae49f4db3 from=translated src=- shape=d62c5a47 vocab=0ec3488c
-/
theorem encodeBytes_sext (a b c d e f : Byte) :
    encodeBytes [a, b, c, d, e, f] =
      [BitVec.ofNat 8 0x86, a, b, c, d, e, f] := by
  simp [encodeBytes]

/-- Seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g] = [0x87, a, b, c, d, e, f, g]`.
@isnad1 id=eq.0h7v.s6.a313fef77e2e from=translated src=- shape=9cbba441 vocab=0ec3488c
-/
theorem encodeBytes_sept (a b c d e f g : Byte) :
    encodeBytes [a, b, c, d, e, f, g] =
      [BitVec.ofNat 8 0x87, a, b, c, d, e, f, g] := by
  simp [encodeBytes]

/-- Eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h] = [0x88, a, b, c, d, e, f, g, h]`.
@isnad1 id=eq.0h8v.s7.575fe47e1525 from=translated src=- shape=2b6b5c53 vocab=0ec3488c
-/
theorem encodeBytes_oct (a b c d e f g h : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h] =
      [BitVec.ofNat 8 0x88, a, b, c, d, e, f, g, h] := by
  simp [encodeBytes]

/-- Nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i] = [0x89, a, b, c, d, e, f, g, h, i]`.
@isnad1 id=eq.0h9v.s7.84f1f2d7b1f0 from=translated src=- shape=f7ca8261 vocab=0ec3488c
-/
theorem encodeBytes_nonuple (a b c d e f g h i : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i] =
      [BitVec.ofNat 8 0x89, a, b, c, d, e, f, g, h, i] := by
  simp [encodeBytes]

/-- Ten-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j] = [0x8A, a, b, c, d, e, f, g, h, i, j]`.
@isnad1 id=eq.0h10v.s7.ddbd8533882d from=translated src=- shape=9258a2e2 vocab=0ec3488c
-/
theorem encodeBytes_decuple (a b c d e f g h i j : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j] =
      [BitVec.ofNat 8 0x8A, a, b, c, d, e, f, g, h, i, j] := by
  simp [encodeBytes]

/-- Eleven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k] =
    [0x8B, a, b, c, d, e, f, g, h, i, j, k]`.
@isnad1 id=eq.0h11v.s7.2d772fecf6d1 from=translated src=- shape=04e3e9db vocab=0ec3488c
-/
theorem encodeBytes_undecuple (a b c d e f g h i j k : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k] =
      [BitVec.ofNat 8 0x8B, a, b, c, d, e, f, g, h, i, j, k] := by
  simp [encodeBytes]

/-- Twelve-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l] =
    [0x8C, a, b, c, d, e, f, g, h, i, j, k, l]`.
@isnad1 id=eq.0h12v.s7.816723e7dbbb from=translated src=- shape=2c653960 vocab=0ec3488c
-/
theorem encodeBytes_duodecuple (a b c d e f g h i j k l : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l] =
      [BitVec.ofNat 8 0x8C, a, b, c, d, e, f, g, h, i, j, k, l] := by
  simp [encodeBytes]

/-- Thirteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m] =
    [0x8D, a, b, c, d, e, f, g, h, i, j, k, l, m]`.
@isnad1 id=eq.0h13v.s7.5cccc6e296ca from=translated src=- shape=405edc3b vocab=0ec3488c
-/
theorem encodeBytes_tredecuple (a b c d e f g h i j k l m : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m] =
      [BitVec.ofNat 8 0x8D, a, b, c, d, e, f, g, h, i, j, k, l, m] := by
  simp [encodeBytes]

/-- Fourteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n] =
    [0x8E, a, b, c, d, e, f, g, h, i, j, k, l, m, n]`.
@isnad1 id=eq.0h14v.s7.be4e3385b64e from=translated src=- shape=0526d0d2 vocab=0ec3488c
-/
theorem encodeBytes_quattuordecuple (a b c d e f g h i j k l m n : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n] =
      [BitVec.ofNat 8 0x8E, a, b, c, d, e, f, g, h, i, j, k, l, m, n] := by
  simp [encodeBytes]

/-- Fifteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] =
    [0x8F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]`.
@isnad1 id=eq.0h15v.s7.b83832d6b4db from=translated src=- shape=a7dc5eea vocab=0ec3488c
-/
theorem encodeBytes_quindecuple (a b c d e f g h i j k l m n o : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] =
      [BitVec.ofNat 8 0x8F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] := by
  simp [encodeBytes]

/-- Sixteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] =
    [0x90, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]`.
@isnad1 id=eq.0h16v.s7.af817a876976 from=translated src=- shape=cc896eee vocab=0ec3488c
-/
theorem encodeBytes_sedecuple (a b c d e f g h i j k l m n o p : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] =
      [BitVec.ofNat 8 0x90, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] := by
  simp [encodeBytes]

/-- Seventeen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] =
    [0x91, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q]`.
@isnad1 id=eq.0h17v.s7.6ec445a74d5a from=translated src=- shape=c4fea530 vocab=0ec3488c
-/
theorem encodeBytes_septendecuple (a b c d e f g h i j k l m n o p q : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] =
      [BitVec.ofNat 8 0x91, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] := by
  simp [encodeBytes]

/-- Eighteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] =
    [0x92, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r]`.
@isnad1 id=eq.0h18v.s8.8620b98d324e from=translated src=- shape=b0e2173b vocab=0ec3488c
-/
theorem encodeBytes_octodecuple (a b c d e f g h i j k l m n o p q r : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] =
      [BitVec.ofNat 8 0x92, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] := by
  simp [encodeBytes]

/-- Nineteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] =
    [0x93, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s]`.
@isnad1 id=eq.0h19v.s8.49b35a35d657 from=translated src=- shape=5552a38b vocab=0ec3488c
-/
theorem encodeBytes_novemdecuple (a b c d e f g h i j k l m n o p q r s : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] =
      [BitVec.ofNat 8 0x93, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] := by
  simp [encodeBytes]

/-- Twenty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =
    [0x94, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t]`.
@isnad1 id=eq.0h20v.s8.9039e5ca07af from=translated src=- shape=c97e58a6 vocab=0ec3488c
-/
theorem encodeBytes_viguple (a b c d e f g h i j k l m n o p q r s t : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =
      [BitVec.ofNat 8 0x94, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] := by
  simp [encodeBytes]

/-- Twenty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] =
    [0x95, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u]`.
@isnad1 id=eq.0h21v.s8.534285240856 from=translated src=- shape=4b7410c1 vocab=0ec3488c
-/
theorem encodeBytes_unviguple (a b c d e f g h i j k l m n o p q r s t u : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] =
      [BitVec.ofNat 8 0x95, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] := by
  simp [encodeBytes]

/-- Twenty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v] =
    [0x96, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v]`.
@isnad1 id=eq.0h22v.s8.ddf66759075f from=translated src=- shape=b4c2920d vocab=0ec3488c
-/
theorem encodeBytes_duoviguple (a b c d e f g h i j k l m n o p q r s t u v : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v] =
      [BitVec.ofNat 8 0x96, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v] := by
  simp [encodeBytes]

/-- Twenty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w] =
    [0x97, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w]`.
@isnad1 id=eq.0h23v.s8.2e7276af34d2 from=translated src=- shape=957d1a52 vocab=0ec3488c
-/
theorem encodeBytes_tresviguple (a b c d e f g h i j k l m n o p q r s t u v w : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w] =
      [BitVec.ofNat 8 0x97, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w] := by
  simp [encodeBytes]

/-- Twenty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x] =
    [0x98, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x]`.
@isnad1 id=eq.0h24v.s8.0d9216bd81db from=translated src=- shape=bc2030ca vocab=0ec3488c
-/
theorem encodeBytes_quattuorviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x] =
      [BitVec.ofNat 8 0x98, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x] := by
  simp [encodeBytes]

/-- Twenty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y] =
    [0x99, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y]`.
@isnad1 id=eq.0h25v.s8.31c9f2c69aa9 from=translated src=- shape=23724aad vocab=0ec3488c
-/
theorem encodeBytes_quinviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y] =
      [BitVec.ofNat 8 0x99, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y] := by
  simp [encodeBytes]

/-- Twenty-six-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z] =
    [0x9A, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]`.
@isnad1 id=eq.0h26v.s8.7420d83ffde5 from=translated src=- shape=1f762737 vocab=0ec3488c
-/
theorem encodeBytes_sesviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z] =
      [BitVec.ofNat 8 0x9A, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z] := by
  simp [encodeBytes]

/-- Twenty-seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa] =
    [0x9B, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa]`.
@isnad1 id=eq.0h27v.s8.2b6a4b7d46f0 from=translated src=- shape=6658ed8c vocab=0ec3488c
-/
theorem encodeBytes_septemviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa] =
      [BitVec.ofNat 8 0x9B, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa] := by
  simp [encodeBytes]

/-- Twenty-eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab] =
    [0x9C, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab]`.
@isnad1 id=eq.0h28v.s8.80c7ebbb3832 from=translated src=- shape=3aa4b721 vocab=0ec3488c
-/
theorem encodeBytes_duodetrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab] =
      [BitVec.ofNat 8 0x9C, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab] := by
  simp [encodeBytes]

/-- Twenty-nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac] =
    [0x9D, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac]`.
@isnad1 id=eq.0h29v.s8.bb8688c71e77 from=translated src=- shape=ae27031a vocab=0ec3488c
-/
theorem encodeBytes_undetrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac] =
      [BitVec.ofNat 8 0x9D, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac] := by
  simp [encodeBytes]

/-- Thirty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad] =
    [0x9E, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad]`.
@isnad1 id=eq.0h30v.s8.46eb8aa094ab from=translated src=- shape=fe5540bc vocab=0ec3488c
-/
theorem encodeBytes_trigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad] =
      [BitVec.ofNat 8 0x9E, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad] := by
  simp [encodeBytes]

/-- Thirty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae] =
    [0x9F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae]`.
@isnad1 id=eq.0h31v.s8.a95ee9dc76d2 from=translated src=- shape=e08f6a3b vocab=0ec3488c
-/
theorem encodeBytes_untrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae] =
      [BitVec.ofNat 8 0x9F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae] := by
  simp [encodeBytes]

/-- Thirty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af] =
    [0xA0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af]`.
@isnad1 id=eq.0h32v.s8.4187c9e228a8 from=translated src=- shape=e4f81382 vocab=0ec3488c
-/
theorem encodeBytes_duotrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af] =
      [BitVec.ofNat 8 0xA0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af] := by
  simp [encodeBytes]

/-- Thirty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag] =
    [0xA1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag]`.
@isnad1 id=eq.0h33v.s8.99d5cc905ba1 from=translated src=- shape=f21442c1 vocab=0ec3488c
-/
theorem encodeBytes_trestrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag] =
      [BitVec.ofNat 8 0xA1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag] := by
  simp [encodeBytes]

/-- Thirty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah] =
    [0xA2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah]`.
@isnad1 id=eq.0h34v.s8.fc16059e2d9b from=translated src=- shape=500c3194 vocab=0ec3488c
-/
theorem encodeBytes_quattuortrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah] =
      [BitVec.ofNat 8 0xA2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah] := by
  simp [encodeBytes]

/-- Thirty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] =
    [0xA3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai]`.
@isnad1 id=eq.0h35v.s8.6c3eda7ee911 from=translated src=- shape=bbd944cd vocab=0ec3488c
-/
theorem encodeBytes_quintrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] =
      [BitVec.ofNat 8 0xA3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] := by
  simp [encodeBytes]

/-- Thirty-six-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] =
    [0xA4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj]`.
@isnad1 id=eq.0h36v.s8.a2c1d37c42d5 from=translated src=- shape=61049343 vocab=0ec3488c
-/
theorem encodeBytes_sestrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] =
      [BitVec.ofNat 8 0xA4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] := by
  simp [encodeBytes]

/-- Thirty-seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] =
    [0xA5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak]`.
@isnad1 id=eq.0h37v.s8.ba287da07560 from=translated src=- shape=231b0480 vocab=0ec3488c
-/
theorem encodeBytes_septemtrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] =
      [BitVec.ofNat 8 0xA5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] := by
  simp [encodeBytes]

/-- Thirty-eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] =
    [0xA6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al]`.
@isnad1 id=eq.0h38v.s8.e9749ff9cc2d from=translated src=- shape=2039d9f6 vocab=0ec3488c
-/
theorem encodeBytes_duodequadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] =
      [BitVec.ofNat 8 0xA6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] := by
  simp [encodeBytes]

/-- Thirty-nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] =
    [0xA7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am]`.
@isnad1 id=eq.0h39v.s8.84250b1c2cbd from=translated src=- shape=f8bdb895 vocab=0ec3488c
-/
theorem encodeBytes_undequadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] =
      [BitVec.ofNat 8 0xA7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] := by
  simp [encodeBytes]

/-- Forty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] =
    [0xA8, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an]`.
@isnad1 id=eq.0h40v.s8.96ce33432451 from=translated src=- shape=e3940488 vocab=0ec3488c
-/
theorem encodeBytes_quadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] =
      [BitVec.ofNat 8 0xA8, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] := by
  simp [encodeBytes]

/-- Forty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] =
    [0xA9, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao]`.
@isnad1 id=eq.0h41v.s8.2ad91f64a8ee from=translated src=- shape=f3d7cf19 vocab=0ec3488c
-/
theorem encodeBytes_unquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] =
      [BitVec.ofNat 8 0xA9, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] := by
  simp [encodeBytes]

/-- Forty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap] =
    [0xAA, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap]`.
@isnad1 id=eq.0h42v.s8.a7f33a7ad01a from=translated src=- shape=e4d40540 vocab=0ec3488c
-/
theorem encodeBytes_duoquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap] =
      [BitVec.ofNat 8 0xAA, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap] := by
  simp [encodeBytes]

/-- Forty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq] =
    [0xAB, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq]`.
@isnad1 id=eq.0h43v.s8.8adc517f8de8 from=translated src=- shape=78cc2c96 vocab=0ec3488c
-/
theorem encodeBytes_tresquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq] =
      [BitVec.ofNat 8 0xAB, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq] := by
  simp [encodeBytes]

/-! ## Encoding produces non-empty output -/

/--
@isnad1 id=lt.0h1v.s3.c9774e392115 from=translated src=- shape=3ef63426 vocab=49394458
-/
theorem encodeBytes_nonempty (data : List Byte) :
    (encodeBytes data).length > 0 := by
  simp [encodeBytes]
  split
  · split <;> simp
  · split <;> simp [List.length_append]

/--
@isnad1 id=lt.0h1v.s3.a484398ac41f from=translated src=- shape=8e1bdd70 vocab=4c65ea79
-/
theorem encode_nonempty (item : RLPItem) : (encode item).length > 0 := by
  cases item with
  | bytes data => exact encodeBytes_nonempty data
  | list items =>
    simp [encode]
    split <;> simp [List.length_append]

/-! ## Round-trip correctness (parametric cases)

These lemmas prove `decode (encode (.bytes [b])) = some (.bytes [b], [])`
mechanically (not via `decide`) by chaining the existing `encodeBytes_*`
and `decode_*` characterizations. They cover the single-byte cases
across all values of `b` — useful as building blocks for an eventual
fully parametric round-trip theorem. -/

/-- Single-byte round-trip for small bytes (`b < 0x80`): the byte is
    its own encoding, and the decoder maps it back to `.bytes [b]`.
@isnad1 id=eq.1h1v.s5.c40527f3be99 from=translated src=- shape=ad009e6b vocab=72d10d08
-/
theorem decode_encode_bytes_single_small (b : Byte) (h : b.toNat < 0x80) :
    decode (encode (.bytes [b])) = some (.bytes [b], []) := by
  simp only [encode, encodeBytes_single_small _ h, decode_single_byte _ h]

/-- Empty byte string round-trip:
    `decode (encode (.bytes [])) = some (.bytes [], [])`. Chains
    `encodeBytes_nil` with `decode_empty_string`.
@isnad1 id=eq.0h0v.s4.938b1dd8c505 from=translated src=- shape=25821987 vocab=16a0a533
-/
theorem decode_encode_bytes_empty :
    decode (encode (.bytes [])) = some (.bytes [], []) := by
  simp only [encode, encodeBytes_nil]
  exact decode_empty_string

/-- Single-byte round-trip for large bytes (`b ≥ 0x80`): encoded as the
    two-byte sequence `[0x81, b]`, then the decoder reads the prefix
    as a one-byte short string, applies the canonical-form check
    (which passes because `b ≥ 0x80`), and returns `.bytes [b]`.
@isnad1 id=eq.1h1v.s5.6997339c476f from=translated src=- shape=240e3753 vocab=72d10d08
-/
theorem decode_encode_bytes_single_large (b : Byte) (h : ¬ b.toNat < 0x80) :
    decode (encode (.bytes [b])) = some (.bytes [b], []) := by
  rw [show encode (.bytes [b]) = [BitVec.ofNat 8 0x81, b] from
    encodeBytes_single_large b h]
  simp [decode, decodeAux, takeBytes, h]

/-- 8-bit truncation round-trips for values `< 256`.-/
private theorem toNat_ofNat8_of_lt {x : Nat} (h : x < 256) :
    (BitVec.ofNat 8 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

/-- Round-trip for a non-singleton short byte string (`length ≤ 55` and `≠ 1`,
    so `[]` and length `≥ 2`): the encoder emits `[0x80 + len] ++ data`, which
    classifies as `shortBytes` with payload length `len`; `takeBytes` consumes
    exactly `data`, and the non-singleton match branch returns `.bytes data`.
@isnad1 id=eq.2h1v.s5.256c8691214f from=translated src=- shape=6a60eb7e vocab=b25f07d9
-/
theorem decode_encode_bytes_short_general (data : List Byte)
    (hne1 : data.length ≠ 1) (hlen : data.length ≤ 55) :
    decode (encode (.bytes data)) = some (.bytes data, []) := by
  have hlt : 0x80 + data.length < 256 := by omega
  have henc : encode (.bytes data)
      = BitVec.ofNat 8 (0x80 + data.length) :: data := by
    show encodeBytes data = _
    rw [encodeBytes_short_of_length_ne_one data hlen hne1]; rfl
  have htoNat : (BitVec.ofNat 8 (0x80 + data.length)).toNat = 0x80 + data.length :=
    toNat_ofNat8_of_lt hlt
  have hclass : classifyPrefix (BitVec.ofNat 8 (0x80 + data.length)) = .shortBytes := by
    rw [classifyPrefix_shortBytes_iff, htoNat]; omega
  have hpl : rlpPrefixShortBytesPayloadLen (BitVec.ofNat 8 (0x80 + data.length))
      = data.length := by
    rw [rlpPrefixShortBytesPayloadLen_def, htoNat]; omega
  rw [henc, decode_cons_eq_classifyPrefix_match, hclass, hpl,
      takeBytes_length_ge (Nat.le_refl data.length)]
  simp only [List.take_length, List.drop_length, Option.bind_eq_bind, Option.bind_some]
  rcases data with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rfl
  · simp at hne1
  · rfl

/-- General short byte-string round-trip (`length ≤ 55`): dispatches on the
    encoder's structure — the two singleton special cases plus the non-singleton
    `decode_encode_bytes_short_general`.
@isnad1 id=eq.1h1v.s5.b4fb51dba5cc from=translated src=- shape=2141e351 vocab=b25f07d9
-/
theorem decode_encode_bytes_short (data : List Byte) (hlen : data.length ≤ 55) :
    decode (encode (.bytes data)) = some (.bytes data, []) := by
  rcases data with _ | ⟨b, _ | ⟨c, t⟩⟩
  · exact decode_encode_bytes_short_general [] (by simp) hlen
  · by_cases hb : b.toNat < 0x80
    · exact decode_encode_bytes_single_small b hb
    · exact decode_encode_bytes_single_large b hb
  · exact decode_encode_bytes_short_general (b :: c :: t) (by simp) hlen

/-! ### Long byte-string round-trip (`length > 55`)

The long form encodes the payload length as a big-endian length field. The
round-trip needs three `toBytesBE` facts — the encoded length fits in `≤ 8`
bytes (matching the decoder's length-of-length range `[1,8]`), is nonempty, and
has a nonzero leading byte (so `readLength`'s leading-zero canonicity check
passes) — together with the `fromBytesBE`/`toBytesBE` round-trip. -/

/-- The minimal big-endian encoding of a value `< 256 ^ k` uses at most `k`
    bytes. Induction follows `toBytesBE`'s division recursion.
@isnad1 id=le.1h2v.s5.fcb9b58a9182 from=translated src=- shape=bb4fef2c vocab=81cd87d9
-/
theorem Nat.toBytesBE_length_le :
    ∀ (len k : Nat), len < 256 ^ k → (Nat.toBytesBE len).length ≤ k := by
  intro len
  induction len using Nat.toBytesBE.induct with
  | case1 => intro k _; simp [Nat.toBytesBE]
  | case2 m _hlt ih =>
    intro k h
    rw [Nat.toBytesBE_succ, List.length_append, List.length_cons, List.length_nil]
    cases k with
    | zero => rw [Nat.pow_zero] at h; omega
    | succ k' =>
      have hpow : 256 ^ (k' + 1) = 256 ^ k' * 256 := by rw [Nat.pow_succ]
      have hk : (m + 1) / 256 < 256 ^ k' := by omega
      have := ih k' hk
      omega

/-- **A canonical field's width is bounded by its value.** For a byte list with
    no leading zero, `fromBytesBE bs < 256 ^ k` forces `bs.length ≤ k`.

    This is the converse direction of `fromBytesBE_lt`, and it only holds under
    canonicality — `[0, 0, 1]` decodes to `1 < 256 ^ 1` while being three bytes
    long. It is what lets a caller state a width restriction over the *decoded
    value* rather than over the encoding: given a decoder that already rejects
    leading zeros, "fits in `k` bytes" and "is `< 256 ^ k`" are interchangeable
    (#11513).
@isnad1 id=le.2h2v.s5.bc7fa7def139 from=translated src=- shape=4bd70dcf vocab=ac036120
-/
theorem Nat.length_le_of_canonical_lt {bs : List Byte} {k : Nat}
    (hcanon : bs.headD 1 ≠ 0) (hlt : Nat.fromBytesBE bs < 256 ^ k) :
    bs.length ≤ k := by
  have hround := Nat.toBytesBE_fromBytesBE_of_canonical bs hcanon
  calc bs.length = (Nat.toBytesBE (Nat.fromBytesBE bs)).length := by rw [hround]
    _ ≤ k := Nat.toBytesBE_length_le _ _ hlt

/-- The minimal big-endian encoding of a positive value is a nonempty list whose
    leading (most-significant) byte is nonzero — the canonical no-leading-zero
    shape. Induction follows `toBytesBE`'s division recursion.
@isnad1 id=ex.1h1v.s5.5993142bbe30 from=translated src=- shape=313e4cc6 vocab=1e7cb535
-/
theorem Nat.toBytesBE_eq_cons_of_pos :
    ∀ (n : Nat), 0 < n →
      ∃ b tl, Nat.toBytesBE n = b :: tl ∧ b ≠ (0 : Byte) := by
  intro n
  induction n using Nat.toBytesBE.induct with
  | case1 => intro h; omega
  | case2 m _hlt ih =>
    intro _h
    rw [Nat.toBytesBE_succ]
    by_cases hq : (m + 1) / 256 = 0
    · rw [hq, Nat.toBytesBE_zero, List.nil_append]
      refine ⟨BitVec.ofNat 8 ((m + 1) % 256), [], rfl, ?_⟩
      have hlt : m + 1 < 256 := by omega
      have hmod : (m + 1) % 256 = m + 1 := Nat.mod_eq_of_lt hlt
      rw [hmod]
      intro hcontra
      have h0 : (BitVec.ofNat 8 (m + 1)).toNat = 0 := by rw [hcontra]; rfl
      rw [toNat_ofNat8_of_lt hlt] at h0
      omega
    · obtain ⟨b, tl, hbtl, hb⟩ := ih (Nat.pos_of_ne_zero hq)
      rw [hbtl, List.cons_append]
      exact ⟨b, tl ++ [BitVec.ofNat 8 ((m + 1) % 256)], rfl, hb⟩

/-- `readLength` recovers the length from a canonical big-endian length field:
    reading `(toBytesBE len).length` bytes off `toBytesBE len ++ rest` returns
    `len` (via the `fromBytesBE` round-trip) and the remaining `rest`. The
    leading-zero check passes because `toBytesBE`'s leading byte is nonzero.
@isnad1 id=eq.1h2v.s5.5e0777911807 from=translated src=- shape=c87a704e vocab=18a0d62c
-/
theorem readLength_toBytesBE_append (len : Nat) (rest : List Byte) (hpos : 0 < len) :
    readLength (Nat.toBytesBE len ++ rest) (Nat.toBytesBE len).length
      = some (len, rest) := by
  obtain ⟨b, tl, hbtl, hb⟩ := Nat.toBytesBE_eq_cons_of_pos len hpos
  have htake : takeBytes (Nat.toBytesBE len ++ rest) (Nat.toBytesBE len).length
      = some (b :: tl, rest) := by
    rw [takeBytes_length_ge (by rw [List.length_append]; omega),
        List.take_left, List.drop_left, hbtl]
  rw [readLength_some_of_takeBytes_nonzero htake hb, ← hbtl,
      Nat.fromBytesBE_toBytesBE]

/-- Long-form byte-string encoding (`length > 55`): the encoder emits the
    `0xB7 + lenOfLen` prefix, the big-endian length field, then the payload.
@isnad1 id=eq.1h1v.s6.b1e6c836efc0 from=translated src=- shape=0dfda435 vocab=41bf04d9
-/
theorem encodeBytes_long_of_length (data : List Byte) (hlen : 55 < data.length) :
    encodeBytes data
      = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
          ++ Nat.toBytesBE data.length ++ data := by
  cases data with
  | nil => simp at hlen
  | cons a tl =>
    cases tl with
    | nil => simp at hlen
    | cons b t =>
      have hnle : ¬ t.length ≤ 53 := by
        simp only [List.length_cons] at hlen; omega
      simp [encodeBytes, hnle]

/-- Long byte-string round-trip (`55 < length < 256 ^ 8`): the encoded prefix
    classifies as `longBytes` with length-of-length `(toBytesBE len).length ∈
    [1,8]`; `readLength` recovers `len`, the `> 55` check passes, and `takeBytes`
    consumes exactly the payload.
@isnad1 id=eq.2h1v.s6.5c3303ed2fa2 from=translated src=- shape=ba47ef25 vocab=4ffa19be
-/
theorem decode_encode_bytes_long (data : List Byte)
    (hlong : 55 < data.length) (hlen : data.length < 256 ^ 8) :
    decode (encode (.bytes data)) = some (.bytes data, []) := by
  obtain ⟨b0, tl0, hcons, _hb0⟩ := Nat.toBytesBE_eq_cons_of_pos data.length (by omega)
  have hL1 : 1 ≤ (Nat.toBytesBE data.length).length := by rw [hcons]; simp
  have hL8 : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le _ _ hlen
  have hpfxlt : 0xB7 + (Nat.toBytesBE data.length).length < 256 := by omega
  have htoNat : (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)).toNat
      = 0xB7 + (Nat.toBytesBE data.length).length := toNat_ofNat8_of_lt hpfxlt
  have henc : encode (.bytes data)
      = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)
          :: (Nat.toBytesBE data.length ++ data) := by
    show encodeBytes data = _
    rw [encodeBytes_long_of_length data hlong]; rfl
  have hclass : classifyPrefix (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length))
      = .longBytes := by
    rw [classifyPrefix_longBytes_iff, htoNat]; omega
  have hlol : rlpPrefixLongBytesLenOfLen
      (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length))
      = (Nat.toBytesBE data.length).length := by
    rw [rlpPrefixLongBytesLenOfLen_def, htoNat]; omega
  rw [henc, decode_cons_eq_classifyPrefix_match, hclass, hlol,
      readLength_toBytesBE_append data.length data (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [ite_eq_right (by omega : ¬ data.length ≤ 55),
      takeBytes_length_ge (Nat.le_refl data.length)]
  simp only [Option.bind_some, List.take_length, List.drop_length]

/-- General byte-string round-trip: any byte payload short enough for the
    8-byte length field (`length < 256 ^ 8`, i.e. every length the decoder
    supports) re-decodes to itself. Combines the short (`≤ 55`) and long
    (`> 55`) cases.
@isnad1 id=eq.1h1v.s5.0bea802421b9 from=translated src=- shape=a660b8b2 vocab=4ffa19be
-/
theorem decode_encode_bytes (data : List Byte) (hlen : data.length < 256 ^ 8) :
    decode (encode (.bytes data)) = some (.bytes data, []) := by
  by_cases hshort : data.length ≤ 55
  · exact decode_encode_bytes_short data hshort
  · exact decode_encode_bytes_long data (by omega) hlen

/-! ### Fuel-parametric, append-general byte round-trip

For the mutual list round-trip, the byte case must hold for `decodeAux (m+1)` at
arbitrary fuel and with an arbitrary trailing `rest` (a sibling item's encoding).
This re-expresses the byte round-trip on the `decodeAux (nDepth+1)` bridges. -/

/-- Splitting off a known-length prefix from an append.
@isnad1 id=eq.0h2v.s5.38aaa2a6f5e3 from=translated src=- shape=08279f07 vocab=917d7d39
-/
theorem takeBytes_append_length (xs ys : List Byte) :
    takeBytes (xs ++ ys) xs.length = some (xs, ys) := by
  rw [takeBytes_length_ge (by rw [List.length_append]; omega),
      List.take_left, List.drop_left]

/-- Parametric non-singleton short byte round-trip (`length ≠ 1`, `≤ 55`).
@isnad1 id=eq.2h3v.s6.ce31fc440a24 from=translated src=- shape=f003a426 vocab=6f4325c8
-/
theorem decodeAux_succ_encodeBytes_short_append (m : Nat) (data rest : List Byte)
    (hne1 : data.length ≠ 1) (hsh : data.length ≤ 55) :
    decodeAux (m + 1) (encodeBytes data ++ rest) = some (.bytes data, rest) := by
  have hlt : 0x80 + data.length < 256 := by omega
  have htoNat : (BitVec.ofNat 8 (0x80 + data.length)).toNat = 0x80 + data.length :=
    toNat_ofNat8_of_lt hlt
  have hclass : classifyPrefix (BitVec.ofNat 8 (0x80 + data.length)) = .shortBytes := by
    rw [classifyPrefix_shortBytes_iff, htoNat]; omega
  have hpl : rlpPrefixShortBytesPayloadLen (BitVec.ofNat 8 (0x80 + data.length))
      = data.length := by
    rw [rlpPrefixShortBytesPayloadLen_def, htoNat]; omega
  have henc : encodeBytes data = BitVec.ofNat 8 (0x80 + data.length) :: data := by
    rw [encodeBytes_short_of_length_ne_one data hsh hne1]; rfl
  rw [henc]
  show decodeAux (m + 1) (BitVec.ofNat 8 (0x80 + data.length) :: (data ++ rest))
      = some (.bytes data, rest)
  rw [decodeAux_cons_shortBytes_of_classifyPrefix m _ (data ++ rest) hclass, hpl,
      takeBytes_append_length data rest]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases data with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rfl
  · simp at hne1
  · rfl

/-- The byte case of the round-trip in the fuel-parametric, append-general form
    the mutual induction needs. Mirrors `decode_encode_bytes` but targets
    `decodeAux (m+1) (… ++ rest)` via the `decodeAux_cons_*_of_classifyPrefix`
    bridges.
@isnad1 id=eq.1h3v.s6.8ccf7c985995 from=translated src=- shape=c2c632f6 vocab=74e81b0a
-/
theorem decodeAux_succ_encodeBytes_append (m : Nat) (data rest : List Byte)
    (hlen : data.length < 256 ^ 8) :
    decodeAux (m + 1) (encodeBytes data ++ rest) = some (.bytes data, rest) := by
  by_cases h1 : data.length = 1
  · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h1
    by_cases hb : b.toNat < 0x80
    · rw [encodeBytes_single_small b hb]
      show decodeAux (m + 1) (b :: rest) = some (.bytes [b], rest)
      exact decodeAux_cons_singleByte_of_classifyPrefix m b rest
        ((classifyPrefix_singleByte_iff b).mpr hb)
    · rw [encodeBytes_single_large b hb]
      have hcl : classifyPrefix (BitVec.ofNat 8 0x81) = .shortBytes := by
        rw [classifyPrefix_shortBytes_iff]; decide
      show decodeAux (m + 1) (BitVec.ofNat 8 0x81 :: (b :: rest)) = some (.bytes [b], rest)
      rw [decodeAux_cons_shortBytes_of_classifyPrefix m _ (b :: rest) hcl,
          show rlpPrefixShortBytesPayloadLen (BitVec.ofNat 8 0x81) = 1 from by decide,
          show takeBytes (b :: rest) 1 = some ([b], rest) from by simp [takeBytes]]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right hb]
  · by_cases hsh : data.length ≤ 55
    · exact decodeAux_succ_encodeBytes_short_append m data rest h1 hsh
    · have hlong : 55 < data.length := by omega
      rw [encodeBytes_long_of_length data hlong]
      show decodeAux (m + 1)
          (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)
            :: ((Nat.toBytesBE data.length ++ data) ++ rest)) = some (.bytes data, rest)
      rw [List.append_assoc]
      have hL1 : 1 ≤ (Nat.toBytesBE data.length).length := by
        obtain ⟨b, tl, hcons, _⟩ := Nat.toBytesBE_eq_cons_of_pos data.length (by omega)
        rw [hcons]; simp
      have hL8 : (Nat.toBytesBE data.length).length ≤ 8 :=
        Nat.toBytesBE_length_le _ _ hlen
      have hpfxlt : 0xB7 + (Nat.toBytesBE data.length).length < 256 := by omega
      have htoNat : (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)).toNat
          = 0xB7 + (Nat.toBytesBE data.length).length := toNat_ofNat8_of_lt hpfxlt
      have hcl : classifyPrefix
          (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)) = .longBytes := by
        rw [classifyPrefix_longBytes_iff, htoNat]; omega
      have hlol : rlpPrefixLongBytesLenOfLen
          (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length))
          = (Nat.toBytesBE data.length).length := by
        rw [rlpPrefixLongBytesLenOfLen_def, htoNat]; omega
      rw [decodeAux_cons_longBytes_of_classifyPrefix m _
            (Nat.toBytesBE data.length ++ (data ++ rest)) hcl, hlol,
          readLength_toBytesBE_append data.length (data ++ rest) (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right (by omega : ¬ data.length ≤ 55), takeBytes_append_length data rest]
      simp only [Option.bind_some]

/-! ### Full round-trip via mutual fuel induction

`decodeAux`/`decodeItems` recurse structurally on the fuel `nDepth`, so a single
step induction on `nDepth` (proving an `decodeAux`-on-`encode` statement together
with a `decodeItems`-on-`encodeItems` statement) yields the mutual structure
without any induction on `RLPItem` itself. -/

/-- Short-list encoder shape (`payload ≤ 55`).
@isnad1 id=eq.1h1v.s5.85258d4fae9a from=translated src=- shape=a7eaa28c vocab=7fe8b1c1
-/
theorem encode_list_short (items : List RLPItem)
    (h : (encode.encodeItems items).length ≤ 55) :
    encode (.list items)
      = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
          :: encode.encodeItems items := by
  rw [encode]
  simp only [h, ite_true, List.singleton_append]

/-- Long-list encoder shape (`payload > 55`).
@isnad1 id=eq.1h1v.s6.fb10f21030dd from=translated src=- shape=c04fa8ef vocab=fa651020
-/
theorem encode_list_long (items : List RLPItem)
    (h : 55 < (encode.encodeItems items).length) :
    encode (.list items)
      = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
          :: (Nat.toBytesBE (encode.encodeItems items).length ++ encode.encodeItems items) := by
  rw [encode]
  rw [ite_eq_right (by omega)]
  rfl

/-- A byte string never shrinks under encoding (used to push the `< 256^8`
    size bound from an encoding down to its payload).
@isnad1 id=le.0h1v.s3.32f80fc7c895 from=translated src=- shape=f211ea19 vocab=ab367132
-/
theorem le_encodeBytes_length (data : List Byte) :
    data.length ≤ (encodeBytes data).length := by
  rcases data with _ | ⟨b, _ | ⟨c, t⟩⟩
  · simp [encodeBytes]
  · by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  · by_cases hsh : (b :: c :: t).length ≤ 55
    · rw [encodeBytes_short_of_length_ne_one (b :: c :: t) hsh (by simp)]
      simp
    · rw [encodeBytes_long_of_length (b :: c :: t) (by simp only [List.length_cons] at hsh ⊢; omega)]
      simp only [List.length_append, List.length_cons]; omega

/-- `decodeItems` one-step unfold on a nonempty input.
@isnad1 id=eq.1h2v.s7.d362fb03bbbe from=translated src=- shape=81022a7a vocab=0fc6f1ab
-/
theorem decodeItems_succ_of_ne_nil (m : Nat) (bs : List Byte) (h : bs ≠ []) :
    decodeItems (m + 1) bs =
      (do let (item, rest) ← decodeAux m bs
          let (items, rest') ← decodeItems m rest
          some (item :: items, rest')) := by
  obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-- The encode→decode round-trip, in mutual fuel-parametric form. Step induction
    on the fuel `nDepth` proves the single-item statement (`decodeAux` on
    `encode item ++ rest`) together with the item-sequence statement
    (`decodeItems` on `encode.encodeItems items`); each level's `.list`/cons case
    is supplied by the IH at `nDepth-1`.
@isnad1 id=and.0h1v.s7.469e314cabac from=translated src=- shape=52805474 vocab=51539582
-/
theorem decode_encode_mutual : ∀ (nDepth : Nat),
    (∀ (item : RLPItem) (rest : List Byte),
        (encode item).length < 256 ^ 8 →
        2 * (encode item).length ≤ nDepth →
        decodeAux nDepth (encode item ++ rest) = some (item, rest))
    ∧ (∀ (items : List RLPItem),
        (encode.encodeItems items).length < 256 ^ 8 →
        2 * (encode.encodeItems items).length < nDepth →
        decodeItems nDepth (encode.encodeItems items) = some (items, [])) := by
  intro nDepth
  induction nDepth with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro item rest _ hfuel
      have := encode_nonempty item; omega
    · intro items _ hfuel; omega
  | succ m ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨?_, ?_⟩
    · -- A (m+1)
      intro item rest hbound hfuel
      cases item with
      | bytes data =>
        have hdata : data.length < 256 ^ 8 :=
          Nat.lt_of_le_of_lt (le_encodeBytes_length data) hbound
        exact decodeAux_succ_encodeBytes_append m data rest hdata
      | list items =>
        by_cases hL55 : (encode.encodeItems items).length ≤ 55
        · -- short list
          have henc : encode (.list items)
              = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
                  :: encode.encodeItems items := encode_list_short items hL55
          rw [henc] at hbound hfuel
          simp only [List.length_cons] at hbound hfuel
          rw [henc]
          show decodeAux (m + 1)
              (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
                :: (encode.encodeItems items ++ rest)) = some (.list items, rest)
          have hpfxlt : 0xC0 + (encode.encodeItems items).length < 256 := by omega
          have htoNat : (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)).toNat
              = 0xC0 + (encode.encodeItems items).length := toNat_ofNat8_of_lt hpfxlt
          have hcl : classifyPrefix
              (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)) = .shortList := by
            rw [classifyPrefix_shortList_iff, htoNat]; omega
          have hpl : rlpPrefixShortListPayloadLen
              (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length))
              = (encode.encodeItems items).length := by
            rw [rlpPrefixShortListPayloadLen_def, htoNat]; omega
          have hitems : decodeItems m (encode.encodeItems items) = some (items, []) :=
            ihB items (by omega) (by omega)
          rw [decodeAux_cons_shortList_of_classifyPrefix m _
                (encode.encodeItems items ++ rest) hcl, hpl,
              takeBytes_append_length (encode.encodeItems items) rest]
          simp only [Option.bind_eq_bind, Option.bind_some, hitems, List.isEmpty_nil, ite_true]
        · -- long list
          have hlong : 55 < (encode.encodeItems items).length := by omega
          obtain ⟨b0, tl0, hcons, _⟩ :=
            Nat.toBytesBE_eq_cons_of_pos (encode.encodeItems items).length (by omega)
          have hL1 : 1 ≤ (Nat.toBytesBE (encode.encodeItems items).length).length := by
            rw [hcons]; simp
          have henc : encode (.list items)
              = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
                  :: (Nat.toBytesBE (encode.encodeItems items).length
                        ++ encode.encodeItems items) := encode_list_long items hlong
          rw [henc] at hbound hfuel
          simp only [List.length_cons, List.length_append] at hbound hfuel
          have hL8 : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
            Nat.toBytesBE_length_le _ _ (by omega)
          rw [henc]
          show decodeAux (m + 1)
              (BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
                :: ((Nat.toBytesBE (encode.encodeItems items).length
                      ++ encode.encodeItems items) ++ rest)) = some (.list items, rest)
          rw [List.append_assoc]
          have hpfxlt : 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length < 256 := by
            omega
          have htoNat :
              (BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)).toNat
              = 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length :=
            toNat_ofNat8_of_lt hpfxlt
          have hcl : classifyPrefix
              (BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length))
              = .longList := by
            rw [classifyPrefix_longList_iff, htoNat]; omega
          have hlol : rlpPrefixLongListLenOfLen
              (BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length))
              = (Nat.toBytesBE (encode.encodeItems items).length).length := by
            rw [rlpPrefixLongListLenOfLen_def, htoNat]; omega
          have hitems : decodeItems m (encode.encodeItems items) = some (items, []) :=
            ihB items (by omega) (by omega)
          rw [decodeAux_cons_longList_of_classifyPrefix m _
                (Nat.toBytesBE (encode.encodeItems items).length
                  ++ (encode.encodeItems items ++ rest)) hcl, hlol,
              readLength_toBytesBE_append (encode.encodeItems items).length
                (encode.encodeItems items ++ rest) (by omega)]
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [ite_eq_right (by omega : ¬ (encode.encodeItems items).length ≤ 55),
              takeBytes_append_length (encode.encodeItems items) rest]
          simp only [Option.bind_some, hitems, List.isEmpty_nil, ite_true]
    · -- B (m+1)
      intro items hbound hfuel
      cases items with
      | nil => rfl
      | cons i is =>
        have henc : encode.encodeItems (i :: is)
            = encode i ++ encode.encodeItems is := rfl
        have hpi := encode_nonempty i
        rw [henc] at hbound hfuel
        simp only [List.length_append] at hbound hfuel
        have hne : encode i ++ encode.encodeItems is ≠ [] := by
          intro hcontra
          rw [List.append_eq_nil_iff] at hcontra
          rw [hcontra.1] at hpi; simp at hpi
        have hAi : decodeAux m (encode i ++ encode.encodeItems is)
            = some (i, encode.encodeItems is) := ihA i _ (by omega) (by omega)
        have hBis : decodeItems m (encode.encodeItems is) = some (is, []) :=
          ihB is (by omega) (by omega)
        rw [henc, decodeItems_succ_of_ne_nil m _ hne, hAi]
        simp only [Option.bind_eq_bind, Option.bind_some, hBis]

/-- **Round-trip correctness (full).** Every RLP item whose encoding fits the
    decoder's 8-byte length field (`(encode item).length < 256^8` — implying the
    same bound for all nested payloads, since each sub-encoding is no longer than
    the whole) re-decodes to itself with no leftover. Specializes
    `decode_encode_mutual` at the `decode` fuel `2 * (encode item).length`.
@isnad1 id=eq.1h1v.s5.bd4fecd808d3 from=translated src=- shape=9ee85a4a vocab=41022127
-/
theorem decode_encode (item : RLPItem) (h : (encode item).length < 256 ^ 8) :
    decode (encode item) = some (item, []) := by
  have hA := (decode_encode_mutual (2 * (encode item).length)).1 item [] h (Nat.le_refl _)
  rw [List.append_nil] at hA
  rw [decode_eq_decodeAux_length]
  exact hA

/-- Discharges the round-trip hypothesis of
    `decodeFully_encode_of_decode_encode`: full decode of any encoded item
    (within the length bound) returns exactly that item.
@isnad1 id=eq.1h1v.s5.fc8b1a4e5c56 from=translated src=- shape=a409ef47 vocab=201d619e
-/
theorem decodeFully_encode (item : RLPItem) (h : (encode item).length < 256 ^ 8) :
    decodeFully (encode item) = some item :=
  decodeFully_encode_of_decode_encode (decode_encode item h)

/-- **Injectivity of `encode`** over items the decoder supports
    (`(encode i₁).length < 256^8`): distinct items never share an encoding. A
    direct corollary of the round-trip — both sides re-decode to themselves, so
    equal encodings force equal items.
@isnad1 id=eq.2h2v.s5.f09cfa8f4881 from=translated src=- shape=34e6b73f vocab=83e6a718
-/
theorem encode_injective {i₁ i₂ : RLPItem} (h : (encode i₁).length < 256 ^ 8)
    (heq : encode i₁ = encode i₂) : i₁ = i₂ := by
  have h₁ := decode_encode i₁ h
  have h₂ := decode_encode i₂ (heq ▸ h)
  rw [heq, h₂] at h₁
  simp only [Option.some.injEq, Prod.mk.injEq] at h₁
  exact h₁.1.symm

/-! ### Right inverse (decodability): a decoded item re-encodes to the bytes
    consumed. The three byte classes are non-recursive standalone lemmas; the two
    list classes are handled inline in `decode_right_inverse_mutual`. -/

/-- Right inverse, single-byte class.
@isnad1 id=eq.2h5v.s6.be30b33d6897 from=translated src=- shape=1a91f82f vocab=a89e4a70
-/
theorem decodeAux_singleByte_right_inv (m : Nat) (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte) (hcl : classifyPrefix pfx = .singleByte)
    (h : decodeAux (m + 1) (pfx :: rest0) = some (item, rest)) :
    pfx :: rest0 = encode item ++ rest := by
  rw [decodeAux_cons_singleByte_of_classifyPrefix m pfx rest0 hcl] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hi, hr⟩ := h; subst hi; subst hr
  show pfx :: rest0 = encodeBytes [pfx] ++ rest0
  rw [encodeBytes_single_small pfx ((classifyPrefix_singleByte_iff pfx).mp hcl)]; simp

/-- Right inverse, short-byte-string class.
@isnad1 id=eq.2h5v.s6.72a97c3671c6 from=translated src=- shape=1a91f82f vocab=307e387f
-/
theorem decodeAux_shortBytes_right_inv (m : Nat) (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte) (hcl : classifyPrefix pfx = .shortBytes)
    (h : decodeAux (m + 1) (pfx :: rest0) = some (item, rest)) :
    pfx :: rest0 = encode item ++ rest := by
  rw [decodeAux_cons_shortBytes_of_classifyPrefix m pfx rest0 hcl] at h
  have hrange := (classifyPrefix_shortBytes_iff pfx).mp hcl
  cases htk : takeBytes rest0 (rlpPrefixShortBytesPayloadLen pfx) with
  | none => rw [htk] at h; simp at h
  | some pair =>
    obtain ⟨data, rest'⟩ := pair
    obtain ⟨hsp, hpl⟩ := takeBytes_eq_some_imp htk
    rw [htk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    have hpfx : pfx = BitVec.ofNat 8 (0x80 + data.length) := by
      rw [hpl, rlpPrefixShortBytesPayloadLen_def,
          show 0x80 + (pfx.toNat - 0x80) = pfx.toNat from by omega, ofNat8_toNat]
    have h55 : data.length ≤ 55 := by rw [hpl, rlpPrefixShortBytesPayloadLen_def]; omega
    rcases data with _ | ⟨b, _ | ⟨c, t⟩⟩
    · -- []  (non-singleton)
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hi, hr⟩ := h; subst hi; subst hr
      show pfx :: rest0 = encodeBytes [] ++ rest'
      rw [encodeBytes_short_of_length_ne_one [] (by simp) (by simp), hsp, hpfx]; simp
    · -- [b]  (singleton)
      replace h : (if b.toNat < 0x80 then none
          else some (RLPItem.bytes [b], rest')) = some (item, rest) := h
      by_cases hb : b.toNat < 0x80
      · rw [ite_eq_left hb] at h; exact absurd h (by simp)
      · rw [ite_eq_right hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hr⟩ := h; subst hi; subst hr
        show pfx :: rest0 = encodeBytes [b] ++ rest'
        rw [encodeBytes_single_large b hb, hsp, hpfx]; simp
    · -- b :: c :: t  (non-singleton)
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hi, hr⟩ := h; subst hi; subst hr
      show pfx :: rest0 = encodeBytes (b :: c :: t) ++ rest'
      rw [encodeBytes_short_of_length_ne_one (b :: c :: t) h55 (by simp), hsp, hpfx]; simp

/-- Right inverse, long-byte-string class.
@isnad1 id=eq.2h5v.s6.a0553706f8cf from=translated src=- shape=1a91f82f vocab=a2db4810
-/
theorem decodeAux_longBytes_right_inv (m : Nat) (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte) (hcl : classifyPrefix pfx = .longBytes)
    (h : decodeAux (m + 1) (pfx :: rest0) = some (item, rest)) :
    pfx :: rest0 = encode item ++ rest := by
  rw [decodeAux_cons_longBytes_of_classifyPrefix m pfx rest0 hcl] at h
  have hrange := (classifyPrefix_longBytes_iff pfx).mp hcl
  cases hrd : readLength rest0 (rlpPrefixLongBytesLenOfLen pfx) with
  | none => rw [hrd] at h; simp at h
  | some pair =>
    obtain ⟨lenVal, rest'⟩ := pair
    rw [hrd] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    by_cases hle : lenVal ≤ 55
    · rw [ite_eq_left hle] at h; simp at h
    · rw [ite_eq_right hle] at h
      cases htk : takeBytes rest' lenVal with
      | none => rw [htk] at h; simp at h
      | some pair2 =>
        obtain ⟨data, rest''⟩ := pair2
        rw [htk] at h
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hr⟩ := h; subst hi; subst hr
        obtain ⟨lenBytes, hsp_rl, hlb_len, _hfb, himp⟩ := readLength_eq_some_imp hrd
        obtain ⟨hsp_tk, hdl⟩ := takeBytes_eq_some_imp htk
        have htobe : Nat.toBytesBE lenVal = lenBytes := himp (by omega)
        have hpfx : pfx = BitVec.ofNat 8 (0xB7 + lenBytes.length) := by
          rw [hlb_len, rlpPrefixLongBytesLenOfLen_def,
              show 0xB7 + (pfx.toNat - 0xB7) = pfx.toNat from by omega, ofNat8_toNat]
        show pfx :: rest0 = encodeBytes data ++ rest''
        rw [encodeBytes_long_of_length data (by rw [hdl]; omega), hdl, htobe, hpfx,
            hsp_rl, hsp_tk]
        simp [List.append_assoc]

/-- **Right inverse (decodability), mutual fuel form.** Whatever `decodeAux` /
    `decodeItems` accept re-encodes to exactly the consumed bytes. Step induction
    on the fuel `nDepth`: byte classes delegate to the standalone lemmas above;
    list classes recurse through `ihB`.
@isnad1 id=and.0h1v.s6.b5ee1117e130 from=translated src=- shape=341d654b vocab=e71a72ff
-/
theorem decode_right_inverse_mutual : ∀ (n : Nat),
    (∀ (bs : List Byte) (item : RLPItem) (rest : List Byte),
        decodeAux n bs = some (item, rest) → bs = encode item ++ rest)
    ∧ (∀ (bs : List Byte) (items : List RLPItem) (rest : List Byte),
        decodeItems n bs = some (items, rest)
          → bs = encode.encodeItems items ++ rest) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro bs item rest h; simp [decodeAux] at h
    · intro bs items rest h
      cases bs with
      | nil =>
        rw [show decodeItems 0 [] = some ([], []) from rfl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hr⟩ := h; subst hi; subst hr; rfl
      | cons a as => simp [decodeItems] at h
  | succ m ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨?_, ?_⟩
    · -- A (m+1)
      intro bs item rest h
      cases bs with
      | nil => simp [decodeAux] at h
      | cons pfx rest0 =>
        cases hcl : classifyPrefix pfx with
        | singleByte => exact decodeAux_singleByte_right_inv m pfx rest0 item rest hcl h
        | shortBytes => exact decodeAux_shortBytes_right_inv m pfx rest0 item rest hcl h
        | longBytes => exact decodeAux_longBytes_right_inv m pfx rest0 item rest hcl h
        | shortList =>
          rw [decodeAux_cons_shortList_of_classifyPrefix m pfx rest0 hcl] at h
          have hrange := (classifyPrefix_shortList_iff pfx).mp hcl
          cases htk : takeBytes rest0 (rlpPrefixShortListPayloadLen pfx) with
          | none => rw [htk] at h; simp at h
          | some pair =>
            obtain ⟨payload, rest'⟩ := pair
            obtain ⟨hsp, hpl⟩ := takeBytes_eq_some_imp htk
            rw [htk] at h
            simp only [Option.bind_eq_bind, Option.bind_some] at h
            cases hdi : decodeItems m payload with
            | none => rw [hdi] at h; simp at h
            | some pair2 =>
              obtain ⟨items, leftover⟩ := pair2
              rw [hdi] at h
              simp only [Option.bind_some] at h
              cases leftover with
              | cons x xs => simp at h
              | nil =>
                simp only [List.isEmpty_nil, ite_true, Option.some.injEq,
                  Prod.mk.injEq] at h
                obtain ⟨hi, hr⟩ := h; subst hi; subst hr
                have hib := ihB payload items [] hdi
                rw [List.append_nil] at hib
                have hpfx : pfx = BitVec.ofNat 8 (0xC0 + payload.length) := by
                  rw [hpl, rlpPrefixShortListPayloadLen_def,
                      show 0xC0 + (pfx.toNat - 0xC0) = pfx.toNat from by omega, ofNat8_toNat]
                have h55 : (encode.encodeItems items).length ≤ 55 := by
                  rw [← hib, hpl, rlpPrefixShortListPayloadLen_def]; omega
                show pfx :: rest0 = encode (.list items) ++ rest'
                rw [encode_list_short items h55, ← hib, hsp, hpfx]; simp
        | longList =>
          rw [decodeAux_cons_longList_of_classifyPrefix m pfx rest0 hcl] at h
          have hrange := (classifyPrefix_longList_iff pfx).mp hcl
          cases hrd : readLength rest0 (rlpPrefixLongListLenOfLen pfx) with
          | none => rw [hrd] at h; simp at h
          | some pair =>
            obtain ⟨lenVal, rest'⟩ := pair
            rw [hrd] at h
            simp only [Option.bind_eq_bind, Option.bind_some] at h
            by_cases hle : lenVal ≤ 55
            · rw [ite_eq_left hle] at h; simp at h
            · rw [ite_eq_right hle] at h
              cases htk : takeBytes rest' lenVal with
              | none => rw [htk] at h; simp at h
              | some pair2 =>
                obtain ⟨payload, rest''⟩ := pair2
                rw [htk] at h
                simp only [Option.bind_some] at h
                cases hdi : decodeItems m payload with
                | none => rw [hdi] at h; simp at h
                | some pair3 =>
                  obtain ⟨items, leftover⟩ := pair3
                  rw [hdi] at h
                  simp only [Option.bind_some] at h
                  cases leftover with
                  | cons x xs => simp at h
                  | nil =>
                    simp only [List.isEmpty_nil, ite_true, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨hi, hr⟩ := h; subst hi; subst hr
                    have hib := ihB payload items [] hdi
                    rw [List.append_nil] at hib
                    obtain ⟨lenBytes, hsp_rl, hlb_len, _hfb, himp⟩ :=
                      readLength_eq_some_imp hrd
                    obtain ⟨hsp_tk, hdl⟩ := takeBytes_eq_some_imp htk
                    have htobe : Nat.toBytesBE lenVal = lenBytes := himp (by omega)
                    have hpfx : pfx = BitVec.ofNat 8 (0xF7 + lenBytes.length) := by
                      rw [hlb_len, rlpPrefixLongListLenOfLen_def,
                          show 0xF7 + (pfx.toNat - 0xF7) = pfx.toNat from by omega,
                          ofNat8_toNat]
                    have hlonglen : 55 < (encode.encodeItems items).length := by
                      rw [← hib, hdl]; omega
                    show pfx :: rest0 = encode (.list items) ++ rest''
                    rw [encode_list_long items hlonglen, ← hib, hdl, htobe, hpfx,
                        hsp_rl, hsp_tk]
                    simp [List.append_assoc]
    · -- B (m+1)
      intro bs items rest h
      cases bs with
      | nil =>
        rw [show decodeItems (m + 1) [] = some ([], []) from rfl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hr⟩ := h; subst hi; subst hr; rfl
      | cons a as =>
        rw [decodeItems_succ_of_ne_nil m (a :: as) (by simp)] at h
        cases hda : decodeAux m (a :: as) with
        | none => rw [hda] at h; simp at h
        | some pair =>
          obtain ⟨item, r⟩ := pair
          rw [hda] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          cases hdi : decodeItems m r with
          | none => rw [hdi] at h; simp at h
          | some pair2 =>
            obtain ⟨items', r'⟩ := pair2
            rw [hdi] at h
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hi, hr⟩ := h; subst hi; subst hr
            have hA := ihA (a :: as) item r hda
            have hB := ihB r items' r' hdi
            show a :: as = encode.encodeItems (item :: items') ++ r'
            rw [show encode.encodeItems (item :: items')
                  = encode item ++ encode.encodeItems items' from rfl, hA, hB]
            simp [List.append_assoc]

/-- **Right inverse of `decode`.** Whatever `decode` accepts re-encodes to exactly
    the bytes it consumed — so the decoder accepts only canonical encodings. The
    ACL2 `rlp-encode-tree-of-rlp-parse-tree` analogue.
@isnad1 id=eq.1h3v.s5.44c8b96a532a from=translated src=- shape=07584f40 vocab=0103facc
-/
theorem decode_eq_some_imp_encode (bs : List Byte) (item : RLPItem) (rest : List Byte)
    (h : decode bs = some (item, rest)) : bs = encode item ++ rest := by
  rw [decode_eq_decodeAux_length] at h
  exact (decode_right_inverse_mutual (2 * bs.length)).1 bs item rest h

/-- **Decodability capstone.** Full decode is exactly the inverse of `encode`:
    `decodeFully bs = some item ↔ bs = encode item` (for items within the
    decoder's 8-byte length-field bound — astronomically permissive). Combines
    the left inverse (`decodeFully_encode`) and the right inverse.
@isnad1 id=iff.1h2v.s5.ddf09b5f7048 from=translated src=- shape=d26065e5 vocab=c892dbff
-/
theorem decodeFully_eq_encode (bs : List Byte) (item : RLPItem)
    (hbound : (encode item).length < 256 ^ 8) :
    decodeFully bs = some item ↔ bs = encode item := by
  constructor
  · intro hd
    have hdec := (decodeFully_eq_some_iff bs item).mp hd
    simpa using decode_eq_some_imp_encode bs item [] hdec
  · intro hb; subst hb; exact decodeFully_encode item hbound

/-! ### Self-delimiting encoding / prefix-unambiguity (ACL2 `rlp-encode-tree-unamb-prefix`)

An RLP encoding determines exactly where it ends, so no valid encoding is a
proper prefix of another. This follows directly from the two inverses: an
encoding followed by *any* trailing bytes decodes back to the item and the exact
trailer. -/

/-- Left inverse with an arbitrary trailer (generalizes `decode_encode`).
@isnad1 id=eq.1h2v.s6.a538c734dc70 from=translated src=- shape=e02b1f5e vocab=d4b90173
-/
theorem decode_encode_append (item : RLPItem) (rest : List Byte)
    (h : (encode item).length < 256 ^ 8) :
    decode (encode item ++ rest) = some (item, rest) := by
  rw [decode_eq_decodeAux_length]
  exact (decode_encode_mutual (2 * (encode item ++ rest).length)).1 item rest h
    (by rw [List.length_append]; omega)

/-- Encodings are left-cancellable against an arbitrary trailer: `encode` is
    self-delimiting, so the split point is unique.
@isnad1 id=and.3h4v.s6.b353bc3dde33 from=translated src=- shape=114988b9 vocab=8ac411c3
-/
theorem encode_append_cancel {i₁ i₂ : RLPItem} {r₁ r₂ : List Byte}
    (h₁ : (encode i₁).length < 256 ^ 8) (h₂ : (encode i₂).length < 256 ^ 8)
    (heq : encode i₁ ++ r₁ = encode i₂ ++ r₂) : i₁ = i₂ ∧ r₁ = r₂ := by
  have d₁ := decode_encode_append i₁ r₁ h₁
  have d₂ := decode_encode_append i₂ r₂ h₂
  rw [heq, d₂] at d₁
  simp only [Option.some.injEq, Prod.mk.injEq] at d₁
  exact ⟨d₁.1.symm, d₁.2.symm⟩

/-- **Prefix-unambiguity.** No valid encoding is a proper prefix of another: if
    `encode i₁` is a prefix of `encode i₂` then the items are equal.
@isnad1 id=eq.3h2v.s6.f01ee12c97f0 from=translated src=- shape=046ebfc3 vocab=7315e4d6
-/
theorem encode_prefix_unambiguous {i₁ i₂ : RLPItem}
    (h₁ : (encode i₁).length < 256 ^ 8) (h₂ : (encode i₂).length < 256 ^ 8)
    (hpre : encode i₁ <+: encode i₂) : i₁ = i₂ := by
  obtain ⟨t, ht⟩ := hpre
  exact (encode_append_cancel h₁ h₂ (r₁ := t) (r₂ := [])
    (by rw [List.append_nil]; exact ht)).1

/-! ## Round-trip correctness (concrete cases)

The round-trip property `decode (encode item) = some (item, [])` is verified
computationally via `decide` on representative test cases covering
all encoding forms:
- Single byte (value < 0x80)
- Short byte string (0-55 bytes)
- Short list (payload 0-55 bytes)
- Nested lists
- Canonical form rejection
-/

-- Single bytes

/-! ## Quasi-encoding rejection (ACL2 §4.2.1)

Coglio's ACL2 RLP development (arXiv:2009.13769) emphasizes that a correct
decoder must **reject** the five families of non-canonical "quasi-encodings" —
byte sequences that *could* be parsed but are not in the image of `encode`.
Accepting them (as some implementations did) breaks the right-inverse /
decodability property and the database-key consensus rule. Our decoder rejects
all five; the parametric rejections are named lemmas, with concrete `decide`
cross-checks below.

1. Redundant singleton `[0x81, x]` with `x < 0x80` — must use the single-byte
   form `[x]`. Rejected by `decode_canonical_rejection_single`.
2. Long byte-string with a leading-zero length field — rejected because
   `readLength` enforces no leading zeros
   (`readLength_none_of_takeBytes_leading_zero`).
3. Long byte-string form used for a `≤ 55` payload — rejected by the
   `lenVal ≤ 55` guard (`decodeAux_long_bytes_short_length_rejected`).
4. Long list with a leading-zero length field — as (2).
5. Long list form used for a `≤ 55` payload — as (3),
   `decodeAux_long_list_short_length_rejected`. -/

-- (1) redundant singleton (parametric form already proven)

end EvmAsm.EL.RLP
