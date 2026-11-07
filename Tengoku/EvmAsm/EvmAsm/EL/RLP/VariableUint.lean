/-
  EvmAsm.EL.RLP.VariableUint

  The unbounded, canonical scalar surface needed by the execution-specs
  ``Uint`` fields.  This is deliberately a pure representation only: no
  emitted routine is routed through it in this step.

  An `RlpUint` stores the prefix-stripped content bytes of one RLP scalar and
  the canonicality fact that `_deserialize_to_uint` requires.  The content is
  a list rather than a fixed 32-byte word, so its value is not silently
  truncated when it is wider than the EVM word used by the existing guest.
  The optional `toU256?` projection is the explicit compatibility boundary for
  callers that have separately established a 32-byte width.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Properties
public import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL.RLP

/-! ## Canonical variable-width scalar content -/

/-- Canonicality of prefix-stripped RLP scalar content.

    The empty content is the canonical encoding of zero.  A nonempty scalar
    must have a nonzero most-significant byte.  RLP's singleton-prefix rule is
    checked by the surrounding RLP item decoder; this predicate is the
    `_deserialize_to_uint` check on the decoded content itself.-/
def isCanonicalUintContent (content : List Byte) : Prop :=
  content.headD 1 ≠ 0

/-- A decoded RLP scalar with arbitrary-width, canonical content.

    There is intentionally no `content.length ≤ 32` field here.  The pinned
    execution-specs `Uint` type is unbounded; width checks belong only to an
    explicit projection such as `toU256?`.-/
structure RlpUint where
  content : List Byte
  canonical : isCanonicalUintContent content

namespace RlpUint

/-- The arbitrary-precision value represented by the scalar content.-/
def value (u : RlpUint) : Nat := Nat.fromBytesBE u.content

/-- The number of bytes in the variable-width representation.-/
def width (u : RlpUint) : Nat := u.content.length

/-- Whether this scalar can be represented by the existing 256-bit word.-/
def fitsU256 (u : RlpUint) : Prop := u.width ≤ 32

/-- Construct a validated scalar from already-decoded content.-/
def ofContent? (content : List Byte) : Option RlpUint :=
  if h : content.headD 1 ≠ 0 then
    some ⟨content, h⟩
  else
    none

/-- A canonical scalar's content is recovered by re-encoding its value.
@isnad1 id=eq.0h1v.s3.889206bd020b from=translated src=- shape=d403cf25 vocab=1257dc4b
-/
theorem content_eq_toBytesBE (u : RlpUint) :
    Nat.toBytesBE u.value = u.content := by
  exact Nat.toBytesBE_fromBytesBE_of_canonical u.content u.canonical

/-- Constructing from a natural uses its minimal big-endian representation.-/
def ofNat (n : Nat) : RlpUint :=
  ⟨Nat.toBytesBE n, by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.toBytesBE_zero]
      simp [isCanonicalUintContent]
    · obtain ⟨b, tl, hbytes, hb⟩ := Nat.toBytesBE_eq_cons_of_pos n hn
      rw [hbytes]
      simpa [isCanonicalUintContent] using hb⟩

/--
@isnad1 id=eq.0h1v.s3.0db2dd782a80 from=translated src=- shape=d403cf25 vocab=7aed6db2
-/
@[simp] theorem ofNat_content (n : Nat) : (ofNat n).content = Nat.toBytesBE n :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.5f62bb814f09 from=translated src=- shape=47dcad53 vocab=04ab6421
-/
@[simp] theorem ofNat_value (n : Nat) : (ofNat n).value = n := by
  simp [ofNat, value, Nat.fromBytesBE_toBytesBE]

/-- A `k`-byte content value is strictly below `256^k`.
@isnad1 id=lt.0h1v.s4.17f3544eb943 from=translated src=- shape=9fc36aa0 vocab=5ecc9b34
-/
theorem value_lt_pow_width (u : RlpUint) :
    u.value < 256 ^ u.width := by
  exact Nat.fromBytesBE_lt u.content

/-- A scalar with at most 32 content bytes is strictly below `2^256`.
@isnad1 id=lt.1h1v.s5.efb3e3b54fd9 from=translated src=- shape=fdf25a47 vocab=98c77507
-/
theorem value_lt_u256_modulus (u : RlpUint) (h : u.fitsU256) :
    u.value < 2 ^ 256 := by
  change Nat.fromBytesBE u.content < 2 ^ 256
  have hlen : u.content.length ≤ 32 := by
    simpa [fitsU256, width] using h
  calc
    Nat.fromBytesBE u.content < 256 ^ u.content.length :=
      Nat.fromBytesBE_lt u.content
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) hlen
    _ = 2 ^ 256 := by norm_num

/-! ## Explicit compatibility projection -/

/-- The existing fixed-width word projection, guarded by an explicit width
    proof.  `BitVec.ofNat` is safe here because `value_lt_u256_modulus` proves
    that no truncation occurs.-/
def toU256 (u : RlpUint) (h : u.fitsU256) : BitVec 256 :=
  if h' : u.width ≤ 32 then
    BitVec.ofNat 256 u.value
  else
    False.elim (h' (by simpa [fitsU256] using h))

/--
@isnad1 id=eq.1h1v.s4.93765e6d5d1a from=translated src=- shape=2faba509 vocab=bbd43b6b
-/
@[simp] theorem toU256_toNat (u : RlpUint) (h : u.fitsU256) :
    (u.toU256 h).toNat = u.value := by
  have hlen : u.width ≤ 32 := by simpa [fitsU256] using h
  rw [toU256, dite_eq_left hlen, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (value_lt_u256_modulus u h)

/-- An option-valued projection for callers that have not proved the width at
    the call site.  The `none` case is a representation failure, not a
    variable-width decode failure.-/
def toU256? (u : RlpUint) : Option (BitVec 256) :=
  if h : u.width ≤ 32 then some (u.toU256 h) else none

/-! ## Concrete checks for the boundary and canonicality -/

end RlpUint

end EvmAsm.EL.RLP
