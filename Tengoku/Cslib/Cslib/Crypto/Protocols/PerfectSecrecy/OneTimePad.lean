/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Tengoku.Cslib.Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import Tengoku.Seed.Data.FinEnum
import Tengoku.Cslib.Cslib.Probability.PMF
import Tengoku.Seed.Data.LawfulXor.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-Time Pad

The one-time pad (Vernam cipher) over `BitVec l`
([KatzLindell2020], Construction 2.9).

## Main definitions

- `Cslib.Crypto.Protocols.PerfectSecrecy.otp`: the one-time pad encryption scheme

## Main results

- `Cslib.Crypto.Protocols.PerfectSecrecy.otp_perfectlySecret`:
  the one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy

open Cslib.Probability.PMF

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are XOR ([KatzLindell2020], Construction 2.9).-/
noncomputable def otp (l : ℕ) :
    EncScheme (BitVec l) (BitVec l) (BitVec l) :=
  .ofPure (PMF.uniformOfFintype _) (· ^^^ ·) (· ^^^ ·) fun k m => by
    simp [xor_cancel_left]

/-- The ciphertext distribution of the OTP is uniform, regardless of the
message: masking with a uniform key is the permutation `Equiv.xor` of the
uniform distribution.
@isnad1 id=eq.0h2v.s4.78bf8af301cd from=translated src=- shape=69d13a90 vocab=72e98bd4
-/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    (otp l).ciphertextDist m = PMF.uniformOfFintype (BitVec l) := by
  have h : (fun k : BitVec l => PMF.pure (k ^^^ m)) = (PMF.pure ∘ ⇑(Equiv.xor m)) :=
    congrArg (PMF.pure ∘ ·) xor_right_eq
  change (PMF.uniformOfFintype (BitVec l)).bind (fun k => PMF.pure (k ^^^ m)) = _
  rw [h, PMF.bind_pure_comp, uniformOfFintype_map_equiv]

/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10).
@isnad1 id=perfectl.0h1v.s3.0b99600e4ce5 from=translated src=- shape=b7ea40b9 vocab=6318e7c1
-/
theorem otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ =>
    (otp_ciphertextDist_eq_uniform l m₀).trans (otp_ciphertextDist_eq_uniform l m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
