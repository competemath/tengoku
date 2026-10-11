import Tengoku.BtcVerified.BtcVerified.BitVM.BitCommitment.ValidOpening
import Tengoku.BtcVerified.BtcVerified.BitVM.BitCommitment.Collision
/-!
  # Equivocation and the binding spine

  Equivocation is one commitment with two valid openings to distinct bits. This
  module closes the proof spine: an equivocation yields a collision witness, so
  collision resistance forbids equivocation, and non-equivocation makes the
  commitments binding.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- Equivocation means one commitment has two valid openings whose revealed bits
are distinct. -/
structure Equivocation (hash : Bit → Nonce → Digest) where
  /-- The commitment that admits two distinct valid openings. -/
  commitment : Commitment Digest
  /-- One valid opening for the commitment. -/
  left : ValidOpening hash commitment
  /-- Another valid opening for the same commitment. -/
  right : ValidOpening hash commitment
  /-- Evidence that the two openings reveal different bits. -/
  bits_distinct : left.opening.bit ≠ right.opening.bit

/-- Extracts the concrete collision witness contained in an equivocation.

The two openings are distinct because they reveal different bits, and their
digests are equal because both verify against the same commitment. -/
def Equivocation.toCollision
    {hash : Bit → Nonce → Digest}
    (equivocation : Equivocation hash) :
    Collision hash :=
  let ⟨_commitment, left, right, bits_distinct⟩ := equivocation
  { left := left.opening
    right := right.opening
    distinct := openings_with_distinct_bits_are_distinct left.opening right.opening bits_distinct
    same_digest := by rw [left.valid, right.valid] }

/-- The collision witness extracted from an equivocation; see `Equivocation.toCollision`. -/
def Collision.ofEquivocation
    {hash : Bit → Nonce → Digest}
    (equivocation : Equivocation hash) :
    Collision hash :=
  equivocation.toCollision

/-- Any equivocation refutes collision resistance, because the equivocation can
be converted into a concrete collision.
@isnad1 id=not.0h4v.s4.bd4bd880b3ac from=translated src=- shape=4428af3d vocab=0c954b33
-/
theorem equivocation_refutes_collision_resistance
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    ¬ CollisionResistance hash := by
  intro resistance
  apply resistance
  exact equivocation.toCollision

/-- `NonEquivocation` says that the bundled commitment function admits no
equivocation witnesses. -/
def NonEquivocation (hash : Bit → Nonce → Digest) : Prop := Equivocation hash → False

/-- Collision resistance gives non-equivocation: an equivocation witness would
produce the collision witness that collision resistance rules out.
@isnad1 id=nonequiv.1h3v.s4.c941a626d2f4 from=translated src=- shape=1737cfdd vocab=5ce1c9df
-/
theorem CollisionResistance.nonEquivocation
    {hash : Bit → Nonce → Digest}
    (resistance : CollisionResistance hash) :
    NonEquivocation hash := by
  intro equivocation
  apply resistance
  exact equivocation.toCollision

/-- If equivocation is impossible, then two valid openings for the same commitment
must reveal the same bit.
@isnad1 id=binding.1h3v.s4.cd44499478c4 from=translated src=- shape=1737cfdd vocab=690d3c6a
-/
theorem NonEquivocation.binding
    {hash : Bit → Nonce → Digest}
    (hashForbidsEquivocation : NonEquivocation hash) :
    Binding hash := by
  intros commitment left right
  by_cases same_bits : left.opening.bit = right.opening.bit
  · exact same_bits
  · apply False.elim
    apply hashForbidsEquivocation
    constructor
    exact same_bits

/-- Collision resistance makes the induced commitments binding.

Collision resistance gives non-equivocation, and non-equivocation rules out
pairs of valid openings that reveal different bits.
@isnad1 id=binding.1h3v.s4.e66e67ac7380 from=translated src=- shape=1737cfdd vocab=14205163
-/
theorem CollisionResistance.binding
    {hash : Bit → Nonce → Digest}
    (resistance : CollisionResistance hash) :
    Binding hash :=
  resistance.nonEquivocation.binding

end BtcVerified.BitVM.BitCommitment
