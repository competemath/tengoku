import Tengoku.DeletionCodesLean.DeletionCode.Windows
import Tengoku.Seed.Data.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms readBits_eq_some_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms readBits_sound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms writeBits_extends` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms writeBits_correct` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Executable partial-word storage for the concrete recovery decoder.
Reads require every requested bit to be known. Writes check the finite word
bound and reject disagreements with previously known bits. Neither operation
receives the unknown target word; it appears only in their correctness proofs.
-/
namespace DeletionCode.PartialWords

open Windows

abbrev Memory := ℕ → Option Bool
abbrev Bits (len : ℕ) := Fin len → Bool

def empty : Memory := fun _ => none

def Sound (s : Memory) (p : Letters) (m : ℕ) : Prop :=
  ∀ j, j < m → ∀ b, s j = some b → b = p j

def Extends (s t : Memory) : Prop :=
  ∀ j b, s j = some b → t j = some b

def Matches {len : ℕ} (bits : Bits len) (p : Letters) (start : ℕ) : Prop :=
  ∀ i, bits i = p (start + i.val)

/-- Read finite data without a choice oracle or access to the target word.-/
def readBits (s : Memory) (start len : ℕ) : Option (Bits len) :=
  if ∀ i : Fin len, s (start + i.val) = some ((s (start + i.val)).getD false)
  then some (fun i => (s (start + i.val)).getD false)
  else none

def Compatible (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Prop :=
  ∀ i, s (start + i.val) = none ∨ s (start + i.val) = some (bits i)

instance (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) :
    Decidable (Compatible s start bits) := by
  unfold Compatible
  infer_instance

def putBits (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Memory :=
  fun j => if h : start ≤ j ∧ j < start + len
    then some (bits ⟨j - start, by omega⟩)
    else s j

/-- Checked write: reject out-of-bounds blocks and inconsistent known letters.-/
def writeBits (s : Memory) (m start : ℕ) {len : ℕ} (bits : Bits len) : Option Memory :=
  if start + len ≤ m ∧ Compatible s start bits
  then some (putBits s start bits)
  else none

/--
@isnad1 id=sound.0h2v.s3.10adfcd101e3 from=translated src=- shape=558eb298 vocab=b664337c
-/
theorem empty_sound (p : Letters) (m : ℕ) : Sound empty p m := by
  intro j hj b hb
  simp [empty] at hb

/--
@isnad1 id=iff.0h4v.s5.a7b3f6f4c89e from=translated src=- shape=7662f69b vocab=f316cc35
-/
theorem readBits_eq_some_iff (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by
  unfold readBits
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro i
      rw [← heq']
      exact h i
    · intro hb
      congr 1
      funext i
      simp [hb i]
  · rename_i h
    constructor
    · simp
    · intro hb
      apply False.elim
      apply h
      intro i
      simp [hb i]

/--
@isnad1 id=matches.3h6v.s5.cbdc67557cf1 from=translated src=- shape=8eace3e9 vocab=35f73f5c
-/
theorem readBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hread : readBits s start len = some bits) :
    Matches bits p start := by
  intro i
  exact hs (start + i.val) (by have := i.isLt; omega) (bits i)
    ((readBits_eq_some_iff s start len bits).mp hread i)

/--
@isnad1 id=compatib.3h6v.s5.9a4c2cba5c18 from=translated src=- shape=301616a8 vocab=6406d964
-/
theorem compatible_of_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    Compatible s start bits := by
  intro i
  cases h : s (start + i.val) with
  | none => exact Or.inl rfl
  | some b =>
    have hb := hs (start + i.val) (by have := i.isLt; omega) b h
    exact Or.inr (congrArg some (hb.trans (hbits i).symm))

/--
@isnad1 id=eq.0h5v.s5.dca6bcf8bf9e from=translated src=- shape=ef3ca566 vocab=1c03ce2e
-/
theorem putBits_at (s : Memory) (start len : ℕ) (bits : Bits len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by
  simp [putBits, i.isLt]

/--
@isnad1 id=extends.1h4v.s4.1ee142440c6b from=translated src=- shape=b666814d vocab=712ea4a1
-/
theorem putBits_extends (s : Memory) (start len : ℕ) (bits : Bits len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by
  intro j b hb
  unfold putBits
  split
  · rename_i h
    let i : Fin len := ⟨j - start, by omega⟩
    have hi : start + i.val = j := by dsimp [i]; omega
    have hc' := hc i
    rw [hi, hb] at hc'
    rcases hc' with hn | heq
    · contradiction
    · simpa [i] using heq.symm
  · exact hb

/--
@isnad1 id=sound.2h6v.s5.a5d8e6f8f2d8 from=translated src=- shape=8b29f17c vocab=1be809d2
-/
theorem putBits_sound (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by
  intro j hj b hb
  unfold putBits at hb
  split at hb
  · rename_i h
    have heq := Option.some.inj hb
    have hbit := hbits ⟨j - start, by omega⟩
    have hidx : start + (j - start) = j := by omega
    simpa [hidx, heq] using hbit
  · exact hs j hj b hb

/--
@isnad1 id=eq.0h4v.s4.b0dd4247da45 from=translated src=- shape=8530e330 vocab=e0f5337d
-/
theorem readBits_putBits (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits (putBits s start bits) start len = some bits := by
  apply (readBits_eq_some_iff _ _ _ _).mpr
  exact putBits_at s start len bits

/--
@isnad1 id=eq.3h6v.s5.d3d424ded807 from=translated src=- shape=07546f8f vocab=2f0b024f
-/
theorem writeBits_success (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by
  simp [writeBits, hbound, compatible_of_sound s p m start len hs hbound bits hbits]

/-- Every successful checked write preserves all previously known bits.
@isnad1 id=extends.1h6v.s4.22c0d3f31a58 from=translated src=- shape=a7d4a04b vocab=09dda26a
-/
theorem writeBits_extends (s t : Memory) (m start len : ℕ) (bits : Bits len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by
  unfold writeBits at hwrite
  split at hwrite
  · rename_i h
    cases Option.some.inj hwrite
    exact putBits_extends s start len bits h.2
  · contradiction

/-- Correct data written to correct memory remains correct and can be read back.
@isnad1 id=ex.3h6v.s6.3f80ad276786 from=translated src=- shape=417c11e8 vocab=960c1d1c
-/
theorem writeBits_correct (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by
  refine ⟨putBits s start bits,
    writeBits_success s p m start len hs hbound bits hbits,
    putBits_sound s p m start len hs bits hbits, ?_, readBits_putBits s start len bits⟩
  exact putBits_extends s start len bits
    (compatible_of_sound s p m start len hs hbound bits hbits)

end DeletionCode.PartialWords
