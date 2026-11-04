import Tengoku.DeletionCodesLean.DeletionCode.ConcreteFill
import Tengoku.DeletionCodesLean.DeletionCode.ConcreteStart
import Tengoku.Seed.Data.List.OfFn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms seed_lookup_finds_position` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fillFromBase_recovers_window` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fillFromBase_rejects_conflict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms checked_write_rejects_out_of_bounds` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms crossing_transfer_agrees_with_negative_word` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms crossing_start_records_transferred_seed` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Small executable regressions for the concrete decoder primitives.

All examples use kernel evaluation through `by decide`, not native_decide.
They check computation and rejection on specific inputs; they do not replace
the general correctness, realization, or bounded-recovery theorems.
-/

namespace DeletionCode.DecoderExamples

open Windows PartialWords

/-- The ten-bit word 0001011100, with an unused zero tail.-/
def sampleWord : Letters :=
  fun i => [false, false, false, true, false, true, true, true, false, false].getD i false

/-- The known seed 101 belongs at relative offset one of the window 01011.-/
def sampleSeed : Bits 3 := fun i => i.val != 1

def sampleMemory : Memory := putBits empty 1 sampleSeed

/--
@isnad1 id=eq.0h0v.s5.da3608ced8fe from=translated src=- shape=ae14dbb2 vocab=76d4a2d9
-/
theorem seed_lookup_finds_position :
    SeedLookup.lookup sampleWord 10 3 5 1 sampleSeed = some 2 := by decide

/--
@isnad1 id=eq.0h0v.s6.038147ae47fa from=translated src=- shape=195e7efa vocab=c5c986d9
-/
theorem seed_lookup_recovers_window :
    (SeedLookup.recoverWindow sampleWord 10 3 5 1 sampleSeed).map
      (fun bits => List.ofFn bits) = some [false, true, false, true, true] := by decide

/--
@isnad1 id=eq.0h0v.s6.f7e06c7b28c5 from=translated src=- shape=1f0326e1 vocab=31a63c44
-/
theorem fillFromBase_recovers_window :
    ((ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 5 0 1).bind
      (fun memory => (readBits memory 0 5).map (fun bits => List.ofFn bits))) =
      some [false, true, false, true, true] := by decide

/-- A conflicting bit outside the seed is detected when the whole window is written.
@isnad1 id=eq.0h0v.s5.5e7079f9b375 from=translated src=- shape=ec352855 vocab=e640ae54
-/
theorem fillFromBase_rejects_conflict :
    (ConcreteFill.fillFromBase sampleWord 10 3 5
      (putBits sampleMemory 0 (fun _ : Fin 1 => true)) 5 0 1).isNone = true := by decide

/--
@isnad1 id=eq.0h0v.s5.79559cb2df9d from=translated src=- shape=b90525b8 vocab=b6e6c0d2
-/
theorem checked_write_rejects_conflict :
    (writeBits (putBits empty 0 (fun _ : Fin 1 => false)) 5 0
      (fun _ : Fin 1 => true)).isNone = true := by decide

/--
@isnad1 id=eq.0h0v.s4.65dcdb3a1706 from=translated src=- shape=08cf11f4 vocab=de758dcd
-/
theorem checked_write_rejects_out_of_bounds :
    (writeBits empty 5 4 sampleSeed).isNone = true := by decide

/-- The same valid lookup must still reject a destination that is too short.
@isnad1 id=eq.0h0v.s5.fde3da5739b4 from=translated src=- shape=d13979ee vocab=cdfc6c6c
-/
theorem fillFromBase_rejects_out_of_bounds :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 4 0 1).isNone = true :=
  by decide

/--
@isnad1 id=eq.0h0v.s5.78e7273e48be from=translated src=- shape=d13979ee vocab=f580c226
-/
theorem fillFromBase_rejects_missing_seed :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 empty 5 0 1).isNone = true := by decide

/-- For k=1, L=6 and rho=1, the positive path is the longer word.
Transferring its seed at the edit deletes the known bit and uses one extension bit.-/
def crossingHeader : HeaderRecovery.Header := ⟨.insertion, 1, true⟩

def crossingLong : Letters := fun i => i == 5

/--
@isnad1 id=and.0h0v.s5.ff91e46b7b6f from=translated src=- shape=ad5ed9d3 vocab=dac91541
-/
theorem crossing_header_parameters :
    1 ≤ crossingHeader.rho ∧ crossingHeader.rho ≤ 1 + 1 ∧
      HeaderRecovery.windowLength 1 = 6 ∧
      crossingLong (HeaderRecovery.editOffset 1) = crossingHeader.bit := by decide

/--
@isnad1 id=other.0h0v.s6.1419a77e6e70 from=translated src=- shape=7bbf1687 vocab=6750a55e
-/
theorem crossing_transfer_uses_extension_bit :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    (result.1, List.ofFn result.2) = (5, [false]) := by decide

/--
@isnad1 id=other.0h0v.s6.b929ba99c6e6 from=translated src=- shape=2b1da123 vocab=437b3f0f
-/
theorem crossing_transfer_agrees_with_negative_word :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    List.ofFn result.2 = List.ofFn (fun i : Fin 1 =>
      HeaderRecovery.negativePath 1 crossingHeader crossingLong (result.1 + i.val)) :=
  by decide

/--
@isnad1 id=eq.0h0v.s6.41134b1545ce from=translated src=- shape=a5052b88 vocab=47c07fde
-/
theorem crossing_start_records_transferred_seed :
    ((ConcreteStart.startPositive 1 crossingHeader 5 (fun _ : Fin 1 => true) false empty).bind
      (fun memory => (readBits memory 5 1).map (fun bits => List.ofFn bits))) =
      some [false] := by decide

end DeletionCode.DecoderExamples
