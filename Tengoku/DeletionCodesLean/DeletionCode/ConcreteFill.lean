import Tengoku.DeletionCodesLean.DeletionCode.PartialWords
import Tengoku.DeletionCodesLean.DeletionCode.SeedLookup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fillFromBase_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms copyFromMemory_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms loadRoot_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fillFromBase_extends` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Executable letter-level fill operations. Base-word fills discover the window
position from stored seed bits. Supplier fills copy stored bits at a recorded
offset. The target words and occurrence witnesses are proof parameters only.
These primitives are used by the bounded decoder proof in ConcreteRecovery.
-/
namespace DeletionCode.ConcreteFill

open Windows PartialWords

/-- Fill a destination window by locating its known seed in the fixed word.-/
def fillFromBase (x : Letters) (n k L : ℕ) (s : Memory) (m start r : ℕ) :
    Option Memory :=
  (readBits s (start + r) k).bind fun seed =>
    (SeedLookup.recoverWindow x n k L r seed).bind fun bits =>
      writeBits s m start bits

/-- Copy a bounded block of actual stored supplier data into checked memory.-/
def copyFromMemory (source : Memory) (sourceLength sourceStart len : ℕ)
    (s : Memory) (m start : ℕ) : Option Memory :=
  if sourceStart + len ≤ sourceLength then
    (readBits source sourceStart len).bind fun bits => writeBits s m start bits
  else none

/-- Root records contain a position in x, so their whole negative path can be read.-/
def loadRoot (x : Letters) (n a len : ℕ) (s : Memory) (m : ℕ) : Option Memory :=
  if a + len ≤ n then writeBits s m 0 (fun i : Fin len => x (a + i.val))
  else none

def Recovered (s t : Memory) (p : Letters) (m start len : ℕ) : Prop :=
  Sound t p m ∧ Extends s t ∧
    readBits t start len = some (fun i : Fin len => p (start + i.val))

/-- A valid base occurrence is filled exactly, using only its stored seed.
@isnad1 id=ex.6h10v.s7.57783ad1dc24 from=translated src=- shape=f574875e vocab=2b277022
-/
theorem fillFromBase_correct (x p : Letters) (n k L : ℕ)
    (s : Memory) (m start r : ℕ) (seed : Bits k)
    (hx : KUnique x n k) (hs : Sound s p m)
    (hbound : start + L ≤ m) (hr : r + k ≤ L)
    (hread : readBits s (start + r) k = some seed)
    (hocc : ∃ a, a + L ≤ n ∧ Agree x a p start L) :
    ∃ t, fillFromBase x n k L s m start r = some t ∧
      Recovered s t p m start L := by
  obtain ⟨a, ha, hagree⟩ := hocc
  have hseed : PartialWords.Matches seed p (start + r) :=
    readBits_sound s p m (start + r) k hs (by omega) seed hread
  have hlookup := SeedLookup.recoverWindow_of_occurrence
    x p n k L r a start seed hx hr ha hagree hseed
  let bits : Bits L := fun i => p (start + i.val)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start L hs hbound bits (fun _ => rfl)
  refine ⟨t, ?_, hsound, hext, hknown⟩
  simp only [fillFromBase, hread, Option.bind_some, hlookup]
  exact ht

/-- Supplier copying preserves truth when the recorded blocks really agree.
@isnad1 id=ex.6h10v.s6.48dc87936cb7 from=translated src=- shape=2bb3b61b vocab=a8e38fd4
-/
theorem copyFromMemory_correct (source s : Memory) (q p : Letters)
    (sourceLength sourceStart len m start : ℕ) (bits : Bits len)
    (hsource : Sound source q sourceLength) (hs : Sound s p m)
    (hsourceBound : sourceStart + len ≤ sourceLength) (hbound : start + len ≤ m)
    (hread : readBits source sourceStart len = some bits)
    (hagree : Agree q sourceStart p start len) :
    ∃ t, copyFromMemory source sourceLength sourceStart len s m start = some t ∧
      Recovered s t p m start len := by
  have hbits : PartialWords.Matches bits p start := by
    intro i
    exact (readBits_sound source q sourceLength sourceStart len hsource
      hsourceBound bits hread i).trans (hagree i.val i.isLt)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start len hs hbound bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simp only [copyFromMemory, ite_eq_left hsourceBound, hread, Option.bind_some]
    exact ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

/--
@isnad1 id=ex.4h7v.s6.165cd70fa9cd from=translated src=- shape=355208ac vocab=d5c29348
-/
theorem loadRoot_correct (x p : Letters) (n a len : ℕ) (s : Memory) (m : ℕ)
    (hs : Sound s p m) (ha : a + len ≤ n) (hbound : len ≤ m)
    (hocc : Agree x a p 0 len) :
    ∃ t, loadRoot x n a len s m = some t ∧ Recovered s t p m 0 len := by
  let bits : Bits len := fun i => x (a + i.val)
  have hbits : PartialWords.Matches bits p 0 := fun i => hocc i.val i.isLt
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m 0 len hs (by omega) bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [loadRoot, ite_eq_left ha] using ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

/-- Even arbitrary base-fill inputs cannot overwrite an already recorded bit.
@isnad1 id=extends.1h9v.s5.f8e5206ead75 from=translated src=- shape=7d543ec2 vocab=a7ec1be5
-/
theorem fillFromBase_extends (x : Letters) (n k L : ℕ)
    (s t : Memory) (m start r : ℕ)
    (h : fillFromBase x n k L s m start r = some t) : Extends s t := by
  unfold fillFromBase at h
  cases hseed : readBits s (start + r) k with
  | none => simp [hseed] at h
  | some seed =>
    simp only [hseed, Option.bind_some] at h
    cases hbits : SeedLookup.recoverWindow x n k L r seed with
    | none => simp [hbits] at h
    | some bits =>
      simp only [hbits, Option.bind_some] at h
      exact writeBits_extends s t m start L bits h

end DeletionCode.ConcreteFill
