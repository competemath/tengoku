import Tengoku.DeletionCodesLean.DeletionCode.Windows

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rebuild_positive_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms negativeLength_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms negativeExtra_lt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rebuild_positive_preserves_agreement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rebuild_positive_from_known_negative` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shorten_seed_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lengthen_seed_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms transfer_positive_seed_correct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms transfer_positive_seed_in_bounds` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms transfer_positive_seed_valid` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms transferFinite_valid` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rebuildPositiveFinite_correct` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Concrete header reconstruction and deterministic transfer of known seed letters.

The transfer functions inspect only the header, the incoming seed and its offset,
and one recorded extension bit. Their correctness and finite output bounds are
proved against the actual words. No decoder or instruction trace is assumed.
-/

namespace DeletionCode.HeaderRecovery

open Windows

inductive Orientation where
  | deletion
  | insertion
  deriving DecidableEq

structure Header where
  orientation : Orientation
  rho : ℕ
  bit : Bool

def windowLength (k : ℕ) : ℕ := 3 * (k + 1)

def editOffset (k : ℕ) : ℕ := windowLength k - 1

def longLength (k : ℕ) (h : Header) : ℕ := 2 * windowLength k - h.rho

def shortLength (k : ℕ) (h : Header) : ℕ := longLength k h - 1

def negativePath (k : ℕ) (h : Header) (long : Letters) : Letters :=
  match h.orientation with
  | .deletion => long
  | .insertion => deleteAt long (editOffset k)

def positivePath (k : ℕ) (h : Header) (long : Letters) : Letters :=
  match h.orientation with
  | .deletion => deleteAt long (editOffset k)
  | .insertion => long

def negativeLength (k : ℕ) (h : Header) : ℕ :=
  match h.orientation with
  | .deletion => longLength k h
  | .insertion => shortLength k h

def positiveLength (k : ℕ) (h : Header) : ℕ :=
  match h.orientation with
  | .deletion => shortLength k h
  | .insertion => longLength k h

def negativeExtra (k : ℕ) (h : Header) : ℕ := negativeLength k h - windowLength k

/--
@isnad1 id=eq.2h2v.s5.982eaad36ce8 from=translated src=- shape=6da91c94 vocab=84a910c3
-/
theorem negativeLength_eq (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeLength k h = windowLength k + negativeExtra k h := by
  unfold negativeExtra
  cases ho : h.orientation <;>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] <;> omega

/--
@isnad1 id=lt.2h2v.s5.144ba80091cb from=translated src=- shape=6bca1119 vocab=4bbcb3a1
-/
theorem negativeExtra_lt (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeExtra k h < windowLength k := by
  unfold negativeExtra
  cases ho : h.orientation <;>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] <;> omega

/-- Reconstruct the positive path from the negative path and recorded header.-/
def rebuildPositive (k : ℕ) (h : Header) (negative : Letters) : Letters :=
  match h.orientation with
  | .deletion => deleteAt negative (editOffset k)
  | .insertion => insertAt negative (editOffset k) h.bit

/--
@isnad1 id=eq.1h3v.s4.318074a2a8d5 from=translated src=- shape=fc6f1ad0 vocab=4f65d3a2
-/
theorem rebuild_positive_correct (k : ℕ) (h : Header) (long : Letters)
    (hbit : long (editOffset k) = h.bit) :
    rebuildPositive k h (negativePath k h long) = positivePath k h long := by
  cases ho : h.orientation with
  | deletion => simp only [rebuildPositive, negativePath, positivePath, ho]
  | insertion =>
    simp only [rebuildPositive, negativePath, positivePath, ho]
    rw [← hbit]
    exact insert_delete long (editOffset k)

/-- Rebuilding depends only on the finite negative word, not its unused tail.
@isnad1 id=agree.3h4v.s6.cd9b1cb73c32 from=translated src=- shape=c08b4d40 vocab=0ac8d6e0
-/
theorem rebuild_positive_preserves_agreement (k : ℕ) (h : Header) (p q : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hknown : Agree p 0 q 0 (negativeLength k h)) :
    Agree (rebuildPositive k h p) 0 (rebuildPositive k h q) 0 (positiveLength k h) := by
  cases ho : h.orientation with
  | deletion =>
    simp only [negativeLength, ho, longLength, windowLength] at hknown
    simp only [rebuildPositive, positiveLength, ho, shortLength, longLength, windowLength]
    intro i hi
    simp only [Nat.zero_add, deleteAt]
    by_cases hleft : i < editOffset k
    · simp only [ite_eq_left hleft]
      simpa only [Nat.zero_add] using hknown i (by omega)
    · simp only [ite_eq_right hleft]
      simpa only [Nat.zero_add] using hknown (i + 1) (by omega)
  | insertion =>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] at hknown
    simp only [rebuildPositive, positiveLength, ho, longLength, windowLength]
    intro i hi
    simp only [Nat.zero_add, insertAt]
    by_cases hleft : i < editOffset k
    · simp only [ite_eq_left hleft]
      have hlt : i < 2 * (3 * (k + 1)) - h.rho - 1 := by
        dsimp [editOffset, windowLength] at hleft
        omega
      simpa only [Nat.zero_add] using hknown i hlt
    · simp only [ite_eq_right hleft]
      by_cases heq : i = editOffset k
      · simp only [ite_eq_left heq]
      · simp only [ite_eq_right heq]
        have hlt : i - 1 < 2 * (3 * (k + 1)) - h.rho - 1 := by
          dsimp [editOffset, windowLength] at hleft heq
          omega
        simpa only [Nat.zero_add] using hknown (i - 1) hlt

/-- Correct finite negative letters suffice to recover the entire positive word.
@isnad1 id=agree.4h4v.s6.55dcdfbe3e14 from=translated src=- shape=4d5323f1 vocab=2cae3f24
-/
theorem rebuild_positive_from_known_negative (k : ℕ) (h : Header)
    (long known : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : Agree known 0 (negativePath k h long) 0 (negativeLength k h)) :
    Agree (rebuildPositive k h known) 0 (positivePath k h long) 0 (positiveLength k h) := by
  rw [← rebuild_positive_correct k h long hbit]
  exact rebuild_positive_preserves_agreement k h known (negativePath k h long)
    hrho0 hrho1 hknown

/-- Only the first k letters of bits are used or certified.-/
structure Seed where
  offset : ℕ
  bits : Letters

/-- Transfer across a deletion, recording a right-extension bit if crossed.-/
def shortenSeed (ell k : ℕ) (seed : Seed) (extra : Bool) : Seed :=
  if seed.offset + k ≤ ell then seed
  else if ell < seed.offset then ⟨seed.offset - 1, seed.bits⟩
  else ⟨seed.offset, deletionSeed k (ell - seed.offset) extra seed.bits⟩

/-- Transfer across an insertion, whose bit is supplied by the header.-/
def lengthenSeed (ell k : ℕ) (seed : Seed) (bit : Bool) : Seed :=
  if seed.offset + k ≤ ell then seed
  else if ell ≤ seed.offset then ⟨seed.offset + 1, seed.bits⟩
  else ⟨seed.offset, insertionSeed (ell - seed.offset) bit seed.bits⟩

/--
@isnad1 id=agree.2h5v.s6.0d3b89d7365d from=translated src=- shape=8f844a6e vocab=464ea41b
-/
theorem shorten_seed_correct (p : Letters) (ell k : ℕ) (seed : Seed)
    (extra : Bool) (hseed : Agree p seed.offset seed.bits 0 k)
    (hextra : seed.offset ≤ ell → ell < seed.offset + k →
      extra = deleteAt p ell (seed.offset + k - 1)) :
    Agree (deleteAt p ell) (shortenSeed ell k seed extra).offset
      (shortenSeed ell k seed extra).bits 0 k := by
  unfold shortenSeed
  split_ifs with hbefore hafter
  · intro i hi
    exact (deletion_before p ell seed.offset k hbefore i hi).trans (hseed i hi)
  · intro i hi
    exact (deletion_after p ell seed.offset k hafter i hi).trans (hseed i hi)
  · have hs : seed.offset ≤ ell := by omega
    have he : ell < seed.offset + k := by omega
    intro i hi
    have hx := deletion_crossing p ell seed.offset k hs he i hi
    dsimp
    rw [Nat.zero_add]
    rw [hx]
    unfold deletionSeed
    split_ifs with hcut hlast
    · simpa only [Nat.zero_add] using hseed i hi
    · simpa only [Nat.zero_add] using hseed (i + 1) hlast
    · exact (hextra hs he).symm

/--
@isnad1 id=agree.1h5v.s5.cb32aa7ef217 from=translated src=- shape=6fd36aba vocab=412018c0
-/
theorem lengthen_seed_correct (p : Letters) (ell k : ℕ) (seed : Seed)
    (bit : Bool) (hseed : Agree p seed.offset seed.bits 0 k) :
    Agree (insertAt p ell bit) (lengthenSeed ell k seed bit).offset
      (lengthenSeed ell k seed bit).bits 0 k := by
  unfold lengthenSeed
  split_ifs with hbefore hafter
  · intro i hi
    exact (insertion_before p ell seed.offset k bit hbefore i hi).trans (hseed i hi)
  · intro i hi
    exact (insertion_after p ell seed.offset k bit hafter i hi).trans (hseed i hi)
  · have hs : seed.offset ≤ ell := by omega
    intro i hi
    have hx := insertion_crossing p ell seed.offset k bit hs i hi
    dsimp
    rw [Nat.zero_add]
    rw [hx]
    unfold insertionSeed
    split_ifs with hcut heq
    · simpa only [Nat.zero_add] using hseed i hi
    · rfl
    · simpa only [Nat.zero_add] using hseed (i - 1) (by omega)

/-- A positive seed is transferred to the negative path using recorded data only.-/
def transferPositiveSeed (k : ℕ) (h : Header) (seed : Seed) (extra : Bool) : Seed :=
  match h.orientation with
  | .deletion => lengthenSeed (editOffset k) k seed h.bit
  | .insertion => shortenSeed (editOffset k) k seed extra

/-- The extra bit is constrained only when a positive-to-negative deletion crosses it.-/
def ExtensionMatches (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool) : Prop :=
  h.orientation = .insertion → seed.offset ≤ editOffset k →
    editOffset k < seed.offset + k →
      extra = negativePath k h long (seed.offset + k - 1)

/--
@isnad1 id=agree.3h5v.s6.dcf81f32d34c from=translated src=- shape=bcf5f8de vocab=e87663ab
-/
theorem transfer_positive_seed_correct (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool)
    (hbit : long (editOffset k) = h.bit)
    (hseed : Agree (positivePath k h long) seed.offset seed.bits 0 k)
    (hextra : ExtensionMatches k h long seed extra) :
    Agree (negativePath k h long) (transferPositiveSeed k h seed extra).offset
      (transferPositiveSeed k h seed extra).bits 0 k := by
  cases ho : h.orientation with
  | deletion =>
    simp only [positivePath, ho] at hseed
    simp only [negativePath, transferPositiveSeed, ho]
    have hresult := lengthen_seed_correct (deleteAt long (editOffset k))
      (editOffset k) k seed h.bit hseed
    have hinv : insertAt (deleteAt long (editOffset k)) (editOffset k) h.bit = long := by
      rw [← hbit]
      exact insert_delete long (editOffset k)
    rw [hinv] at hresult
    exact hresult
  | insertion =>
    simp only [positivePath, ho] at hseed
    simp only [negativePath, transferPositiveSeed, ho]
    apply shorten_seed_correct long (editOffset k) k seed extra hseed
    simpa only [ExtensionMatches, ho, negativePath, true_implies] using hextra

/--
@isnad1 id=le.3h4v.s6.545d7a2778d8 from=translated src=- shape=6c57949e vocab=580a5eeb
-/
theorem transfer_positive_seed_in_bounds (k : ℕ) (h : Header)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbound : seed.offset + k ≤ positiveLength k h) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h := by
  cases ho : h.orientation with
  | deletion =>
    simp only [positiveLength, ho, shortLength, longLength, windowLength] at hbound
    by_cases hbefore : seed.offset + k ≤ editOffset k
    · simp only [transferPositiveSeed, ho, lengthenSeed, ite_eq_left hbefore,
        negativeLength, longLength, windowLength]
      omega
    · by_cases hafter : editOffset k ≤ seed.offset
      · simp only [transferPositiveSeed, ho, lengthenSeed, ite_eq_right hbefore,
          ite_eq_left hafter, negativeLength, longLength, windowLength]
        omega
      · simp only [transferPositiveSeed, ho, lengthenSeed, ite_eq_right hbefore,
          ite_eq_right hafter, negativeLength, longLength, windowLength]
        omega
  | insertion =>
    simp only [positiveLength, ho, longLength, windowLength] at hbound
    by_cases hbefore : seed.offset + k ≤ editOffset k
    · simp only [transferPositiveSeed, ho, shortenSeed, ite_eq_left hbefore,
        negativeLength, shortLength, longLength, windowLength]
      dsimp [editOffset, windowLength] at hbefore
      omega
    · by_cases hafter : editOffset k < seed.offset
      · simp only [transferPositiveSeed, ho, shortenSeed, ite_eq_right hbefore,
          ite_eq_left hafter, negativeLength, shortLength, longLength, windowLength]
        dsimp [editOffset, windowLength] at hafter
        omega
      · simp only [transferPositiveSeed, ho, shortenSeed, ite_eq_right hbefore,
          ite_eq_right hafter, negativeLength, shortLength, longLength, windowLength]
        dsimp [editOffset, windowLength] at hafter
        omega

/-- The combined letter and bounds guarantee needed for a concrete start instruction.
@isnad1 id=and.6h5v.s7.f514950645e6 from=translated src=- shape=583ec5db vocab=da6b8342
-/
theorem transfer_positive_seed_valid (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : seed.offset + k ≤ positiveLength k h)
    (hseed : Agree (positivePath k h long) seed.offset seed.bits 0 k)
    (hextra : ExtensionMatches k h long seed extra) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h ∧
      Agree (negativePath k h long) (transferPositiveSeed k h seed extra).offset
        (transferPositiveSeed k h seed extra).bits 0 k := by
  exact ⟨transfer_positive_seed_in_bounds k h seed extra hrho0 hrho1 hbound,
    transfer_positive_seed_correct k h long seed extra hbit hseed hextra⟩

abbrev Bits (n : ℕ) := Fin n → Bool

/-- Embed exactly n bits into a total letter function with a fixed unused tail.-/
def padBits {n : ℕ} (bits : Bits n) : Letters :=
  fun i => if hi : i < n then bits ⟨i, hi⟩ else false

/-- A decoder-facing seed transfer: its input and output each contain exactly k bits.-/
def transferFinite (k : ℕ) (h : Header) (offset : ℕ)
    (bits : Bits k) (extra : Bool) : ℕ × Bits k :=
  let output := transferPositiveSeed k h ⟨offset, padBits bits⟩ extra
  (output.offset, fun i => output.bits i.val)

/--
@isnad1 id=and.6h6v.s7.793de3e2cf61 from=translated src=- shape=6488c2ad vocab=dfa1e5ef
-/
theorem transferFinite_valid (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : Bits k) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k →
        extra = negativePath k h long (offset + k - 1)) :
    (transferFinite k h offset bits extra).1 + k ≤ negativeLength k h ∧
      ∀ i : Fin k,
        negativePath k h long ((transferFinite k h offset bits extra).1 + i.val) =
          (transferFinite k h offset bits extra).2 i := by
  have hseed' : Agree (positivePath k h long) offset (padBits bits) 0 k := by
    intro i hi
    simpa only [Nat.zero_add, padBits, dite_eq_left hi] using hseed ⟨i, hi⟩
  have hextra' : ExtensionMatches k h long ⟨offset, padBits bits⟩ extra := by
    exact hextra
  have hvalid := transfer_positive_seed_valid k h long ⟨offset, padBits bits⟩ extra
    hrho0 hrho1 hbit hbound hseed' hextra'
  refine ⟨hvalid.1, ?_⟩
  intro i
  simpa only [transferFinite, Nat.zero_add] using hvalid.2 i.val i.isLt

/-- Reconstruct exactly the finite positive word from exactly the finite negative word.-/
def rebuildPositiveFinite (k : ℕ) (h : Header)
    (negative : Bits (negativeLength k h)) : Bits (positiveLength k h) :=
  fun i => rebuildPositive k h (padBits negative) i.val

/--
@isnad1 id=eq.4h5v.s6.aabc977cc197 from=translated src=- shape=58007078 vocab=23af0549
-/
theorem rebuildPositiveFinite_correct (k : ℕ) (h : Header) (long : Letters)
    (negative : Bits (negativeLength k h))
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : ∀ i : Fin (negativeLength k h), negative i = negativePath k h long i.val) :
    ∀ i : Fin (positiveLength k h),
      rebuildPositiveFinite k h negative i = positivePath k h long i.val := by
  have hknown' : Agree (padBits negative) 0 (negativePath k h long) 0
      (negativeLength k h) := by
    intro i hi
    simpa only [Nat.zero_add, padBits, dite_eq_left hi] using hknown ⟨i, hi⟩
  have hcorrect := rebuild_positive_from_known_negative k h long (padBits negative)
    hrho0 hrho1 hbit hknown'
  intro i
  simpa only [rebuildPositiveFinite, Nat.zero_add] using hcorrect i.val i.isLt

end DeletionCode.HeaderRecovery
