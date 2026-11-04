import Tengoku.DeletionCodesLean.DeletionCode.TraceEditData
import Tengoku.DeletionCodesLean.DeletionCode.TraceSeparation
import Tengoku.Seed.Data.List.OfFn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms decode_encode` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms target_eq_source_of_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms recordIndex_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_finite_record` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms vector_edit_indices` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Chronological edit records use absolute matched-column anchors. A deletion
stores no source bit: its payload is (false,false). An insertion stores
(true,bit). The original source and the record reconstruct the actual target.
The finite-vector realization is suitable for counting records independently
of the random hash, including nonseparated alignments.
-/
namespace DeletionCode.AnchorRecords

open AlignmentTrace TraceEditData

abbrev Packet := ℕ × (Bool × Bool)

def payload : Column → Bool × Bool
  | .matched _ => (false, false)
  | .deletion _ => (false, false)
  | .insertion bit => (true, bit)

def encodeFrom (matchedBefore : ℕ) : Trace → List Packet
  | [] => []
  | .matched _ :: rest => encodeFrom (matchedBefore + 1) rest
  | .deletion _ :: rest => (matchedBefore, (false, false)) :: encodeFrom matchedBefore rest
  | .insertion bit :: rest => (matchedBefore, (true, bit)) :: encodeFrom matchedBefore rest

def encode (trace : Trace) : List Packet := encodeFrom 0 trace

/-- Copy the matched gap; then delete the next source letter or insert a bit.
The decoder is total even on malformed records, which are harmless overcounts.-/
def decodeFrom (matchedBefore : ℕ) (source : List Bool) : List Packet → List Bool
  | [] => source
  | (anchor, (side, bit)) :: rest =>
      if side then
        source.take (anchor - matchedBefore) ++
          bit :: decodeFrom anchor (source.drop (anchor - matchedBefore)) rest
      else
        source.take (anchor - matchedBefore) ++
          decodeFrom anchor (source.drop (anchor - matchedBefore + 1)) rest

def decode (source : List Bool) (packets : List Packet) : List Bool :=
  decodeFrom 0 source packets

/--
@isnad1 id=eq.0h2v.s4.cf72e676f7c2 from=translated src=- shape=9b5cd667 vocab=daa71221
-/
theorem encodeFrom_length (trace : Trace) (m : ℕ) :
    (encodeFrom m trace).length = trace.deletions + trace.insertions := by
  induction trace generalizing m with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [encodeFrom, Trace.deletions, Trace.insertions, ih] <;> omega

/--
@isnad1 id=eq.0h1v.s4.4db97aa06a40 from=translated src=- shape=1e99ff92 vocab=2f96a800
-/
theorem encode_length (trace : Trace) :
    (encode trace).length = trace.deletions + trace.insertions := encodeFrom_length trace 0

/--
@isnad1 id=and.1h3v.s5.058a8a5cd0e8 from=translated src=- shape=133cce91 vocab=864f374c
-/
theorem encodeFrom_anchor_bounds (trace : Trace) (m : ℕ) (p : Packet)
    (hp : p ∈ encodeFrom m trace) :
    m ≤ p.1 ∧ p.1 ≤ m + trace.matchedCount := by
  induction trace generalizing m with
  | nil => simp [encodeFrom] at hp
  | cons col rest ih =>
    cases col with
    | matched bit =>
      have h := ih (m + 1) hp
      simp only [Trace.matchedCount]
      omega
    | deletion bit =>
      simp only [encodeFrom, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [Trace.matchedCount]
      · exact ih m hp
    | insertion bit =>
      simp only [encodeFrom, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [Trace.matchedCount]
      · exact ih m hp

/--
@isnad1 id=le.1h2v.s4.18bc408e2430 from=translated src=- shape=582c8706 vocab=8f6776e3
-/
theorem encode_anchor_le (trace : Trace) (p : Packet) (hp : p ∈ encode trace) :
    p.1 ≤ trace.matchedCount := by
  simpa only [Nat.zero_add] using (encodeFrom_anchor_bounds trace 0 p hp).2

private theorem decodeFrom_matched (m : ℕ) (bit : Bool) (source : List Bool)
    (packets : List Packet) (hanchor : ∀ p ∈ packets, m + 1 ≤ p.1) :
    decodeFrom m (bit :: source) packets = bit :: decodeFrom (m + 1) source packets := by
  cases packets with
  | nil => rfl
  | cons packet rest =>
    obtain ⟨anchor, side, inserted⟩ := packet
    have ha : m + 1 ≤ anchor := hanchor _ (List.mem_cons_self ..)
    have hgap : anchor - m = (anchor - (m + 1)) + 1 := by omega
    cases side <;> simp [decodeFrom, hgap, Nat.add_assoc]

/-- The record decoder recovers the actual trace target from its source.
@isnad1 id=eq.0h2v.s4.2126cf743a9b from=translated src=- shape=6cc453b5 vocab=06679203
-/
theorem decodeFrom_encodeFrom (trace : Trace) (m : ℕ) :
    decodeFrom m trace.source (encodeFrom m trace) = trace.target := by
  induction trace generalizing m with
  | nil => rfl
  | cons col rest ih =>
    cases col with
    | matched bit =>
      change decodeFrom m (bit :: Trace.source rest) (encodeFrom (m + 1) rest) =
        bit :: Trace.target rest
      rw [decodeFrom_matched m bit (Trace.source rest) (encodeFrom (m + 1) rest)
        (fun p hp => (encodeFrom_anchor_bounds rest (m + 1) p hp).1), ih]
    | deletion bit =>
      simp [encodeFrom, decodeFrom, Trace.source, Trace.target, ih]
    | insertion bit =>
      simp [encodeFrom, decodeFrom, Trace.source, Trace.target, ih]

/--
@isnad1 id=eq.0h1v.s3.e0b7a0daf5a4 from=translated src=- shape=9e2d34f5 vocab=97595316
-/
theorem decode_encode (trace : Trace) : decode trace.source (encode trace) = trace.target :=
  decodeFrom_encodeFrom trace 0

/-- Zero deletions and insertions leave every source letter matched.
@isnad1 id=eq.2h1v.s4.c11854dc42ff from=translated src=- shape=b7e25c33 vocab=680d451c
-/
theorem target_eq_source_of_zero (trace : Trace)
    (hdel : trace.deletions = 0) (hins : trace.insertions = 0) :
    trace.target = trace.source := by
  have hlen : (encode trace).length = 0 := by rw [encode_length, hdel, hins]
  have he : encode trace = [] := List.length_eq_zero_iff.mp hlen
  simpa only [he, decode, decodeFrom] using (decode_encode trace).symm

/--
@isnad1 id=eq.0h3v.s5.25da5d4ec0a0 from=translated src=- shape=f3ffb9eb vocab=0100fb1d
-/
theorem encodeFrom_append (left right : Trace) (m : ℕ) :
    encodeFrom m (left ++ right) =
      encodeFrom m left ++ encodeFrom (m + left.matchedCount) right := by
  induction left generalizing m with
  | nil => simp [encodeFrom, Trace.matchedCount]
  | cons col rest ih =>
    cases col <;> simp [encodeFrom, Trace.matchedCount, ih,
      Nat.add_assoc, Nat.add_comm]

/-- A selected edit occurs after the packets of its exact trace prefix.
@isnad1 id=eq.0h2v.s7.e4da62a1a89f from=translated src=- shape=59a61275 vocab=aa610137
-/
theorem encode_split_edit (trace : Trace) (c : EditColumn trace) :
    encode trace = encode (trace.take c.val.val) ++
      (trace.matchedAnchor c.val.val, payload (column trace c)) ::
        encodeFrom (trace.matchedAnchor c.val.val) (trace.drop (c.val.val + 1)) := by
  have hs := congrArg (encodeFrom 0) (split_column trace c)
  rw [encodeFrom_append] at hs
  simp only [Nat.zero_add] at hs
  rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩
  · simpa only [encode, Trace.matchedAnchor, hc, encodeFrom, payload] using hs
  · simpa only [encode, Trace.matchedAnchor, hc, encodeFrom, payload] using hs

def recordRank (trace : Trace) (c : EditColumn trace) : ℕ :=
  (encode (trace.take c.val.val)).length

/--
@isnad1 id=lt.0h2v.s3.cf10e576cfd2 from=translated src=- shape=b3c91f49 vocab=048a2dd3
-/
theorem recordRank_lt (trace : Trace) (c : EditColumn trace) :
    recordRank trace c < (encode trace).length := by
  have h := congrArg List.length (encode_split_edit trace c)
  simp only [List.length_append, List.length_cons] at h
  unfold recordRank
  omega

def recordIndex (trace : Trace) (c : EditColumn trace) : Fin (encode trace).length :=
  ⟨recordRank trace c, recordRank_lt trace c⟩

/--
@isnad1 id=eq.0h2v.s6.6e1b2f9812a3 from=translated src=- shape=58562d21 vocab=36a0c3bc
-/
theorem packetAt_recordRank (trace : Trace) (c : EditColumn trace) :
    (encode trace)[recordRank trace c]? =
      some (trace.matchedAnchor c.val.val, payload (column trace c)) := by
  rw [encode_split_edit trace c]
  unfold recordRank
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/--
@isnad1 id=eq.0h2v.s5.ae094876133e from=translated src=- shape=cd77eb30 vocab=458425ae
-/
theorem get_recordIndex (trace : Trace) (c : EditColumn trace) :
    (encode trace).get (recordIndex trace c) =
      (trace.matchedAnchor c.val.val, payload (column trace c)) := by
  have h := packetAt_recordRank trace c
  rw [List.getElem?_eq_getElem (recordRank_lt trace c)] at h
  exact Option.some.inj h

/--
@isnad1 id=lt.1h3v.s5.ecb0dda04fbb from=translated src=- shape=90330bad vocab=9740f7ba
-/
theorem recordRank_strict (trace : Trace) (c d : EditColumn trace)
    (hcd : c.val.val < d.val.val) : recordRank trace c < recordRank trace d := by
  have hdel := TraceSeparation.deletions_take_mono trace
    (show c.val.val + 1 ≤ d.val.val by omega)
  have hins := TraceSeparation.insertions_take_mono trace
    (show c.val.val + 1 ≤ d.val.val by omega)
  have hstep : Trace.deletions (trace.take (c.val.val + 1)) +
      Trace.insertions (trace.take (c.val.val + 1)) =
        Trace.deletions (trace.take c.val.val) + Trace.insertions (trace.take c.val.val) + 1 := by
    rw [List.take_succ_eq_append_getElem c.val.isLt,
      Trace.deletions_append, Trace.insertions_append]
    change Trace.deletions (trace.take c.val.val) + Trace.deletions [column trace c] +
      (Trace.insertions (trace.take c.val.val) + Trace.insertions [column trace c]) = _
    rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩
    · simp only [hc, Trace.deletions, Trace.insertions] <;> omega
    · simp only [hc, Trace.deletions, Trace.insertions] <;> omega
  simp only [recordRank, encode_length]
  omega

/--
@isnad1 id=injectiv.0h1v.s3.33931bc389b9 from=translated src=- shape=24bc8ec9 vocab=38b48df4
-/
theorem recordIndex_injective (trace : Trace) : Function.Injective (recordIndex trace) := by
  intro c d heq
  have hv : recordRank trace c = recordRank trace d := congrArg Fin.val heq
  apply Subtype.ext
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := recordRank_strict trace c d hlt
    omega
  · have := recordRank_strict trace d c hgt
    omega

/-- With at least one deletion, every edit anchor is strictly below source length.
@isnad1 id=lt.2h2v.s5.73f76365f877 from=translated src=- shape=f715d39f vocab=6c2835f1
-/
theorem encode_anchor_lt_source (trace : Trace) (hd : 1 ≤ trace.deletions)
    (p : Packet) (hp : p ∈ encode trace) : p.1 < trace.source.length := by
  have ha := encode_anchor_le trace p hp
  have hn := trace.source_length
  omega

/--
@isnad1 id=ex.2h3v.s6.14fa962efd9c from=translated src=- shape=1747bb0d vocab=6b05e253
-/
theorem finite_record_of_bounds (packets : List Packet) (n r : ℕ)
    (hlen : packets.length = r) (hbound : ∀ p ∈ packets, p.1 < n) :
    ∃ anchors : Fin r → Fin n, ∃ data : Fin r → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = packets := by
  subst r
  let anchors : Fin packets.length → Fin n :=
    fun i => ⟨(packets.get i).1, hbound _ (List.get_mem packets i)⟩
  refine ⟨anchors, fun i => (packets.get i).2, ?_⟩
  change List.ofFn (packets.get) = packets
  exact List.ofFn_get packets

/-- Every positive balanced trace has a record in the finite product space
used in the counting proof. The packet list is equal to the actual encoding.
@isnad1 id=ex.4h3v.s7.d41f1eb5a072 from=translated src=- shape=baa18f91 vocab=fa0744ec
-/
theorem exists_finite_record (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d)
    (hins : trace.insertions = d) (hd : 1 ≤ d) :
    ∃ anchors : Fin (2 * d) → Fin n, ∃ data : Fin (2 * d) → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = encode trace := by
  apply finite_record_of_bounds
  · rw [encode_length, hdel, hins]
    omega
  · intro p hp
    rw [← hsource]
    exact encode_anchor_lt_source trace (by omega) p hp

/-- Any finite-vector presentation of the encoding contains distinct indices
for distinct actual edits, with precisely their matched-column anchors.
@isnad1 id=ex.1h5v.s6.371325204e4c from=translated src=- shape=4d9dda63 vocab=ca098a10
-/
theorem vector_edit_indices (trace : Trace) {n r : ℕ}
    (anchors : Fin r → Fin n) (data : Fin r → Bool × Bool)
    (heq : List.ofFn (fun i => ((anchors i).val, data i)) = encode trace) :
    ∃ e : EditColumn trace → Fin r, Function.Injective e ∧
      ∀ c, (anchors (e c)).val = trace.matchedAnchor c.val.val := by
  have hlen : (encode trace).length = r := by rw [← heq, List.length_ofFn]
  let e : EditColumn trace → Fin r := fun c => Fin.cast hlen (recordIndex trace c)
  refine ⟨e, ?_, ?_⟩
  · intro c d hcd
    apply recordIndex_injective trace
    apply Fin.ext
    have hv : (e c).val = (e d).val := congrArg (fun i : Fin r => i.val) hcd
    exact hv
  · intro c
    have hget := packetAt_recordRank trace c
    rw [← heq] at hget
    have hi : recordRank trace c < r := by
      rw [← hlen]
      exact recordRank_lt trace c
    rw [List.getElem?_ofFn, dite_eq_left hi] at hget
    exact congrArg Prod.fst (Option.some.inj hget)

end DeletionCode.AnchorRecords
