/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.LeanPool.LeanPool.CircuitComplexity.AON.Defs
import Tengoku.LeanPool.LeanPool.CircuitComplexity.Internal.AON

/-! # Internal: Completeness of fan-in-2 AND/OR

This module proves `CompleteBasis Basis.andOr2` using the generic simulation
lemma `CompleteBasis.of_simulation`. The proof compiles any circuit over
`Basis.unboundedAON` into one over `Basis.andOr2` by decomposing each
unbounded fan-in gate into a chain of fan-in-2 gates.

## Strategy

Given a circuit `c : Circuit Basis.unboundedAON N M G`, we construct
`c' : Circuit Basis.andOr2 N M G'` with `c'.eval = c.eval`.

Each original gate with fan-in `k` is replaced by a chain of `chainLen k`
fan-in-2 gates:
- `k = 0`: one constant gate (dual-op trick: `OR(x₀, ¬x₀) = true`, etc.)
- `k = 1`: one passthrough gate (`op(x₀, x₀) = x₀`)
- `k ≥ 2`: `k - 1` gates chaining the inputs left-to-right

The new circuit's internal gates consist of chains for all original internal
gates followed by chains for all original output gates. The new output gates
are trivial passthroughs reading the last wire of each output chain.
-/

@[expose] public section

namespace CircuitComplexity

/-! ## AONOp extensions -/

/-- Dual operation: swaps AND ↔ OR. Used for constant-gate construction. -/
def AONOp.dual : AONOp → AONOp
  | .and => .or
  | .or => .and

/-- Identity element for fold: `true` for AND, `false` for OR. -/
def AONOp.identity : AONOp → Bool
  | .and => true
  | .or => false

/-- The binary operation corresponding to an AONOp. -/
def AONOp.binOp : AONOp → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)

/--
@isnad1 id=eq.0h3v.s4.32f0ad07ed27 from=translated src=- shape=7915fbf4 vocab=a859d5a6
-/
lemma AONOp.eval_eq_foldl (op : AONOp) (n : Nat) (v : BitString n) :
    op.eval n v = Fin.foldl n (fun acc i => op.binOp acc (v i)) op.identity := by
  cases op <;> rfl

/--
@isnad1 id=eq.0h2v.s3.5e33e14a0294 from=translated src=- shape=a6d2da5b vocab=fa2f9579
-/
lemma AONOp.identity_binOp (op : AONOp) (b : Bool) : op.binOp op.identity b = b := by
  cases op <;> simp [AONOp.binOp, AONOp.identity]

/--
@isnad1 id=eq.0h2v.s3.6702cd88106b from=translated src=- shape=7efc9de7 vocab=d403eb2c
-/
lemma AONOp.binOp_self (op : AONOp) (b : Bool) : op.binOp b b = b := by
  cases op <;> cases b <;> rfl

/--
@isnad1 id=eq.0h4v.s4.4c251f0a8eec from=translated src=- shape=615ceac8 vocab=d403eb2c
-/
lemma AONOp.binOp_assoc (op : AONOp) (a b c : Bool) :
    op.binOp (op.binOp a b) c = op.binOp a (op.binOp b c) := by
  cases op <;> simp [AONOp.binOp, Bool.and_assoc, Bool.or_assoc]

/-- The dual-op trick for constants: `OR(b, ¬b) = true`, `AND(b, ¬b) = false`.
@isnad1 id=eq.0h2v.s5.a118f20a6ca4 from=translated src=- shape=c7714c43 vocab=6cc5e762
-/
lemma AONOp.dual_const (op : AONOp) (b : Bool) :
    op.dual.eval 2 (fun i => (if i.val = 0 then false else true).xor b) =
    op.identity := by
  cases op <;> cases b <;>
    simp [AONOp.dual, AONOp.identity, AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- A passthrough evaluates to the input value.
@isnad1 id=eq.0h2v.s4.941e8474943a from=translated src=- shape=e1624e69 vocab=54e53c2d
-/
lemma AONOp.passthrough_eq (op : AONOp) (v : Bool) :
    op.eval 2 (fun _ => v) = v := by
  cases op <;> cases v <;>
    simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- `eval` on 0 inputs gives the identity.
@isnad1 id=eq.0h1v.s3.d72982f40cd0 from=translated src=- shape=600a10ec vocab=d1485e40
-/
lemma AONOp.eval_zero (op : AONOp) : op.eval 0 Fin.elim0 = op.identity := by
  cases op <;> simp [AONOp.eval, AONOp.identity, Fin.foldl_zero]

/-- `eval` on 1 input gives `identity op input`.
@isnad1 id=eq.0h2v.s5.90a9a654df23 from=translated src=- shape=d2f7352d vocab=d321219b
-/
lemma AONOp.eval_one (op : AONOp) (v : Fin 1 → Bool) :
    op.eval 1 v = op.binOp op.identity (v 0) := by
  cases op <;> simp [AONOp.eval, AONOp.binOp, AONOp.identity, Fin.foldl_succ_last, Fin.foldl_zero]

namespace CompileAON

/-! ## Chain length and prefix sums -/

/-- Number of fan-in-2 gates needed to simulate one gate with `k` inputs. -/
def chainLen (k : Nat) : Nat := if k ≤ 1 then 1 else k - 1

/--
@isnad1 id=eq.0h0v.s3.d3aceab84f4b from=translated src=- shape=3c26ae4f vocab=d4b9ade4
-/
@[simp] lemma chainLen_zero : chainLen 0 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.cd011ccca8a4 from=translated src=- shape=3c26ae4f vocab=d4b9ade4
-/
@[simp] lemma chainLen_one : chainLen 1 = 1 := rfl

/--
@isnad1 id=lt.0h1v.s3.f1b84e1a039a from=translated src=- shape=8a62b088 vocab=30de3bea
-/
lemma chainLen_pos (k : Nat) : 0 < chainLen k := by
  unfold chainLen; split <;> omega

/--
@isnad1 id=eq.1h1v.s4.8a866c770d25 from=translated src=- shape=e0c4802e vocab=66032e27
-/
lemma chainLen_of_ge_two {k : Nat} (hk : 2 ≤ k) : chainLen k = k - 1 := by
  rw [chainLen, ite_eq_right (by omega)]

/-- Prefix sum: `prefixSum f n = f 0 + f 1 + ⋯ + f (n-1)`. -/
def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

/--
@isnad1 id=eq.0h1v.s4.97984e9658f6 from=translated src=- shape=b298c1f9 vocab=edea51a7
-/
@[simp] lemma prefixSum_zero' (f : Nat → Nat) : prefixSum f 0 = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.1dc054b330a3 from=translated src=- shape=6d1f17e2 vocab=3c70b568
-/
lemma prefixSum_succ (f : Nat → Nat) (n : Nat) :
    prefixSum f (n + 1) = prefixSum f n + f n := rfl

/--
@isnad1 id=le.1h3v.s4.796502b2ce97 from=translated src=- shape=ce0fd851 vocab=8bb6331f
-/
lemma prefixSum_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    prefixSum f i ≤ prefixSum f j := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ ih => rw [prefixSum_succ]; omega

/-! ## Segment lookup -/

/-- Given a flat index into a segmented array, find the segment and position. -/
def segLookup (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    Nat × Nat :=
  match n with
  | 0 => absurd h (by simp)
  | n + 1 =>
    if hlt : idx < prefixSum f n then segLookup n f idx hlt
    else (n, idx - prefixSum f n)

/--
@isnad1 id=lt.1h3v.s4.c709547457fa from=translated src=- shape=eb5c0e33 vocab=cc52b52e
-/
lemma segLookup_fst_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).1 < n := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact Nat.lt_succ_of_lt (ih _)
    · exact Nat.lt_succ_of_le (Nat.le_refl n)

/--
@isnad1 id=lt.1h3v.s5.ad733c4829be from=translated src=- shape=3f42b9a5 vocab=26b52fb6
-/
lemma segLookup_snd_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).2 < f (segLookup n f idx h).1 := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · dsimp only
      rw [prefixSum_succ] at h; omega

/--
@isnad1 id=eq.1h3v.s5.163bd9d183ed from=translated src=- shape=9f8b5f2d vocab=fe560124
-/
lemma segLookup_sum (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    prefixSum f (segLookup n f idx h).1 + (segLookup n f idx h).2 = idx := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · dsimp only; omega

/-! ## Wire layout definitions -/

variable {N M G : Nat} [NeZero N] [NeZero M]

/-- Chain size function for internal gates (0-padded beyond G). -/
def iChainF (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  if h : i < G then chainLen (c.gates ⟨i, h⟩).fanIn else 0

/-- Chain size function for output gates (0-padded beyond M). -/
def oChainF (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  if h : j < M then chainLen (c.outputs ⟨j, h⟩).fanIn else 0

/-- Total number of compiled gates contributed by the internal gates. -/
def iTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (iChainF c) G
/-- Total number of compiled gates contributed by the output gates. -/
def oTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (oChainF c) M

/-- Total internal gates in the compiled circuit. -/
def G' (c : Circuit Basis.unboundedAON N M G) : Nat := iTotal c + oTotal c

/-- Offset of the chain for internal gate `i`. -/
def iOffset (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  prefixSum (iChainF c) i

/-- Offset of the chain for output gate `j`. -/
def oOffset (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  iTotal c + prefixSum (oChainF c) j

/--
@isnad1 id=eq.1h5v.s6.b8bd217cd296 from=translated src=- shape=f92d32d8 vocab=b587aa43
-/
lemma iChainF_eq (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iChainF c i = chainLen (c.gates ⟨i, hi⟩).fanIn := by simp [iChainF, hi]

/--
@isnad1 id=eq.1h5v.s6.0564e1ffc1bc from=translated src=- shape=ae5abc31 vocab=d3d764a3
-/
lemma oChainF_eq (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oChainF c j = chainLen (c.outputs ⟨j, hj⟩).fanIn := by simp [oChainF, hj]

/--
@isnad1 id=eq.1h5v.s6.1b9c95697890 from=translated src=- shape=46f447ca vocab=3faff6b3
-/
lemma iOffset_succ (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c (i + 1) = iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn := by
  simp [iOffset, prefixSum_succ, iChainF, hi]

/--
@isnad1 id=le.1h5v.s6.24b8d42d4cac from=translated src=- shape=948240ac vocab=487be480
-/
lemma iOffset_chain_le_iTotal (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn ≤ iTotal c := by
  rw [← iOffset_succ c hi]; exact prefixSum_mono _ (by omega)

/--
@isnad1 id=le.1h5v.s6.f97e80652777 from=translated src=- shape=00eff299 vocab=9a5e6173
-/
lemma oOffset_chain_le_G' (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn ≤ G' c := by
  suffices h : prefixSum (oChainF c) j + chainLen (c.outputs ⟨j, hj⟩).fanIn
      ≤ prefixSum (oChainF c) M by unfold oOffset G' iTotal oTotal at *; omega
  rw [← oChainF_eq c hj, ← prefixSum_succ]
  exact prefixSum_mono _ (by omega)

/-! ## Wire remapping -/

/-- Map an old wire index to its new position. Input wires are unchanged;
    internal gate `i` maps to the last gate of its chain. -/
def remapWire (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G)) :
    Fin (N + G' c) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else
    have hi : w.val - N < G := by omega
    have hle := iOffset_chain_le_iTotal c hi
    have hpos := chainLen_pos (c.gates ⟨w.val - N, hi⟩).fanIn
    ⟨N + iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, hi⟩).fanIn - 1, by
      unfold G'; omega⟩

/-- If `w < N + i` in the old circuit, `remapWire w < N + iOffset i` in the new.
@isnad1 id=lt.2h6v.s6.df77e35c67f2 from=translated src=- shape=a5de4476 vocab=fb78f5ee
-/
lemma remapWire_lt_of_lt (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    {i : Nat} (hi : i ≤ G) (hw : w.val < N + i) :
    (remapWire c w).val < N + iOffset c i := by
  unfold remapWire
  split
  · simp [iOffset]; omega
  · rename_i hNotLt
    push Not at hNotLt
    have hwN : w.val - N < i := by omega
    simp only []
    have key : iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, by omega⟩).fanIn
        ≤ iOffset c i := by
      rw [← iOffset_succ c (by omega : w.val - N < G)]
      exact prefixSum_mono _ (by omega)
    have := chainLen_pos (c.gates ⟨w.val - N, by omega⟩).fanIn
    omega

/-- `remapWire` maps to a wire that comes before any output chain.
@isnad1 id=lt.0h6v.s6.73a2d8f9486e from=translated src=- shape=796e9bc4 vocab=30151ce5
-/
lemma remapWire_lt_oOffset (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    (j : Nat) : (remapWire c w).val < N + oOffset c j := by
  have h := remapWire_lt_of_lt c w (Nat.le.refl) w.isLt
  have : iOffset c G = iTotal c := rfl
  unfold oOffset at *; omega

/-! ## Chain gate construction -/

/-- Helper: construct a function `Fin 2 → α` from two values. -/
def fin2 (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

/--
@isnad1 id=eq.0h3v.s4.8d15bda01052 from=translated src=- shape=b08fdde3 vocab=4124276b
-/
@[simp] lemma fin2_zero (a b : α) : fin2 a b 0 = a := rfl
/--
@isnad1 id=eq.0h3v.s4.3e3abe04eac1 from=translated src=- shape=9ac2d65f vocab=4124276b
-/
@[simp] lemma fin2_one (a b : α) : fin2 a b 1 = b := rfl

/-- Operation for the chain gate: dual-op for constants, same op otherwise. -/
def mkChainOp (op : AONOp) (k : Nat) : AONOp :=
  if k = 0 then op.dual else op

/-- Input wires for the j-th chain gate. -/
def mkChainInputs {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat)
    (hj : j < chainLen k) (hbase : base + chainLen k ≤ W) : Fin 2 → Fin W :=
  if hk0 : k = 0 then fun _ => ⟨0, hW⟩
  else if hk1 : k = 1 then fun _ => ri ⟨0, by omega⟩
  else if hj0 : j = 0 then fin2 (ri ⟨0, by omega⟩) (ri ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    have : j + 1 < k := by omega
    have : 1 ≤ j := by omega
    fin2 ⟨base + j - 1, by omega⟩ (ri ⟨j + 1, by omega⟩)

/-- Negation flags for the j-th chain gate. -/
def mkChainNeg (k : Nat) (rn : Fin k → Bool) (j : Nat)
    (hj : j < chainLen k) : Fin 2 → Bool :=
  if hk0 : k = 0 then fin2 false true
  else if hk1 : k = 1 then fun _ => rn ⟨0, by omega⟩
  else if _ : j = 0 then fin2 (rn ⟨0, by omega⟩) (rn ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    fin2 false (rn ⟨j + 1, by omega⟩)

/-- Build the `j`-th fan-in-2 gate in a chain for an original gate.
    Components are split out so projections reduce without unfolding `dite`. -/
def mkChainGate {W : Nat} (hW : 0 < W) (op : AONOp) (k : Nat)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W) : Gate Basis.andOr2 W :=
  { op := mkChainOp op k, fanIn := 2, arityOk := rfl,
    inputs := mkChainInputs hW k ri base j hj hbase,
    negated := mkChainNeg k rn j hj }

/-- All inputs of a chain are strictly before `base + j` in the wire ordering. -/
private lemma mkChainInputs_lt {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W)
    (hri_lt : ∀ i, (ri i).val < base) (hbase_pos : 0 < base)
    (i : Fin 2) :
    (mkChainInputs hW k ri base j hj hbase i).val < base + j := by
  simp only [mkChainInputs]
  split_ifs with hk0 hk1 hj0
  · dsimp only; omega
  · exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)
  · simp only [fin2]; split_ifs
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
  · simp only [fin2]; split_ifs
    · dsimp only; omega
    · exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)

/-! ## Compiled circuit -/

/-- Input wires for the compiled gate at flat index `idx`. -/
def compileGateInputs (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Fin (N + G' c) :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainInputs (by omega) (c.gates ⟨seg.1, hi⟩).fanIn
      (fun i => remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i))
      (N + iOffset c seg.1) seg.2 hj
      (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainInputs (by omega) (c.outputs ⟨seg.1, hj⟩).fanIn
      (fun i => remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i))
      (N + oOffset c seg.1) seg.2 hk
      (by have := oOffset_chain_le_G' c hj; omega)

/-- Operation for the compiled gate at flat index `idx`. -/
def compileGateOp (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) : AONOp :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    mkChainOp (c.gates ⟨seg.1, hi⟩).op (c.gates ⟨seg.1, hi⟩).fanIn
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    mkChainOp (c.outputs ⟨seg.1, hj⟩).op (c.outputs ⟨seg.1, hj⟩).fanIn

/-- Negation flags for the compiled gate at flat index `idx`. -/
def compileGateNeg (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Bool :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainNeg (c.gates ⟨seg.1, hi⟩).fanIn (c.gates ⟨seg.1, hi⟩).negated seg.2 hj
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainNeg (c.outputs ⟨seg.1, hj⟩).fanIn (c.outputs ⟨seg.1, hj⟩).negated seg.2 hk

/-- Gate function for the compiled circuit. Components are separated so
    projections reduce without going through `dite`. -/
def compileGates (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Gate Basis.andOr2 (N + G' c) :=
  { op := compileGateOp c idx, fanIn := 2, arityOk := rfl,
    inputs := compileGateInputs c idx,
    negated := compileGateNeg c idx }

/-- Output gates: passthroughs reading the last wire of each output chain. -/
def compileOutputs (c : Circuit Basis.unboundedAON N M G) (j : Fin M) :
    Gate Basis.andOr2 (N + G' c) :=
  let lastWire : Fin (N + G' c) :=
    ⟨N + oOffset c j.val + chainLen (c.outputs j).fanIn - 1, by
      have hle : oOffset c j.val + chainLen (c.outputs j).fanIn ≤ G' c :=
        oOffset_chain_le_G' c j.isLt
      have hpos := chainLen_pos (c.outputs j).fanIn
      omega⟩
  { op := .and, fanIn := 2, arityOk := rfl,
    inputs := fun _ => lastWire, negated := fun _ => false }

/-- The compiled circuit over `Basis.andOr2`. -/
def compileFn (c : Circuit Basis.unboundedAON N M G) : Circuit Basis.andOr2 N M (G' c) where
  gates := compileGates c
  outputs := compileOutputs c
  acyclic := by
    intro idx k
    change (compileGateInputs c idx k).val < N + idx.val
    have hN : 0 < N := by have := NeZero.ne N; omega
    unfold compileGateInputs
    split
    case isTrue h =>
      -- Internal region: idx.val < iTotal c
      set seg := segLookup G (iChainF c) idx.val h with hseg_def
      have hi : seg.1 < G := segLookup_fst_lt G _ _ h
      have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
        rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
      have hsum : prefixSum (iChainF c) seg.1 + seg.2 = idx.val :=
        segLookup_sum G _ _ h
      have hiOff : iOffset c seg.1 = prefixSum (iChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i)).val <
          N + iOffset c seg.1 :=
        fun i => remapWire_lt_of_lt c _ (by omega) (c.acyclic ⟨seg.1, hi⟩ i)
      have hbase_eq : N + iOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hiOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hj
        (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
        hri_lt (by omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)
    case isFalse h =>
      -- Output region: idx.val ≥ iTotal c
      have hoff : idx.val - iTotal c < oTotal c := by
        have := idx.isLt; unfold G' at this; omega
      set seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff with hseg_def
      have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
      have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
        rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
      have hsum : prefixSum (oChainF c) seg.1 + seg.2 = idx.val - iTotal c :=
        segLookup_sum M _ _ hoff
      have hoOff : oOffset c seg.1 = iTotal c + prefixSum (oChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i)).val <
          N + oOffset c seg.1 :=
        fun i => remapWire_lt_oOffset c _ seg.1
      have hbase_eq : N + oOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hoOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hk
        (by have := oOffset_chain_le_G' c hj; omega)
        hri_lt (by rw [hoOff]; omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)

/-! ## Eval equivalence -/

/-- `segLookup` inverts `prefixSum`: if `idx = prefixSum f i + j` and `j < f i`,
    then `segLookup` returns `(i, j)`.
@isnad1 id=eq.3h4v.s6.1d0dbe314280 from=translated src=- shape=46db347e vocab=477b4aaf
-/
lemma segLookup_of_prefixSum (n : Nat) (f : Nat → Nat) (i j : Nat)
    (hi : i < n) (hj : j < f i)
    (h : prefixSum f i + j < prefixSum f n) :
    segLookup n f (prefixSum f i + j) h = (i, j) := by
  induction n with
  | zero => omega
  | succ n ihn =>
    simp only [segLookup]
    by_cases hlt : prefixSum f i + j < prefixSum f n
    · have hin : i < n := by
        by_contra h'; have := prefixSum_mono f (show n ≤ i by omega); omega
      simp [hlt, ihn hin hlt]
    · have : i = n := by
        by_contra h'
        have := prefixSum_mono f (by omega : i + 1 ≤ n)
        rw [prefixSum_succ] at this; omega
      simp_all

/-- Partial fold: the result of folding `op.binOp` over the first `j` values. -/
private def partialFold (op : AONOp) (v : Fin k → Bool) (j : Nat) : Bool :=
  if h : j ≤ k then
    Fin.foldl j (fun acc i => op.binOp acc (v ⟨i.val, by omega⟩)) op.identity
  else op.eval k v

end CompileAON

end CircuitComplexity
