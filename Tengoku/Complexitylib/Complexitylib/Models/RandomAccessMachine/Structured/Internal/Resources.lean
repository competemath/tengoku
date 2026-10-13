/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import Tengoku

/-!
# Resource-proof infrastructure for structured RAM programs

This internal module packages the generic proof obligations that arise when a
structured program is verified against the concrete logarithmic-cost RAM:
finite register envelopes, their induced `finsum` space bounds, and compositional
source executions carrying exact steps with upper bounds on time and space.
-/

@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Internal

/-- A register store fits an index/value envelope. Every nonzero register lies
below `indexBound`, and every stored value is at most `valueBound`. -/
structure StoreEnvelope (indexBound valueBound : ℕ) (store : Store) : Prop where
  index_lt : ∀ index, store index ≠ 0 → index < indexBound
  value_le : ∀ index, store index ≤ valueBound

/-- Enlarging either side of a store envelope preserves the bound.
@isnad1 id=storeenv.3h5v.s4.fea150ad69d9 from=translated src=- shape=7533c8b1 vocab=5227c82a
-/
theorem StoreEnvelope.mono {indexBound valueBound largerIndex largerValue : ℕ}
    {store : Store} (hstore : StoreEnvelope indexBound valueBound store)
    (hindex : indexBound ≤ largerIndex) (hvalue : valueBound ≤ largerValue) :
    StoreEnvelope largerIndex largerValue store where
  index_lt index hnonzero := lt_of_lt_of_le (hstore.index_lt index hnonzero) hindex
  value_le index := le_trans (hstore.value_le index) hvalue

/-- A reserved-prefix bit input fits any envelope containing its length register,
input interval, list length, and Boolean values.
@isnad1 id=storeenv.4h5v.s5.81b5e9acf71e from=translated src=- shape=928ec2fc vocab=570165c3
-/
theorem Input.bitStoreEnvelope {lengthReg inputBase indexBound valueBound : ℕ}
    (bits : List Bool) (hlengthReg : lengthReg < indexBound)
    (hinputEnd : inputBase + bits.length ≤ indexBound)
    (hlength : bits.length ≤ valueBound) (hone : 1 ≤ valueBound) :
    StoreEnvelope indexBound valueBound (Input.bitStore lengthReg inputBase bits) := by
  constructor
  · intro index hnonzero
    simp only [Input.bitStore] at hnonzero
    split at hnonzero
    · subst index
      exact hlengthReg
    · rename_i hlengthRegNe
      split at hnonzero
      · rename_i hbase
        split at hnonzero
        · rename_i bit hbit
          have hoffset : index - inputBase < bits.length :=
            List.getElem?_eq_some_iff.mp hbit |>.1
          have hrecover : inputBase + (index - inputBase) = index :=
            Nat.add_sub_of_le hbase
          omega
        · simp at hnonzero
      · simp at hnonzero
  · intro index
    by_cases hlengthRegEq : index = lengthReg
    · simpa [Input.bitStore, hlengthRegEq] using hlength
    · rw [Input.bitStore, ite_eq_right hlengthRegEq]
      by_cases hbase : inputBase ≤ index
      · rw [ite_eq_left hbase]
        cases hlookup : bits[index - inputBase]? with
        | none => simp
        | some bit =>
            cases bit
            · simp [Input.bitValue]
            · simpa [Input.bitValue] using hone
      · simp [hbase]

/-- Logarithmic space occupied by the largest store admitted by an envelope. -/
def envelopeSpace (indexBound valueBound : ℕ) : ℕ :=
  indexBound * (bitlen indexBound + bitlen valueBound)

/-- A store envelope bounds the real finite-sum source-space measure.
@isnad1 id=le.1h3v.s4.1769b3bc32c7 from=translated src=- shape=a98bf590 vocab=2b3a20db
-/
theorem StoreEnvelope.space_le {indexBound valueBound : ℕ} {store : Store}
    (hstore : StoreEnvelope indexBound valueBound store) :
    store.space ≤ envelopeSpace indexBound valueBound := by
  rw [Store.space, envelopeSpace,
    finsum_eq_finsetSum_of_support_subset (s := Finset.range indexBound)]
  · calc
      ∑ index ∈ Finset.range indexBound,
          (if store index = 0 then 0 else bitlen index + bitlen (store index))
          ≤ ∑ _index ∈ Finset.range indexBound,
              (bitlen indexBound + bitlen valueBound) := by
            apply Finset.sum_le_sum
            intro index hindex
            split_ifs with hzero
            · simp
            · have hindexLe : index ≤ indexBound := by
                exact Nat.le_of_lt (Finset.mem_range.mp hindex)
              have hindexSize := Nat.size_le_size hindexLe
              have hvalueSize := Nat.size_le_size (hstore.value_le index)
              simpa [bitlen] using Nat.add_le_add hindexSize hvalueSize
      _ = indexBound * (bitlen indexBound + bitlen valueBound) := by simp
  · intro index hsupport
    by_contra hindex
    have hstoreZero : store index = 0 := by
      by_contra hnonzero
      exact hindex (Finset.mem_range.mpr (hstore.index_lt index hnonzero))
    simp [hstoreZero] at hsupport

/-- Updating an in-envelope register with an in-envelope value preserves the
store envelope.
@isnad1 id=storeenv.3h5v.s5.fd4d8cbe8193 from=translated src=- shape=b1590f70 vocab=7cdc28b3
-/
theorem StoreEnvelope.update {indexBound valueBound index value : ℕ}
    {store : Store} (hstore : StoreEnvelope indexBound valueBound store)
    (hindex : index < indexBound) (hvalue : value ≤ valueBound) :
    StoreEnvelope indexBound valueBound (Function.update store index value) := by
  constructor
  · intro candidate hnonzero
    by_cases heq : candidate = index
    · simpa [heq] using hindex
    · exact hstore.index_lt candidate
        (by simpa [Function.update_of_ne heq] using hnonzero)
  · intro candidate
    by_cases heq : candidate = index
    · subst candidate
      simpa using hvalue
    · simpa [Function.update_of_ne heq] using hstore.value_le candidate

namespace Basic

/-- Register written by a basic instruction in a given store. The store argument
is relevant only for indirect writes. -/
@[simp]
def writeIndex : Structured.Basic → Store → ℕ
  | .imm dst _, _ | .add dst _ _, _ | .sub dst _ _, _ | .mul dst _ _, _ |
      .load dst _, _ => dst
  | .store address _, store => store address

/-- Value written by a basic instruction in a given store. -/
@[simp]
def writeValue : Structured.Basic → Store → ℕ
  | .imm _ value, _ => value
  | .add _ left right, store => store left + store right
  | .sub _ left right, store => store left - store right
  | .mul _ left right, store => store left * store right
  | .load _ address, store => store (store address)
  | .store _ src, store => store src

/-- Basic execution is a single functional update, uniformly across direct and
indirect instructions.
@isnad1 id=eq.0h2v.s4.7cb2d575755e from=translated src=- shape=f75e448f vocab=0c462edd
-/
theorem exec_eq_update (op : Structured.Basic) (store : Store) :
    op.exec store = Function.update store (writeIndex op store) (writeValue op store) := by
  cases op <;> rfl

/-- A concrete straight-line execution stays inside one store envelope at its
initial store and after every instruction. Unlike a uniform preservation
condition, this certificate can use semantic facts about the actual store at
each program point. -/
def EnvelopeChain (indexBound valueBound : ℕ) : List Structured.Basic → Store → Prop
  | [], store => StoreEnvelope indexBound valueBound store
  | op :: rest, store =>
      StoreEnvelope indexBound valueBound store ∧
        EnvelopeChain indexBound valueBound rest (op.exec store)

/--
@isnad1 id=envelope.2h5v.s5.6e3d2dc24161 from=translated src=- shape=32a5204a vocab=61936695
-/
theorem EnvelopeChain.append {indexBound valueBound : ℕ}
    {first second : List Structured.Basic} {store : Store}
    (hfirst : EnvelopeChain indexBound valueBound first store)
    (hsecond : EnvelopeChain indexBound valueBound second
      (Structured.Basic.execList first store)) :
    EnvelopeChain indexBound valueBound (first ++ second) store := by
  induction first generalizing store with
  | nil => simpa [Structured.Basic.execList] using hsecond
  | cons op rest ih =>
      exact ⟨hfirst.1, ih hfirst.2 hsecond⟩

/--
@isnad1 id=storeenv.1h4v.s4.38063e5bba0a from=translated src=- shape=fa9190f7 vocab=cd8ac71b
-/
theorem EnvelopeChain.final {indexBound valueBound : ℕ}
    {ops : List Structured.Basic} {store : Store}
    (hchain : EnvelopeChain indexBound valueBound ops store) :
    StoreEnvelope indexBound valueBound (Structured.Basic.execList ops store) := by
  induction ops generalizing store with
  | nil => exact hchain
  | cons op rest ih => exact ih hchain.2

end Basic

/-- A basic instruction preserves an envelope when its destination and written
value fit that envelope.
@isnad1 id=storeenv.3h4v.s5.6a4b9cf48ff0 from=translated src=- shape=937f3e46 vocab=bdc32039
-/
theorem StoreEnvelope.execBasic {indexBound valueBound : ℕ}
    {store : Store} (hstore : StoreEnvelope indexBound valueBound store)
    (op : Structured.Basic) (hindex : Basic.writeIndex op store < indexBound)
    (hvalue : Basic.writeValue op store ≤ valueBound) :
    StoreEnvelope indexBound valueBound (op.exec store) := by
  rw [Basic.exec_eq_update]
  exact hstore.update hindex hvalue

/-- A straight-line list of immediate writes preserves a register whose index
does not occur among the destinations.
@isnad1 id=eq.1h3v.s5.56d2bfafca9b from=translated src=- shape=0c792443 vocab=5f2fae3b
-/
theorem Basic.execList_imm_apply_of_not_mem (writes : List (ℕ × ℕ))
    (store : Store) (index : ℕ) (hnot : index ∉ writes.map Prod.fst) :
    Basic.execList (writes.map fun write => Basic.imm write.1 write.2) store index =
      store index := by
  induction writes generalizing store with
  | nil => rfl
  | cons write rest ih =>
      have hne : index ≠ write.1 := by
        simpa using fun heq => hnot (by simp [heq])
      have htail : index ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (by simp [hmem])
      rw [List.map_cons, Basic.execList, ih _ htail]
      simp [Basic.exec, Function.update_of_ne hne]

/-- With distinct destinations, a listed immediate write determines the final
value at its destination.
@isnad1 id=eq.2h4v.s6.0283261a0031 from=translated src=- shape=5b11ab5d vocab=c0c45a36
-/
theorem Basic.execList_imm_apply_of_mem (writes : List (ℕ × ℕ))
    (store : Store) (hnodup : (writes.map Prod.fst).Nodup)
    {index value : ℕ} (hmem : (index, value) ∈ writes) :
    Basic.execList (writes.map fun write => Basic.imm write.1 write.2) store index =
      value := by
  induction writes generalizing store with
  | nil => simp at hmem
  | cons write rest ih =>
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rw [List.map_cons, Basic.execList]
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst write
        rw [Basic.execList_imm_apply_of_not_mem rest]
        · simp [Basic.exec]
        · simpa using hhead
      · exact ih (store := (Basic.imm write.1 write.2).exec store) htail hrest

/-- A one-bit cushion over the width of the envelope's largest value. -/
def valueWidth (valueBound : ℕ) : ℕ := bitlen valueBound + 1

/--
@isnad1 id=le.1h2v.s4.fc11f4e8d4dd from=translated src=- shape=6b9a563b vocab=cad43eb6
-/
theorem bitlen_le_valueWidth {valueBound value : ℕ} (hvalue : value ≤ valueBound) :
    bitlen value ≤ valueWidth valueBound := by
  have hsize := Nat.size_le_size hvalue
  simpa [bitlen, valueWidth] using le_trans hsize (Nat.le_add_right _ _)

/--
@isnad1 id=le.0h1v.s3.428d76c86939 from=translated src=- shape=8a62b088 vocab=20386f60
-/
theorem one_le_valueWidth (valueBound : ℕ) : 1 ≤ valueWidth valueBound := by
  simp [valueWidth]

/-- Any basic instruction whose pre- and post-stores fit the same envelope has
logarithmic cost at most four times the envelope value width.
@isnad1 id=le.2h4v.s5.761d1692f8ce from=translated src=- shape=d7722b6e vocab=18d96156
-/
theorem Basic.logCost_le_four_valueWidth {indexBound valueBound : ℕ}
    (op : Basic) (store : Store)
    (hstore : StoreEnvelope indexBound valueBound store)
    (hnext : StoreEnvelope indexBound valueBound (op.exec store)) :
    op.logCost store ≤ 4 * valueWidth valueBound := by
  have hone := one_le_valueWidth valueBound
  cases op with
  | imm dst value =>
      have hvalue : value ≤ valueBound := by
        simpa [Basic.exec] using hnext.value_le dst
      have hvalueWidth := bitlen_le_valueWidth hvalue
      simp only [Basic.logCost]
      omega
  | add dst left right =>
      have hleftWidth := bitlen_le_valueWidth (hstore.value_le left)
      have hrightWidth := bitlen_le_valueWidth (hstore.value_le right)
      have hresult : store left + store right ≤ valueBound := by
        simpa [Basic.exec] using hnext.value_le dst
      have hresultWidth := bitlen_le_valueWidth hresult
      simp only [Basic.logCost]
      omega
  | sub dst left right =>
      have hleftWidth := bitlen_le_valueWidth (hstore.value_le left)
      have hrightWidth := bitlen_le_valueWidth (hstore.value_le right)
      simp only [Basic.logCost]
      omega
  | mul dst left right =>
      have hleftWidth := bitlen_le_valueWidth (hstore.value_le left)
      have hrightWidth := bitlen_le_valueWidth (hstore.value_le right)
      have hresult : store left * store right ≤ valueBound := by
        simpa [Basic.exec] using hnext.value_le dst
      have hresultWidth := bitlen_le_valueWidth hresult
      simp only [Basic.logCost]
      omega
  | load dst address =>
      have haddressWidth := bitlen_le_valueWidth (hstore.value_le address)
      have hvalueWidth := bitlen_le_valueWidth (hstore.value_le (store address))
      simp only [Basic.logCost]
      omega
  | store address src =>
      have haddressWidth := bitlen_le_valueWidth (hstore.value_le address)
      have hsourceWidth := bitlen_le_valueWidth (hstore.value_le src)
      simp only [Basic.logCost]
      omega

/-- A source execution with an exact transition count and upper bounds on its
logarithmic cost and peak space. -/
def MeasuredRuns (cmd : Cmd) (initial final : Store)
    (steps costBound spaceLimit : ℕ) : Prop :=
  ∃ cost space, Exec cmd initial final steps cost space ∧
    cost ≤ costBound ∧ space ≤ spaceLimit

/-- A straight-line basic block always has an exact source execution. This
certificate deliberately leaves cost and space existential, allowing semantic
proofs to proceed before a client chooses a resource envelope.
@isnad1 id=ex.0h2v.s4.0bcfd39ab47b from=translated src=- shape=a7924d1e vocab=70c6e5d1
-/
theorem exec_basics_exists (ops : List Basic) (initial : Store) :
    ∃ cost space,
      Exec (Cmd.basics ops) initial (Basic.execList ops initial)
        ops.length cost space := by
  induction ops generalizing initial with
  | nil =>
      exact ⟨0, initial.space, by
        simpa only [Cmd.basics, List.map_nil, Cmd.seqList, Basic.execList,
          List.length_nil] using Exec.skip initial⟩
  | cons op rest ih =>
      cases rest with
      | nil =>
          exact ⟨op.logCost initial,
            max initial.space (op.exec initial).space, by
              simpa [Cmd.basics, Basic.execList, Cmd.seqList] using Exec.basic op initial⟩
      | cons next tail =>
          obtain ⟨cost, space, hrest⟩ := ih (initial := op.exec initial)
          refine ⟨op.logCost initial + cost,
            max (max initial.space (op.exec initial).space) space, ?_⟩
          have hrun := Exec.seq (Exec.basic op initial) hrest
          convert hrun using 1
          · rfl
          · rfl
          · simp only [List.length_cons]; omega

namespace MeasuredRuns

/--
@isnad1 id=measured.1h3v.s4.75a3f12b67a2 from=translated src=- shape=1c5287e6 vocab=d92235d6
-/
theorem skipEnvelope {indexBound valueBound : ℕ} {store : Store}
    (hstore : StoreEnvelope indexBound valueBound store) :
    MeasuredRuns Cmd.skip store store 0 0 (envelopeSpace indexBound valueBound) := by
  exact ⟨0, store.space, Exec.skip store, le_rfl, hstore.space_le⟩

/--
@isnad1 id=measured.2h4v.s5.f7c501ab523b from=translated src=- shape=233ea5e6 vocab=abe5286c
-/
theorem basicEnvelope {indexBound valueBound : ℕ} (op : Basic) (store : Store)
    (hstore : StoreEnvelope indexBound valueBound store)
    (hnext : StoreEnvelope indexBound valueBound (op.exec store)) :
    MeasuredRuns (.basic op) store (op.exec store) 1 (4 * valueWidth valueBound)
      (envelopeSpace indexBound valueBound) := by
  exact ⟨op.logCost store, max store.space (op.exec store).space,
    Exec.basic op store, Basic.logCost_le_four_valueWidth op store hstore hnext,
    max_le hstore.space_le hnext.space_le⟩

/--
@isnad1 id=measured.2h10v.s5.b488781125b2 from=translated src=- shape=93f35ae3 vocab=1bf91283
-/
theorem seq {first second : Cmd} {initial middle final : Store}
    {firstSteps secondSteps firstCost secondCost spaceLimit : ℕ}
    (hfirst : MeasuredRuns first initial middle firstSteps firstCost spaceLimit)
    (hsecond : MeasuredRuns second middle final secondSteps secondCost spaceLimit) :
    MeasuredRuns (.seq first second) initial final (firstSteps + secondSteps)
      (firstCost + secondCost) spaceLimit := by
  obtain ⟨cost₁, space₁, hexec₁, hcost₁, hspace₁⟩ := hfirst
  obtain ⟨cost₂, space₂, hexec₂, hcost₂, hspace₂⟩ := hsecond
  exact ⟨cost₁ + cost₂, max space₁ space₂, Exec.seq hexec₁ hexec₂,
    Nat.add_le_add hcost₁ hcost₂, max_le hspace₁ hspace₂⟩

/-- A straight-line list of basic instructions inherits uniform resource bounds
when every listed instruction preserves the chosen store envelope.
@isnad1 id=and.2h4v.s6.9c7759b32a59 from=translated src=- shape=0fd421b4 vocab=c347e7c9
-/
theorem basicsEnvelope {indexBound valueBound : ℕ} (ops : List Basic)
    (initial : Store) (hinitial : StoreEnvelope indexBound valueBound initial)
    (hpreserve : ∀ op, op ∈ ops → ∀ store,
      StoreEnvelope indexBound valueBound store →
      StoreEnvelope indexBound valueBound (op.exec store)) :
    MeasuredRuns (Cmd.basics ops) initial (Basic.execList ops initial)
      ops.length (4 * ops.length * valueWidth valueBound)
      (envelopeSpace indexBound valueBound) ∧
    StoreEnvelope indexBound valueBound (Basic.execList ops initial) := by
  induction ops generalizing initial with
  | nil =>
      exact ⟨by simpa [Cmd.basics, Basic.execList, Cmd.seqList] using skipEnvelope hinitial,
        hinitial⟩
  | cons op rest ih =>
      have hnext := hpreserve op (by simp) initial hinitial
      have hfirst := basicEnvelope op initial hinitial hnext
      cases rest with
      | nil =>
          exact ⟨by simpa [Cmd.basics, Basic.execList, Cmd.seqList] using hfirst, hnext⟩
      | cons next tail =>
          obtain ⟨hrest, hfinal⟩ := ih (initial := op.exec initial) hnext (by
            intro candidate hcandidate store hstore
            exact hpreserve candidate (by simp [hcandidate]) store hstore)
          have hrun := hfirst.seq hrest
          refine ⟨?_, hfinal⟩
          · change MeasuredRuns (.seq (.basic op) (Cmd.basics (next :: tail)))
              initial (Basic.execList (next :: tail) (op.exec initial))
              (tail.length + 2) (4 * (tail.length + 2) * valueWidth valueBound)
              (envelopeSpace indexBound valueBound)
            convert hrun using 1
            all_goals simp
            all_goals ring

/-- A concrete per-program-point envelope chain yields the same exact-step,
uniform-cost certificate as a globally uniform preservation proof.
@isnad1 id=and.1h4v.s5.fa1180bf9677 from=translated src=- shape=c84372c9 vocab=e488a6a1
-/
theorem basicsEnvelopeChain {indexBound valueBound : ℕ} (ops : List Basic)
    (initial : Store) (hchain : Basic.EnvelopeChain indexBound valueBound ops initial) :
    MeasuredRuns (Cmd.basics ops) initial (Basic.execList ops initial)
      ops.length (4 * ops.length * valueWidth valueBound)
      (envelopeSpace indexBound valueBound) ∧
    StoreEnvelope indexBound valueBound (Basic.execList ops initial) := by
  induction ops generalizing initial with
  | nil =>
      exact ⟨by simpa [Cmd.basics, Basic.execList, Cmd.seqList] using skipEnvelope hchain,
        hchain⟩
  | cons op rest ih =>
      have hinitial := hchain.1
      have htail := hchain.2
      have hnext : StoreEnvelope indexBound valueBound (op.exec initial) := by
        cases rest with
        | nil => exact htail
        | cons next tail => exact htail.1
      have hfirst := basicEnvelope op initial hinitial hnext
      cases rest with
      | nil =>
          exact ⟨by simpa [Cmd.basics, Basic.execList, Cmd.seqList] using hfirst, hnext⟩
      | cons next tail =>
          obtain ⟨hrest, hfinal⟩ :=
            ih (initial := op.exec initial) htail
          have hrun := hfirst.seq hrest
          refine ⟨?_, hfinal⟩
          change MeasuredRuns (.seq (.basic op) (Cmd.basics (next :: tail)))
            initial (Basic.execList (next :: tail) (op.exec initial))
            (tail.length + 2) (4 * (tail.length + 2) * valueWidth valueBound)
            (envelopeSpace indexBound valueBound)
          convert hrun using 1
          all_goals simp
          all_goals ring

/--
@isnad1 id=measured.2h7v.s5.330d19bcc3db from=translated src=- shape=8289ee18 vocab=1892c66a
-/
theorem weakenCost {cmd : Cmd} {initial final : Store}
    {steps costBound largerBound spaceLimit : ℕ}
    (hrun : MeasuredRuns cmd initial final steps costBound spaceLimit)
    (hle : costBound ≤ largerBound) :
    MeasuredRuns cmd initial final steps largerBound spaceLimit := by
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hrun
  exact ⟨cost, space, hexec, le_trans hcost hle, hspace⟩

/--
@isnad1 id=measured.2h7v.s5.aac60d01cdb9 from=translated src=- shape=84e29a4b vocab=1892c66a
-/
theorem weakenSpace {cmd : Cmd} {initial final : Store}
    {steps costBound spaceLimit largerLimit : ℕ}
    (hrun : MeasuredRuns cmd initial final steps costBound spaceLimit)
    (hle : spaceLimit ≤ largerLimit) :
    MeasuredRuns cmd initial final steps costBound largerLimit := by
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hrun
  exact ⟨cost, space, hexec, hcost, le_trans hspace hle⟩

/--
@isnad1 id=measured.3h8v.s5.d0ec6c2baf10 from=translated src=- shape=16d979ed vocab=1892c66a
-/
theorem weaken {cmd : Cmd} {initial final : Store}
    {steps costBound largerCost spaceLimit largerSpace : ℕ}
    (hrun : MeasuredRuns cmd initial final steps costBound spaceLimit)
    (hcost : costBound ≤ largerCost) (hspace : spaceLimit ≤ largerSpace) :
    MeasuredRuns cmd initial final steps largerCost largerSpace :=
  (hrun.weakenCost hcost).weakenSpace hspace

/--
@isnad1 id=measured.3h9v.s6.e820b20ea41e from=translated src=- shape=6f8dbe9c vocab=3f674a43
-/
theorem ifZeroEnvelope {indexBound valueBound test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} {steps costBound : ℕ}
    (htest : initial test = 0)
    (hstore : StoreEnvelope indexBound valueBound initial)
    (hbranch : MeasuredRuns onZero initial final steps costBound
      (envelopeSpace indexBound valueBound)) :
    MeasuredRuns (.ifZero test onZero onNonzero) initial final (steps + 1)
      (valueWidth valueBound + costBound) (envelopeSpace indexBound valueBound) := by
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hbranch
  refine ⟨bitlen (initial test) + 1 + cost, max initial.space space,
    Exec.ifZero htest hexec, ?_, max_le hstore.space_le hspace⟩
  rw [htest]
  have hone := one_le_valueWidth valueBound
  simp only [bitlen, Nat.size_zero, zero_add]
  omega

/--
@isnad1 id=measured.3h9v.s6.1f877526e587 from=translated src=- shape=e70234e2 vocab=470d0afa
-/
theorem ifNonzeroEnvelope {indexBound valueBound test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} {steps costBound : ℕ}
    (htest : initial test ≠ 0)
    (hstore : StoreEnvelope indexBound valueBound initial)
    (hbranch : MeasuredRuns onNonzero initial final steps costBound
      (envelopeSpace indexBound valueBound)) :
    MeasuredRuns (.ifZero test onZero onNonzero) initial final (steps + 2)
      (3 * valueWidth valueBound + costBound)
      (envelopeSpace indexBound valueBound) := by
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hbranch
  refine ⟨bitlen (initial test) + 1 + cost + 1, max initial.space space,
    Exec.ifNonzero htest hexec, ?_, max_le hstore.space_le hspace⟩
  have htestWidth := bitlen_le_valueWidth (hstore.value_le test)
  have hone := one_le_valueWidth valueBound
  omega

/--
@isnad1 id=measured.2h5v.s5.36619bcb7c6b from=translated src=- shape=e601b9c9 vocab=5e7e740b
-/
theorem whileZeroEnvelope {indexBound valueBound test : ℕ} {body : Cmd}
    {store : Store} (htest : store test = 0)
    (hstore : StoreEnvelope indexBound valueBound store) :
    MeasuredRuns (.whileNonzero test body) store store 1 (valueWidth valueBound)
      (envelopeSpace indexBound valueBound) := by
  refine ⟨bitlen (store test) + 1, store.space, Exec.whileZero htest, ?_,
    hstore.space_le⟩
  rw [htest]
  simpa [bitlen] using one_le_valueWidth valueBound

/--
@isnad1 id=measured.4h11v.s6.6ad005206869 from=translated src=- shape=d43df9fd vocab=82da89e6
-/
theorem whileNonzeroEnvelope {indexBound valueBound test : ℕ} {body : Cmd}
    {initial middle final : Store}
    {bodySteps loopSteps bodyCost loopCost : ℕ}
    (htest : initial test ≠ 0)
    (hstore : StoreEnvelope indexBound valueBound initial)
    (hbody : MeasuredRuns body initial middle bodySteps bodyCost
      (envelopeSpace indexBound valueBound))
    (hloop : MeasuredRuns (.whileNonzero test body) middle final loopSteps loopCost
      (envelopeSpace indexBound valueBound)) :
    MeasuredRuns (.whileNonzero test body) initial final
      (bodySteps + loopSteps + 2)
      (3 * valueWidth valueBound + bodyCost + loopCost)
      (envelopeSpace indexBound valueBound) := by
  obtain ⟨bodyActualCost, bodySpace, hbodyExec, hbodyCost, hbodySpace⟩ := hbody
  obtain ⟨loopActualCost, loopSpace, hloopExec, hloopCost, hloopSpace⟩ := hloop
  refine ⟨bitlen (initial test) + 1 + bodyActualCost + 1 + loopActualCost,
    max bodySpace loopSpace, Exec.whileNonzero htest hbodyExec hloopExec, ?_,
    max_le hbodySpace hloopSpace⟩
  have htestWidth := bitlen_le_valueWidth (hstore.value_le test)
  have hone := one_le_valueWidth valueBound
  omega

/-- Exact source transition count obtained by iterating bodies with the given
per-element step count. Each nonempty iteration also pays two loop-control
transitions, and the final zero test pays one. -/
def whileFoldSteps {α : Type*} (bodySteps : α → ℕ) : List α → ℕ
  | [] => 1
  | item :: rest => bodySteps item + whileFoldSteps bodySteps rest + 2

/-- Compositional cost bound for a list-indexed loop. Each nonempty iteration
pays three envelope widths for its nonzero test and back edge; the final zero
test pays one envelope width. -/
def whileFoldCost {α : Type*} (width : ℕ) (bodyCost : α → ℕ) : List α → ℕ
  | [] => width
  | item :: rest => 3 * width + bodyCost item + whileFoldCost width bodyCost rest

/-- Verify a structured loop by folding an abstract state over a logical input
list. The client supplies only its invariant, one body certificate, and the
zero/nonzero interpretations of the test register; run stitching and resource
accounting are generic.
@isnad1 id=ex.4h14v.s7.c097ea80bfff from=translated src=- shape=ecf90422 vocab=798e2a9d
-/
theorem whileFoldEnvelope {α σ : Type*} {indexBound valueBound test : ℕ}
    {body : Cmd} (Inv : List α → σ → Store → Prop)
    (advance : σ → α → σ) (bodySteps bodyCost : α → ℕ)
    (hstore : ∀ (items : List α) (state : σ) (store : Store),
      Inv items state store → StoreEnvelope indexBound valueBound store)
    (hnil : ∀ (state : σ) (store : Store),
      Inv [] state store → store test = 0)
    (hcons : ∀ (item : α) (rest : List α) (state : σ) (store : Store),
      Inv (item :: rest) state store → store test ≠ 0)
    (hbody : ∀ (item : α) (rest : List α) (state : σ) (store : Store),
      Inv (item :: rest) state store →
        ∃ next,
          MeasuredRuns body store next (bodySteps item) (bodyCost item)
            (envelopeSpace indexBound valueBound) ∧
          Inv rest (advance state item) next)
    {items : List α} {state : σ} {initial : Store}
    (hinv : Inv items state initial) :
    ∃ final,
      MeasuredRuns (.whileNonzero test body) initial final
        (whileFoldSteps bodySteps items)
        (whileFoldCost (valueWidth valueBound) bodyCost items)
        (envelopeSpace indexBound valueBound) ∧
      Inv [] (items.foldl advance state) final := by
  induction items generalizing state initial with
  | nil =>
      exact ⟨initial,
        MeasuredRuns.whileZeroEnvelope (hnil state initial hinv)
          (hstore [] state initial hinv), hinv⟩
  | cons item rest ih =>
      obtain ⟨middle, hrun, hnext⟩ := hbody item rest state initial hinv
      obtain ⟨final, hloop, hfinal⟩ := ih hnext
      refine ⟨final, ?_, ?_⟩
      · simpa [whileFoldSteps, whileFoldCost] using
          MeasuredRuns.whileNonzeroEnvelope
            (hcons item rest state initial hinv)
            (hstore (item :: rest) state initial hinv) hrun hloop
      · simpa using hfinal

end MeasuredRuns

end Internal

end Structured

end RAM

end Complexity
