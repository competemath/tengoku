/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Registers.Horner
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.StateBounds
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Machine.Internal.ControllerInvariant

/-!
# Coarse runtime bounds for the streaming Tseitin controller

This proof-only module rounds the token-level state bounds and the concrete
register-operation bounds to one uniform controller budget. For an input of
bit length `n`, every state reached along a valid typed token prefix has all
six register values below `2 * (n + 1)`. One controller token therefore fits
within sixteen copies of `TM.opBudget` at that cap, including sequencing
overhead. The complete token pass is bounded by an explicit quartic.

## Main results

- `two_mul_tokens_length_eq_encode_length_internal`
- `streaming_maxValue_run_prefix_le_internal`
- `bufferValues_run_prefix_bounded_internal`
- `commitLiteralTime_le_controllerTokenBudget_internal`
- `closeClauseTime_le_controllerTokenBudget_internal`
- `controllerRunBudget_le_quartic_internal`
- `typed_controllerRun_le_quartic_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Token count and streaming-state bounds -/

/-- Every concrete token contributes exactly two encoded bits.
@isnad1 id=eq.0h1v.s4.d143fe9bab28 from=translated src=- shape=6a1d94ba vocab=7b42b649
-/
theorem encodeTokens_length_internal (toks : List EncToken) :
    (encodeTokens toks).length = 2 * toks.length := by
  induction toks with
  | nil => rfl
  | cons tok toks ih =>
      cases tok with
      | bit b => cases b <;> simp [encodeTokens_cons, EncToken.encode, ih] <;> omega
      | litSep => simp [encodeTokens_cons, EncToken.encode, ih]; omega
      | clauseSep => simp [encodeTokens_cons, EncToken.encode, ih]; omega

/-- The token count of a typed CNF is exactly half its concrete bit length.
@isnad1 id=eq.0h1v.s4.6ece5437fe93 from=translated src=- shape=eedf9cc7 vocab=919a549c
-/
theorem two_mul_tokens_length_eq_encode_length_internal (φ : CNF) :
    2 * φ.tokens.length = φ.encode.length := by
  rw [← CNF.encodeTokens_tokens φ, encodeTokens_length_internal]

/-- In particular, the number of typed tokens is at most the bit length.
@isnad1 id=le.0h1v.s3.18137aee11f2 from=translated src=- shape=56e7c393 vocab=347f94ef
-/
theorem tokens_length_le_encode_length_internal (φ : CNF) :
    φ.tokens.length ≤ φ.encode.length := by
  have hlength := two_mul_tokens_length_eq_encode_length_internal φ
  omega

/-- One cap used for every unary register during a valid controller run. -/
def controllerValueCap (inputLength : ℕ) : ℕ :=
  2 * (inputLength + 1)

/-- All six concrete buffer-register values lie below a common cap. -/
def BufferValues.BoundedBy (v : BufferValues) (cap : ℕ) : Prop :=
  v.fresh ≤ cap ∧ v.current ≤ cap ∧ v.a ≤ cap ∧ v.b ≤ cap ∧
    v.c ≤ cap ∧ v.scratch ≤ cap

/-- A buffer bound can be enlarged.
@isnad1 id=boundedb.2h3v.s4.67e7dcbeaa91 from=translated src=- shape=85d87de9 vocab=d13a51e6
-/
theorem BufferValues.BoundedBy.mono {v : BufferValues} {cap cap' : ℕ}
    (h : v.BoundedBy cap) (hcap : cap ≤ cap') : v.BoundedBy cap' := by
  rcases h with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  exact ⟨hfresh.trans hcap, hcurrent.trans hcap, ha.trans hcap,
    hb.trans hcap, hc.trans hcap, hscratch.trans hcap⟩

/-- The machine-register representation of a pure state is bounded by that
state's `maxValue`.
@isnad1 id=boundedb.0h1v.s2.275430a90559 from=translated src=- shape=fc2c1e2b vocab=d7fadc86
-/
theorem bufferValues_ofStreaming_boundedBy_maxValue_internal
    (st : Streaming.State) :
    (BufferValues.ofStreaming st).BoundedBy st.maxValue := by
  rcases st with ⟨next, pending, scan, emitted⟩
  cases pending <;> cases scan <;>
    simp [BufferValues.BoundedBy, BufferValues.ofStreaming,
      streamingScanValue, streamingBufferA, streamingBufferB,
      streamingBufferC, Streaming.State.maxValue,
      Streaming.Pending.maxValue, Streaming.Scan.maxValue]

/-- Every successful state reached along a prefix of a typed CNF token stream
fits the global input-length cap.
@isnad1 id=le.3h5v.s6.5c5ddb705cd9 from=translated src=- shape=0a9c40ec vocab=c53a64aa
-/
theorem streaming_maxValue_run_prefix_le_internal
    {z : List Bool} (φ : CNF) (hz : z = φ.encode)
    {pre suffix : List EncToken} {st : Streaming.State}
    (hsplit : φ.tokens = pre ++ suffix)
    (hrun : Streaming.run (Streaming.initial (z.length + 1)) pre = some st) :
    st.maxValue ≤ controllerValueCap z.length := by
  subst z
  have hrunBound := Streaming.maxValue_run_le_internal hrun
  have hpre : pre.length ≤ φ.tokens.length := by
    rw [hsplit, List.length_append]
    omega
  have htokens := tokens_length_le_encode_length_internal φ
  have hinitial :
      (Streaming.initial (φ.encode.length + 1)).maxValue = φ.encode.length + 1 := by
    simp [Streaming.initial, Streaming.State.maxValue,
      Streaming.Pending.maxValue, Streaming.Scan.maxValue]
  rw [hinitial] at hrunBound
  simp only [controllerValueCap]
  omega

/-- The corresponding six unary-register values fit the same prefix-global
cap.
@isnad1 id=boundedb.3h5v.s6.3b1f4fbefce9 from=translated src=- shape=b1b7d030 vocab=044f49fe
-/
theorem bufferValues_run_prefix_bounded_internal
    {z : List Bool} (φ : CNF) (hz : z = φ.encode)
    {pre suffix : List EncToken} {st : Streaming.State}
    (hsplit : φ.tokens = pre ++ suffix)
    (hrun : Streaming.run (Streaming.initial (z.length + 1)) pre = some st) :
    (BufferValues.ofStreaming st).BoundedBy (controllerValueCap z.length) :=
  (bufferValues_ofStreaming_boundedBy_maxValue_internal st).mono
    (streaming_maxValue_run_prefix_le_internal φ hz hsplit hrun)

/-! ## Uniform per-token register budget -/

/-- A deliberately coarse budget for every controller action associated with
one input token. -/
def controllerTokenBudget (cap : ℕ) : ℕ :=
  16 * (TM.opBudget cap + 1)

private theorem literalTime_le_opBudget {value cap : ℕ} (hvalue : value ≤ cap) :
    literalTime value ≤ TM.opBudget cap := by
  simpa only [literalTime] using TM.emitLitTM_le_opBudget hvalue

private theorem copyTime_le_opBudget {src dst cap : ℕ}
    (hsrc : src ≤ cap) (hdst : dst ≤ cap) :
    copyTime src dst ≤ TM.opBudget cap := by
  simpa only [copyTime] using TM.copyIntoTM_le_opBudget hsrc hdst

private theorem unaryUpdateTime_le_opBudget {value cap : ℕ}
    (hvalue : value ≤ cap) :
    unaryUpdateTime value ≤ TM.opBudget cap := by
  simpa only [unaryUpdateTime] using TM.incRegTM_le_opBudget hvalue

/-- Three literal emissions and their small sequencing overhead fit within
four augmented operation budgets.
@isnad1 id=le.3h4v.s5.0e4e7fd8ca4b from=translated src=- shape=a14eba42 vocab=9f45171e
-/
theorem clauseTime_le_four_opBudgets_internal {a b c cap : ℕ}
    (ha : a ≤ cap) (hb : b ≤ cap) (hc : c ≤ cap) :
    clauseTime a b c ≤ 4 * (TM.opBudget cap + 1) := by
  have hA := literalTime_le_opBudget ha
  have hB := literalTime_le_opBudget hb
  have hC := literalTime_le_opBudget hc
  have hop := TM.one_le_opBudget (M := cap)
  simp only [clauseTime]
  omega

/-- The largest pending-clause emission is the empty-clause two-clause
gadget, bounded by nine augmented operation budgets.
@isnad1 id=le.1h3v.s5.f9c441e05386 from=translated src=- shape=1f675eb7 vocab=22041f78
-/
theorem pendingTime_le_nine_opBudgets_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    pendingTime pending v ≤ 9 * (TM.opBudget cap + 1) := by
  rcases hv with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hFresh := clauseTime_le_four_opBudgets_internal hfresh hfresh hfresh
  have hAAA := clauseTime_le_four_opBudgets_internal ha ha ha
  have hABB := clauseTime_le_four_opBudgets_internal ha hb hb
  have hABC := clauseTime_le_four_opBudgets_internal ha hb hc
  have hop := TM.one_le_opBudget (M := cap)
  cases pending with
  | zero =>
      simp only [pendingTime]
      omega
  | one sign =>
      simp only [pendingTime]
      omega
  | two aSign bSign =>
      simp only [pendingTime]
      omega
  | three aSign bSign cSign =>
      simp only [pendingTime]
      omega

/-- Clearing the four literal buffers fits within four augmented operation
budgets.
@isnad1 id=le.1h2v.s5.4d22eb3a015a from=translated src=- shape=0a21647a vocab=af5632d1
-/
theorem clearBuffersTime_le_four_opBudgets_internal
    (v : BufferValues) {cap : ℕ} (hv : v.BoundedBy cap) :
    clearBuffersTime v ≤ 4 * (TM.opBudget cap + 1) := by
  rcases hv with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hCurrent := unaryUpdateTime_le_opBudget hcurrent
  have hA := unaryUpdateTime_le_opBudget ha
  have hB := unaryUpdateTime_le_opBudget hb
  have hC := unaryUpdateTime_le_opBudget hc
  simp only [clearBuffersTime]
  omega

/-- The three copies, increment, and clear in a wide-window rotation fit
within five augmented operation budgets.
@isnad1 id=le.1h2v.s5.5aba8aeedcff from=translated src=- shape=0a21647a vocab=b6962ca8
-/
theorem rollWideBuffersTime_le_five_opBudgets_internal
    (v : BufferValues) {cap : ℕ} (hv : v.BoundedBy cap) :
    rollWideBuffersTime v ≤ 5 * (TM.opBudget cap + 1) := by
  rcases hv with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hFreshA := copyTime_le_opBudget hfresh ha
  have hCB := copyTime_le_opBudget hc hb
  have hCurrentC := copyTime_le_opBudget hcurrent hc
  have hIncrement := unaryUpdateTime_le_opBudget hfresh
  have hClear := unaryUpdateTime_le_opBudget hcurrent
  simp only [rollWideBuffersTime]
  omega

/-- Every literal-commit branch fits within ten augmented operation budgets,
well below the uniform per-token allowance.
@isnad1 id=le.1h3v.s5.a664d646d6a2 from=translated src=- shape=1f675eb7 vocab=4156eb09
-/
theorem commitLiteralTime_le_ten_opBudgets_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    commitLiteralTime pending v ≤ 10 * (TM.opBudget cap + 1) := by
  rcases hv with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hCopyA := copyTime_le_opBudget hcurrent ha
  have hCopyB := copyTime_le_opBudget hcurrent hb
  have hCopyC := copyTime_le_opBudget hcurrent hc
  have hClear := unaryUpdateTime_le_opBudget hcurrent
  have hClause := clauseTime_le_four_opBudgets_internal ha hb hfresh
  have hRoll := rollWideBuffersTime_le_five_opBudgets_internal v
    ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hop := TM.one_le_opBudget (M := cap)
  cases pending with
  | zero =>
      simp only [commitLiteralTime]
      omega
  | one sign =>
      simp only [commitLiteralTime]
      omega
  | two aSign bSign =>
      simp only [commitLiteralTime]
      omega
  | three aSign bSign cSign =>
      simp only [commitLiteralTime]
      omega

/-- The close-clause branch is the worst token action. Its structural time
plus two bit reads and the child-return step still fits the uniform allowance.
@isnad1 id=le.1h3v.s4.6d93a993fe4e from=translated src=- shape=2559617d vocab=501c710c
-/
theorem closeClauseTime_add_three_le_controllerTokenBudget_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    closeClauseTime pending v + 3 ≤ controllerTokenBudget cap := by
  rcases hv with ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hPending := pendingTime_le_nine_opBudgets_internal pending v
    ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hClear := clearBuffersTime_le_four_opBudgets_internal v
    ⟨hfresh, hcurrent, ha, hb, hc, hscratch⟩
  have hAdvance := unaryUpdateTime_le_opBudget hfresh
  have hop := TM.one_le_opBudget (M := cap)
  cases pending with
  | zero =>
      have hClearAdvanced :
          clearBuffersTime (v.advanced .zero) ≤ 4 * (TM.opBudget cap + 1) := by
        simpa [BufferValues.advanced, clearBuffersTime] using hClear
      simp only [closeClauseTime, advanceFreshTime, controllerTokenBudget]
      omega
  | one sign =>
      simp only [closeClauseTime, advanceFreshTime, BufferValues.advanced,
        controllerTokenBudget] at hPending ⊢
      omega
  | two aSign bSign =>
      simp only [closeClauseTime, advanceFreshTime, BufferValues.advanced,
        controllerTokenBudget] at hPending ⊢
      omega
  | three aSign bSign cSign =>
      simp only [closeClauseTime, advanceFreshTime, BufferValues.advanced,
        controllerTokenBudget] at hPending ⊢
      omega

/-- The structural close-clause time alone fits the per-token allowance.
@isnad1 id=le.1h3v.s4.00384654e469 from=translated src=- shape=9a303b38 vocab=31183b5d
-/
theorem closeClauseTime_le_controllerTokenBudget_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    closeClauseTime pending v ≤ controllerTokenBudget cap := by
  have hClose :=
    closeClauseTime_add_three_le_controllerTokenBudget_internal pending v hv
  omega

/-- Literal commits also fit the same uniform per-token allowance.
@isnad1 id=le.1h3v.s4.28de4e5d4f96 from=translated src=- shape=9a303b38 vocab=4b072aeb
-/
theorem commitLiteralTime_le_controllerTokenBudget_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    commitLiteralTime pending v ≤ controllerTokenBudget cap := by
  have hCommit := commitLiteralTime_le_ten_opBudgets_internal pending v hv
  simp only [controllerTokenBudget]
  omega

/-- A literal commit together with both bit reads and the child-return step
fits the uniform per-token allowance.
@isnad1 id=le.1h3v.s4.d413010b65a0 from=translated src=- shape=2559617d vocab=7f4fa276
-/
theorem commitLiteralTime_add_three_le_controllerTokenBudget_internal
    (pending : PendingSigns) (v : BufferValues) {cap : ℕ}
    (hv : v.BoundedBy cap) :
    commitLiteralTime pending v + 3 ≤ controllerTokenBudget cap := by
  have hCommit := commitLiteralTime_le_ten_opBudgets_internal pending v hv
  have hop := TM.one_le_opBudget (M := cap)
  simp only [controllerTokenBudget]
  omega

/-- Incrementing the current literal counter, including both input reads and
the child-return step, fits the uniform per-token allowance.
@isnad1 id=le.1h2v.s4.b732dcd82929 from=translated src=- shape=540597fd vocab=8d24e0dc
-/
theorem unaryUpdateTime_current_add_three_le_controllerTokenBudget_internal
    (v : BufferValues) {cap : ℕ} (hv : v.BoundedBy cap) :
    unaryUpdateTime v.current + 3 ≤ controllerTokenBudget cap := by
  have hUpdate := unaryUpdateTime_le_opBudget hv.2.1
  have hop := TM.one_le_opBudget (M := cap)
  simp only [controllerTokenBudget]
  omega

/-! ## Quartic whole-run budget -/

/-- Token processing plus one sequencing step per token and a final halt. -/
def controllerRunBudget (inputLength : ℕ) : ℕ :=
  (inputLength + 1) *
      (controllerTokenBudget (controllerValueCap inputLength) + 1) + 1

/-- At the input-derived cap, the cubic register budget has a simple closed
form.
@isnad1 id=eq.0h1v.s5.67ae1656049c from=translated src=- shape=8bcde14e vocab=ea54e63d
-/
theorem opBudget_controllerValueCap_eq_internal (n : ℕ) :
    TM.opBudget (controllerValueCap n) = 256 * (n + 2) ^ 3 := by
  simp only [TM.opBudget, controllerValueCap]
  ring

/-- The augmented per-token budget is bounded by a convenient cubic.
@isnad1 id=le.0h1v.s5.df8ad91d5959 from=translated src=- shape=81bb751b vocab=39e8a3a9
-/
theorem controllerTokenBudget_valueCap_le_cubic_internal (n : ℕ) :
    controllerTokenBudget (controllerValueCap n) + 1 ≤
      8192 * (n + 2) ^ 3 := by
  rw [controllerTokenBudget, opBudget_controllerValueCap_eq_internal]
  have hcube : 1 ≤ (n + 2) ^ 3 := Nat.one_le_pow 3 (n + 2) (by omega)
  nlinarith

/-- The full controller pass has an explicit quartic time envelope.
@isnad1 id=le.0h1v.s5.a9b930ed0d70 from=translated src=- shape=11bad5fb vocab=7a2940f3
-/
theorem controllerRunBudget_le_quartic_internal (n : ℕ) :
    controllerRunBudget n ≤ 16384 * (n + 2) ^ 4 := by
  have hcount : n + 1 ≤ n + 2 := by omega
  have htoken := controllerTokenBudget_valueCap_le_cubic_internal n
  have hmul := Nat.mul_le_mul hcount htoken
  have hfour : 1 ≤ (n + 2) ^ 4 := Nat.one_le_pow 4 (n + 2) (by omega)
  rw [controllerRunBudget]
  calc
    (n + 1) * (controllerTokenBudget (controllerValueCap n) + 1) + 1
        ≤ (n + 2) * (8192 * (n + 2) ^ 3) + 1 :=
      Nat.add_le_add hmul le_rfl
    _ = 8192 * (n + 2) ^ 4 + 1 := by ring
    _ ≤ 16384 * (n + 2) ^ 4 := by omega

/-- For a typed input `z = φ.encode`, even charging one controller allowance
for every token and one terminal action lies below the same quartic.
@isnad1 id=le.1h2v.s6.b268d2127fbb from=translated src=- shape=a359618c vocab=821fab40
-/
theorem typed_controllerRun_le_quartic_internal
    {z : List Bool} (φ : CNF) (hz : z = φ.encode) :
    (φ.tokens.length + 1) *
          (controllerTokenBudget (controllerValueCap z.length) + 1) + 1 ≤
      16384 * (z.length + 2) ^ 4 := by
  subst z
  have htokens := tokens_length_le_encode_length_internal φ
  have hcount : φ.tokens.length + 1 ≤ φ.encode.length + 1 := by omega
  have hmul := Nat.mul_le_mul hcount
    (le_refl (controllerTokenBudget (controllerValueCap φ.encode.length) + 1))
  calc
    (φ.tokens.length + 1) *
          (controllerTokenBudget (controllerValueCap φ.encode.length) + 1) + 1
        ≤ controllerRunBudget φ.encode.length := by
      rw [controllerRunBudget]
      exact Nat.add_le_add hmul le_rfl
    _ ≤ 16384 * (φ.encode.length + 2) ^ 4 :=
      controllerRunBudget_le_quartic_internal φ.encode.length

end Machine

end ThreeSAT

end SAT

end Complexity
