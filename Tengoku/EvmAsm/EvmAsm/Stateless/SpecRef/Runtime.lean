/-
  EvmAsm.Stateless.SpecRef.Runtime

  Lean functional *reference port* of `execution-specs @ tests-zkevm@v0.4.0`
  `src/ethereum/forks/amsterdam/vm/runtime.py` — the runtime helpers used
  while executing EVM code.  Feeder for bead `evm-asm-4ch8f.49.2`: it is the
  mathematical spec anchor for the JUMP/JUMPI validity tail (`.55`). The
  emitted handlers scan the current frame's code directly; this module supplies
  the matching pushdata-aware boundary model. Reference model only — no theorems about
  the RV64 guest live here.

  Currently ports the single function `get_valid_jump_destinations`.
-/
module

public import Tengoku.EvmAsm.EvmAsm.EL.RLP.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (Byte)

/-! ## `get_valid_jump_destinations`

Code is a `List Byte` (matching `SpecRef.Crypto`'s `Bytes`, but stated
inline here so this module stays decoupled from the crypto/accel imports —
the JUMP/JUMPI tail `.55` consumes it without pulling ZisK).

The Python analyses the code with a single forward pass over instruction
*boundaries*, starting at `pc = 0`:

* `JUMPDEST` (`0x5b`) → the boundary is a valid jump destination; `pc += 1`.
* `PUSH1..PUSH32` (`0x60..0x7f`) → skip the opcode and its `n = op-0x5f`
  immediate bytes: `pc += (op - 0x60 + 1) + 1`.  A `0x5b` *inside* the
  immediate data is therefore never a boundary and never valid.
* EIP-8024 `DUPN`/`SWAPN` (`0xe6`/`0xe7`) → if the next byte exists and lies in
  the *invalid* immediate range `0x5b..0x7f` the immediate is **not** skipped
  (the byte stays an instruction boundary): `pc += 1`.  Otherwise skip the
  immediate: `pc += 2`.
* EIP-8024 `EXCHANGE` (`0xe8`) → same, with invalid immediate range
  `0x52..0x7f`.
* any other byte → `pc += 1`.  (The Python distinguishes a valid non-listed
  opcode, which advances `pc += 1`, from an invalid byte, whose `ValueError`
  path also advances `pc += 1` before `continue`.  Both advance by exactly one
  and add no destination, so a single "else `+1`" arm faithfully covers both.)

We factor the boundary step into `jdAdvance` (the amount `pc` moves, always
`≥ 1`) and record the visited-and-`0x5b` boundaries in `validJumpDestinations`.
-/

/-- The amount the boundary pointer advances at `pc`, mirroring one iteration
    of `get_valid_jump_destinations`.  Always `≥ 1` (see `jdAdvance_pos`), so
    the analysis terminates and — in the guest — the scan variant `end - pc`
    strictly decreases on every arm.-/
def jdAdvance (code : List Byte) (pc : Nat) : Nat :=
  let op := (code.getD pc 0).toNat
  if op = 0x5b then 1
  else if 0x60 ≤ op ∧ op ≤ 0x7f then (op - 0x60 + 1) + 1
  else if op = 0xe6 ∨ op = 0xe7 then
    (if pc + 1 < code.length
        ∧ 0x5b ≤ (code.getD (pc + 1) 0).toNat ∧ (code.getD (pc + 1) 0).toNat ≤ 0x7f
     then 1 else 2)
  else if op = 0xe8 then
    (if pc + 1 < code.length
        ∧ 0x52 ≤ (code.getD (pc + 1) 0).toNat ∧ (code.getD (pc + 1) 0).toNat ≤ 0x7f
     then 1 else 2)
  else 1

/-- Every arm of the boundary step advances the pointer by at least one byte.
    This is the per-arm "≥1 advance" fact the jumpdest-scan loop variant
    (`end - pc`) relies on.
@isnad1 id=le.0h2v.s4.1a047b338496 from=translated src=- shape=81e36898 vocab=6f4c6f5b
-/
theorem jdAdvance_pos (code : List Byte) (pc : Nat) : 1 ≤ jdAdvance code pc := by
  simp only [jdAdvance]
  repeat' split
  all_goals omega

/-- Boundary walk with an explicit `fuel` budget.  Because every step advances
    `pc` by `≥ 1`, `fuel = code.length` suffices to reach the end (see
    `validJumpDestinations`).-/
def validJDaux (code : List Byte) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    if pc < code.length then
      let rest := validJDaux code fuel (pc + jdAdvance code pc)
      if (code.getD pc 0).toNat = 0x5b then pc :: rest else rest
    else []

/-- The set of valid jump destinations of `code`, as a list of 0-indexed
    positions (the Python returns a `Set[Uint]`; membership is decidable, so a
    list is an adequate reference model).  Faithful port of
    `get_valid_jump_destinations`.-/
def validJumpDestinations (code : List Byte) : List Nat :=
  validJDaux code code.length 0

/-- Decidable membership view, convenient as a bitmap post
    (`bit idx set ⟺ isValidJumpDest code idx`).-/
def isValidJumpDest (code : List Byte) (idx : Nat) : Bool :=
  idx ∈ validJumpDestinations code

/-! ## Characterization

Every position the walk records is in-bounds and holds the `JUMPDEST` opcode.
This is the load-bearing fact for the JUMP/JUMPI validity tail (`.55`): a
destination that passes the O(1) bitmap test is necessarily a `0x5b` byte at an
instruction boundary — the pushdata/immediate skips are what make it sound. -/
/--
@isnad1 id=and.1h4v.s5.82a805403c24 from=translated src=- shape=5898954e vocab=105c06c0
-/
theorem validJDaux_mem (code : List Byte) (fuel pc : Nat) {idx : Nat}
    (h : idx ∈ validJDaux code fuel pc) :
    idx < code.length ∧ (code.getD idx 0).toNat = 0x5b := by
  induction fuel generalizing pc with
  | zero => simp [validJDaux] at h
  | succ f ih =>
    unfold validJDaux at h
    split at h
    · next hlt =>
      simp only at h
      split at h
      · next hjd =>
        rcases List.mem_cons.1 h with rfl | h'
        · exact ⟨hlt, hjd⟩
        · exact ih _ h'
      · exact ih _ h
    · simp at h

/-- A valid jump destination is an in-bounds `JUMPDEST` (`0x5b`) byte.
@isnad1 id=and.1h2v.s5.26ea3dbd767e from=translated src=- shape=f9b420e1 vocab=ff124506
-/
theorem mem_validJumpDestinations (code : List Byte) {idx : Nat}
    (h : idx ∈ validJumpDestinations code) :
    idx < code.length ∧ (code.getD idx 0).toNat = 0x5b :=
  validJDaux_mem code code.length 0 h

/-! ## Boundary walk, reachability, and the one-step prefix decomposition

`validJDaux` uses an explicit `fuel` budget, which is awkward for the induction
the guest scan proof (`evm-asm-cfjzu`) needs.  `walkFrom` is the same walk with
well-founded recursion on `code.length - pc`; `walkFrom_zero_eq` bridges it to
`validJumpDestinations`.  `Reaches code s t` records that `t` is on the walk
starting at `s` (an *instruction boundary* relative to `s`).

The payoff is `vjd_lt_step` (L1): between a boundary `pc` and its successor
`pc + jdAdvance code pc`, the *only* possible valid destination is `pc` itself.
This is what lets each scan arm extend the invariant's bitmap clause by exactly
its own step — and it is where the pushdata/immediate skips become load-bearing
(deleting a PUSH-skip arm changes `jdAdvance`, hence the boundary set). -/

/-- The boundary walk from `pc`, as the list of recorded (`0x5b`) positions.
    Well-founded on `code.length - pc` (each step advances `≥ 1`, `jdAdvance_pos`).-/
def walkFrom (code : List Byte) (pc : Nat) : List Nat :=
  if _h : pc < code.length then
    let rest := walkFrom code (pc + jdAdvance code pc)
    if (code.getD pc 0).toNat = 0x5b then pc :: rest else rest
  else []
termination_by code.length - pc
decreasing_by have := jdAdvance_pos code pc; omega

/--
@isnad1 id=eq.0h2v.s6.673405582ac2 from=translated src=- shape=906b8061 vocab=78462d01
-/
theorem walkFrom_unfold (code : List Byte) (pc : Nat) :
    walkFrom code pc =
      if pc < code.length then
        (if (code.getD pc 0).toNat = 0x5b then pc :: walkFrom code (pc + jdAdvance code pc)
         else walkFrom code (pc + jdAdvance code pc))
      else [] := by rw [walkFrom]; split <;> simp

/-- Every position the walk from `s` records is `≥ s`.
@isnad1 id=le.1h3v.s4.059a070a846e from=translated src=- shape=685b1e69 vocab=cbe4a41c
-/
theorem mem_walkFrom_ge (code : List Byte) (s x : Nat) (h : x ∈ walkFrom code s) : s ≤ x := by
  rw [walkFrom_unfold] at h
  split at h
  · have hrec : ∀ y ∈ walkFrom code (s + jdAdvance code s), s ≤ y := fun y hy => by
      have := mem_walkFrom_ge code (s + jdAdvance code s) y hy; omega
    split at h
    · rcases List.mem_cons.1 h with rfl | h'
      · exact Nat.le_refl _
      · exact hrec _ h'
    · exact hrec _ h
  · simp at h
termination_by code.length - s
decreasing_by have := jdAdvance_pos code s; omega

/-- `t` is on the boundary walk starting at `s`.-/
inductive Reaches (code : List Byte) : Nat → Nat → Prop where
  | refl (s : Nat) : Reaches code s s
  | step (s t : Nat) (h : s < code.length) (hr : Reaches code (s + jdAdvance code s) t) :
      Reaches code s t

/--
@isnad1 id=le.1h3v.s4.4f9c0b268bba from=translated src=- shape=e9a2bbe3 vocab=3f4cd204
-/
theorem Reaches.le {code : List Byte} {s t : Nat} (h : Reaches code s t) : s ≤ t := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s t hlt hr ih => have := jdAdvance_pos code s; omega

/-- The boundary step advances by at most 33 (a `PUSH32` opcode plus its 32
    immediates).
@isnad1 id=le.0h2v.s4.18834aa0d37c from=translated src=- shape=2a4ef811 vocab=6f4c6f5b
-/
theorem jdAdvance_le (code : List Byte) (pc : Nat) : jdAdvance code pc ≤ 33 := by
  simp only [jdAdvance]
  repeat' split
  all_goals omega

/-- A boundary reached from `0` lies within `code.length + 32` (the last step
    starts below `code.length` and advances by `≤ 33`).  Bounds the scan
    pointer's overshoot past the code end.
@isnad1 id=le.1h2v.s5.eff3c53aecd9 from=translated src=- shape=7d2800a2 vocab=4f53a88b
-/
theorem Reaches_zero_le {code : List Byte} {t : Nat} (h : Reaches code 0 t) :
    t ≤ code.length + 32 := by
  have aux : ∀ {s t : Nat}, Reaches code s t → t ≤ s ∨ t ≤ code.length + 32 := by
    intro s t h
    induction h with
    | refl => exact Or.inl (Nat.le_refl _)
    | step s t hlt hr ih =>
      have hadv := jdAdvance_le code s
      rcases ih with h1 | h1
      · exact Or.inr (by omega)
      · exact Or.inr h1
  rcases aux h with h1 | h1 <;> omega

/-- Reachability extends by one boundary step at the far end — the invariant's
    "advance `x5`" transition.
@isnad1 id=reaches.2h3v.s5.560d36a9cdf8 from=translated src=- shape=8b363af7 vocab=3ba136b4
-/
theorem Reaches.extend {code : List Byte} {s p : Nat} (hr : Reaches code s p)
    (hp : p < code.length) : Reaches code s (p + jdAdvance code p) := by
  induction hr with
  | refl s => exact .step s _ hp (.refl _)
  | step s t hlt hr ih => exact .step s _ hlt (ih hp)

/-- Positions of `walkFrom code s` that are `≥ p` are exactly `walkFrom code p`,
    when `p` is reachable from `s`.  The core inductive split (L1).
@isnad1 id=mem.3h4v.s5.84b71337c4ff from=translated src=- shape=f7505e5d vocab=58a75b4e
-/
theorem splitWalk {code : List Byte} {s p : Nat} (hr : Reaches code s p) :
    ∀ x ∈ walkFrom code s, p ≤ x → x ∈ walkFrom code p := by
  induction hr with
  | refl => exact fun x hx _ => hx
  | step s t hlt hr ih =>
    intro x hx hpx
    rw [walkFrom_unfold, ite_eq_left hlt] at hx
    have hge : s + jdAdvance code s ≤ t := hr.le
    have hpos := jdAdvance_pos code s
    have hxin : x ∈ walkFrom code (s + jdAdvance code s) := by
      split at hx
      · rcases List.mem_cons.1 hx with heq | h'
        · exfalso; omega
        · exact h'
      · exact hx
    exact ih x hxin hpx

/-- `walkFrom code p` is a suffix of `walkFrom code s` when `p` is reachable.
@isnad1 id=mem.2h4v.s5.d2418430450d from=translated src=- shape=188bccb7 vocab=a9100f21
-/
theorem walkFrom_subset {code : List Byte} {s p : Nat} (hr : Reaches code s p) :
    ∀ x ∈ walkFrom code p, x ∈ walkFrom code s := by
  induction hr with
  | refl => exact fun x hx => hx
  | step s t hlt hr ih =>
    intro x hx
    rw [walkFrom_unfold, ite_eq_left hlt]
    split
    · exact List.mem_cons_of_mem _ (ih x hx)
    · exact ih x hx

/-- Enough fuel makes the fuelled walk agree with the well-founded one.
@isnad1 id=eq.1h3v.s5.ef4c0fbc667e from=translated src=- shape=3eb8b7dc vocab=0c4b033b
-/
theorem validJDaux_eq_walkFrom (code : List Byte) (fuel pc : Nat)
    (hfuel : code.length - pc ≤ fuel) :
    validJDaux code fuel pc = walkFrom code pc := by
  induction fuel generalizing pc with
  | zero => rw [validJDaux, walkFrom_unfold, ite_eq_right (by omega : ¬ pc < code.length)]
  | succ f ih =>
    rw [validJDaux, walkFrom_unfold]
    split
    · next hlt => rw [ih (pc + jdAdvance code pc) (by have := jdAdvance_pos code pc; omega)]
    · rfl

/-- `validJumpDestinations` is the walk from `0`.
@isnad1 id=eq.0h1v.s3.725e769df70c from=translated src=- shape=e73548dc vocab=8f292333
-/
theorem walkFrom_zero_eq (code : List Byte) :
    walkFrom code 0 = validJumpDestinations code := by
  rw [validJumpDestinations, validJDaux_eq_walkFrom code code.length 0 (by omega)]

/-- **L1 — the one-step prefix decomposition** (the scan-arm crux).  For a
    boundary `pc` (`Reaches code 0 pc`, `pc < length`), the valid destinations
    below `pc + jdAdvance code pc` are those below `pc`, plus `pc` itself exactly
    when `code[pc] = 0x5b`.  Every scan arm extends its bitmap clause by this.
@isnad1 id=iff.2h3v.s6.e8bf8372e930 from=translated src=- shape=eeceb04e vocab=4242ee16
-/
theorem vjd_lt_step {code : List Byte} {pc : Nat}
    (hr : Reaches code 0 pc) (hlt : pc < code.length) (idx : Nat) :
    (idx ∈ validJumpDestinations code ∧ idx < pc + jdAdvance code pc)
    ↔ ((idx ∈ validJumpDestinations code ∧ idx < pc)
        ∨ ((code.getD pc 0).toNat = 0x5b ∧ idx = pc)) := by
  rw [← walkFrom_zero_eq]
  constructor
  · rintro ⟨hmem, hlt2⟩
    rcases Nat.lt_or_ge idx pc with hip | hip
    · exact Or.inl ⟨hmem, hip⟩
    · have hin := splitWalk hr idx hmem hip
      rw [walkFrom_unfold, ite_eq_left hlt] at hin
      split at hin
      · next hjd =>
        rcases List.mem_cons.1 hin with heq | htail
        · exact Or.inr ⟨hjd, heq⟩
        · exact absurd (mem_walkFrom_ge _ _ _ htail) (by omega)
      · exact absurd (mem_walkFrom_ge _ _ _ hin) (by omega)
  · have hpos := jdAdvance_pos code pc
    rintro (⟨hmem, hip⟩ | ⟨hjd, rfl⟩)
    · exact ⟨hmem, by omega⟩
    · refine ⟨walkFrom_subset hr idx ?_, by omega⟩
      rw [walkFrom_unfold, ite_eq_left hlt, ite_eq_left hjd]; exact List.mem_cons_self

end EvmAsm.Stateless.SpecRef
