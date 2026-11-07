/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Tengoku.Seed.Algebra.BigOperators.Fin
public import Tengoku.Seed.Data.Fintype.Inv
public import Tengoku.Cslib.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending a machine with additional work tapes

`extendTapes tm e`, for an embedding `e : Fin k ↪ Fin k'`, runs `tm` inside a machine with more
work tapes. The tapes selected by `e` are used by `tm`: target tape `e j` plays the role of source
tape `j`. The remaining tapes are left unchanged.

The configuration map `embed e cfg extraTapes extraPos` places `cfg` on the selected tapes and
initialises the remaining tapes from `extraTapes` and `extraPos`.

The main lemmas show that one step and an entire run of the larger machine mirror the corresponding
step and run of `tm`.

## Main definitions

* `Turing.MultiTapeTM.partialInv`: the partial inverse of the tape embedding.
* `Turing.MultiTapeTM.extendTapes`: the machine with reindexed work tapes.
* `Turing.MultiTapeTM.embed`: the corresponding configuration map.
* `Turing.MultiTapeTM.tapeEmb`: the embedding placing the only tape of a one-tape machine on
  tape `i`, and `Turing.MultiTapeTM.noTapes`: the embedding of a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.step_embed` and `Turing.MultiTapeTM.runFrom_embed`: the one-step and run-level
  mirroring lemmas.
* `Turing.MultiTapeTM.workTapePos_embed_of_not_range`: the extra tapes never move.
* `Turing.MultiTapeTM.spaceUsed_embed_le`: the resulting space bound.
* `Turing.MultiTapeTM.oneTapeCfg`: the one-tape view of a configuration.
* `Turing.MultiTapeTM.runFrom_tapeEmb`, `Turing.MultiTapeTM.spaceUsed_tapeEmb_le`: the run and the
  space of a one-tape machine placed on work tape `i`.
* `Turing.MultiTapeTM.TransformsTapes.tapeEmb`: a one-tape specification, read on tape `i`.
* `Turing.MultiTapeTM.runFrom_noTapes`, `Turing.MultiTapeTM.spaceUsed_noTapes_le`: the run and the
  space of a machine without work tapes, placed in a machine with `k` of them.
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The computable analogue of `Function.partialInv` for an embedding `e`: `partialInv e l = some j`
when `e j = l` (such `j` is unique by injectivity), and `none` when `l` lies outside the range of
`e`.-/
@[expose] public def partialInv (e : Fin k ↪ Fin k') (l : Fin k') : Option (Fin k) :=
  if h : l ∈ Set.range e then some (e.invOfMemRange ⟨l, h⟩) else none

/-- `partialInv e` is a partial inverse of `e`.
@isnad1 id=ispartia.0h3v.s5.4cd32182e337 from=translated src=- shape=d880d060 vocab=875c5031
-/
public lemma partialInv_isPartialInv (e : Fin k ↪ Fin k') :
    Function.IsPartialInv e (partialInv e) := fun j l => by
  grind [partialInv, Function.Embedding.left_inv_of_invOfMemRange,
    Function.Embedding.right_inv_of_invOfMemRange]

/-- `tm` run on the tapes selected by the embedding `e`, leaving other tapes untouched: work tape
`e j` plays the role of `tm`'s tape `j`, and any tape outside `range e` is never written and never
moves.-/
@[expose] public def extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    MultiTapeTM k' Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work (e j)
    { inputTape := a.inputTape
      workTapes := fun l => match partialInv e l with
        | some j => a.workTapes j
        | none => (none, 0)
      output := a.output
      state := a.state }

/--
@isnad1 id=eq.0h6v.s5.1fea0b7c2751 from=translated src=- shape=6e432f3b vocab=933a5b9d
-/
@[simp]
public lemma extendTapes_q₀ (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).q₀ = tm.q₀ := rfl

/-- A configuration of `tm`, embedded: tape `j` goes to tape `e j`, the tapes outside `range e`
carry the given `extraTapes` contents and `extraPos` head positions.-/
@[expose] public def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input :=
  ⟨cfg.state, cfg.inputPos,
    fun l => match partialInv e l with
      | some j => cfg.workTapes j
      | none => extraTapes l,
    fun l => match partialInv e l with
      | some j => cfg.workTapePos j
      | none => extraPos l,
    cfg.output⟩

/-- The partial inverse recovers the source tape of an embedded tape.
@isnad1 id=eq.0h4v.s5.bc7dbf6ca0a1 from=translated src=- shape=4e4b3cff vocab=344103cf
-/
@[simp]
public lemma partialInv_embed (e : Fin k ↪ Fin k') (j : Fin k) : partialInv e (e j) = some j :=
  (partialInv_isPartialInv e).eq j

/-- Outside the range of `e`, the partial inverse is undefined.
@isnad1 id=eq.1h4v.s5.2a19556f0f17 from=translated src=- shape=289d2169 vocab=b0592578
-/
public lemma partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (hl : l ∉ Set.range e) :
    partialInv e l = none :=
  dite_eq_right hl

/-- If the partial inverse is `some j`, then `e j = l`.
@isnad1 id=eq.1h5v.s5.6cbe9c50a86e from=translated src=- shape=ffbbdb2d vocab=344103cf
-/
public lemma partialInv_eq_some (e : Fin k ↪ Fin k') {l : Fin k'} {j : Fin k}
    (h : partialInv e l = some j) : e j = l :=
  (partialInv_isPartialInv e j l).mp h

/--
@isnad1 id=eq.0h9v.s5.ab209a737020 from=translated src=- shape=ddb27f54 vocab=007624ee
-/
@[simp]
public lemma embed_inputSymbol (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (embed e cfg extraTapes extraPos).inputSymbol = cfg.inputSymbol := rfl

/--
@isnad1 id=eq.0h10v.s6.5d07225cc772 from=translated src=- shape=050fabb7 vocab=31e23729
-/
@[simp]
public lemma embed_workTapes_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapes (e j) = cfg.workTapes j := by
  simp [embed]

/--
@isnad1 id=eq.0h10v.s6.1a63b5eb33ac from=translated src=- shape=41b7f27c vocab=65289c68
-/
@[simp]
public lemma embed_workTapePos_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapePos (e j) = cfg.workTapePos j := by
  simp [embed]

/--
@isnad1 id=eq.0h10v.s6.cd0db85af231 from=translated src=- shape=430832d1 vocab=259c9396
-/
@[simp]
public lemma embed_workTapeSymbols_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapeSymbols (e j) = cfg.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- Reindexing is a step-semiconjugation: the reindexed machine acts on the embedded tapes exactly
as `tm` does, and never touches the extra tapes.
@isnad1 id=eq.0h10v.s6.a228ad101487 from=translated src=- shape=245a6693 vocab=8a857dcc
-/
public lemma step_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) :
    (tm.extendTapes e).step (embed e cfg extraTapes extraPos)
      = embed e (tm.step cfg) extraTapes extraPos := by
  cases hq : cfg.state with
  | none => simp [embed, hq]
  | some q =>
    rw [step_apply_of_state (cfg := embed e cfg extraTapes extraPos) hq, step_apply_of_state hq]
    simp only [extendTapes, embed_inputSymbol, embed_workTapeSymbols_embed]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [Action.apply, embed] <;>
      cases partialInv e l <;> simp

/-- The reindexed run mirrors the original, with the extra tapes held fixed throughout.
@isnad1 id=eq.0h11v.s6.beab196adc25 from=translated src=- shape=31be5e4f vocab=1c3611b3
-/
public lemma runFrom_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n
      = embed e (tm.runFrom cfg n) extraTapes extraPos :=
  (Function.Semiconj.iterate_right (f := (embed e · extraTapes extraPos))
    (fun c => (step_embed tm e c extraTapes extraPos).symm) n cfg).symm

section Space

/-- The head of a tape outside `range e` never leaves its starting position.
@isnad1 id=eq.1h12v.s6.3898449be404 from=translated src=- shape=25817647 vocab=f638c098
-/
public lemma workTapePos_embed_of_not_range (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) {l : Fin k'} (hl : l ∉ Set.range e) :
    ((tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n).workTapePos l
      = extraPos l := by
  rw [runFrom_embed]
  simp only [embed, partialInv_eq_none e hl]

/-- **Space bound for a reindexed run.** The embedded tapes contribute the space used by `tm`, while
each of the remaining `k' - k` tapes never moves and contributes at most one cell.
@isnad1 id=le.0h11v.s6.a028f428664e from=translated src=- shape=9c56f840 vocab=795ed393
-/
public lemma spaceUsed_embed_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n
      ≤ tm.spaceUsed cfg n + (k' - k) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding e cfg _ 1
    (fun m _ j => by rw [runFrom_embed, embed_workTapePos_embed])
    fun l hl => spaceUsedByTape_le_one _ fun m _ => by
      rw [workTapePos_embed_of_not_range tm e cfg extraTapes extraPos m hl]
      simp only [embed, partialInv_eq_none e hl]

end Space

/-! ### Placing a one-tape machine on a single work tape -/

section OneTape

variable {k : ℕ}

/-- The embedding that places the only work tape of a one-tape machine on tape `i`.-/
@[expose] public def tapeEmb (i : Fin k) : Fin 1 ↪ Fin k :=
  ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

/--
@isnad1 id=eq.0h3v.s5.bf174d25622a from=translated src=- shape=930001e3 vocab=6c8dc5b8
-/
@[simp]
public lemma tapeEmb_apply (i : Fin k) (j : Fin 1) : tapeEmb i j = i := rfl

/--
@isnad1 id=eq.0h2v.s6.a264ce9956d1 from=translated src=- shape=590ff4ed vocab=ddcd5019
-/
@[simp]
public lemma range_tapeEmb (i : Fin k) : Set.range (tapeEmb i) = {i} := by
  ext l
  simp [eq_comm]

/-- Tape `i` is the image of the only tape of a one-tape machine, and no other tape is.
@isnad1 id=eq.0h3v.s6.064d59be2bce from=translated src=- shape=17be1870 vocab=0f82680e
-/
@[simp]
public lemma partialInv_tapeEmb (i l : Fin k) :
    partialInv (tapeEmb i) l = if l = i then some 0 else none := by
  split_ifs with h
  · exact h ▸ partialInv_embed (tapeEmb i) 0
  · exact partialInv_eq_none _ (by simp [h])

/-- A one-tape configuration placed on tape `i` leaves every other tape as it was.
@isnad1 id=eq.0h8v.s7.014ad744fe9e from=translated src=- shape=2ca2b58b vocab=b12d9e9a
-/
public lemma embed_tapeEmb (i : Fin k) (cfg : Cfg 1 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (tapeEmb i) cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Function.update tapes i (cfg.workTapes 0),
        Function.update heads i (cfg.workTapePos 0), cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [embed, hl]

/-- The one-tape view of a configuration of a machine with `k` work tapes: the tape and head of
tape `i`, with everything else as it is.-/
@[expose] public def oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    Cfg 1 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun _ => cfg.workTapes i, fun _ => cfg.workTapePos i, cfg.output⟩

/-- A configuration is its own one-tape view on tape `i`, placed back on tape `i`.
@isnad1 id=eq.0h6v.s5.46e964028e43 from=translated src=- shape=24dbd663 vocab=f6bfb2ba
-/
public lemma embed_oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    embed (tapeEmb i) (oneTapeCfg i cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_tapeEmb]
  simp [oneTapeCfg]

/-- **Running a one-tape machine on work tape `i`.** The run is the run on the one-tape view of the
configuration, placed back on tape `i`; every other tape and head keeps its starting value. Combine
with `embed_tapeEmb` to read off the resulting configuration.
@isnad1 id=eq.0h8v.s6.4f9ef6b36f8d from=translated src=- shape=9103d50c vocab=0a8d652d
-/
public lemma runFrom_tapeEmb (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).runFrom cfg n =
      embed (tapeEmb i) (tm.runFrom (oneTapeCfg i cfg) n) cfg.workTapes cfg.workTapePos := by
  rw [← runFrom_embed, embed_oneTapeCfg]

/-- **Space bound for a one-tape machine placed on tape `i`:** the space of the one-tape run, plus
one cell for each tape the machine does not use.
@isnad1 id=le.0h8v.s6.acd341034bae from=translated src=- shape=5dab4227 vocab=c0ecf593
-/
public lemma spaceUsed_tapeEmb_le (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).spaceUsed cfg n ≤ tm.spaceUsed (oneTapeCfg i cfg) n + (k - 1) := by
  conv_lhs => rw [← embed_oneTapeCfg i cfg]
  exact spaceUsed_embed_le _ _ _ _ _ _

/-- **A one-tape specification on tape `i`.** A one-tape machine placed on tape `i` transforms the
word on that tape as it did on its own tape and leaves every other word alone; each remaining tape
costs one cell.
@isnad1 id=transfor.1h9v.s7.73fbc84d7c35 from=translated src=- shape=37262cad vocab=c772e61b
-/
public theorem TransformsTapes.tapeEmb {tm : MultiTapeTM 1 Symbol State}
    {P : (input : List Symbol) → (Fin 1 → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin 1 → List Symbol) → (Fin 1 → List Symbol) → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (i : Fin k) :
    TransformsTapes (tm.extendTapes (MultiTapeTM.tapeEmb i))
      (fun input ws => P input fun _ => ws i)
      (fun input ws ws' => ∃ v, Q input (fun _ => ws i) v ∧ ws' = Function.update ws i (v 0))
      t (s + (k - 1)) := by
  intro input ws out hP
  obtain ⟨v, hrun, hQ, hspace⟩ := h input (fun _ => ws i) out hP
  simp only [wordsCfg] at hrun hspace
  refine ⟨Function.update ws i (v 0), ?_, ⟨v, hQ, rfl⟩, ?_⟩
  · rw [extendTapes_q₀, runFrom_tapeEmb]
    simp only [oneTapeCfg, wordsCfg, hrun]
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [hl]
  · rw [extendTapes_q₀]
    exact (spaceUsed_tapeEmb_le _ _ _ _).trans (Nat.add_le_add_right hspace _)

end OneTape

section NoTapes

variable {k : ℕ}

/-- The embedding of a machine without work tapes into a machine with `k` of them.-/
@[expose] public def noTapes (k : ℕ) : Fin 0 ↪ Fin k := ⟨Fin.elim0, fun a => a.elim0⟩

/-- No tape is in the range of `noTapes`.
@isnad1 id=eq.0h2v.s4.655cbb6c2b6f from=translated src=- shape=47644d46 vocab=6b871cf4
-/
@[simp]
public lemma partialInv_noTapes (l : Fin k) : partialInv (noTapes k) l = none :=
  partialInv_eq_none _ (by simp)

/-- The view of a configuration as a configuration of a machine without work tapes.-/
@[expose] public def noTapesCfg (cfg : Cfg k Symbol State input) : Cfg 0 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, nofun, nofun, cfg.output⟩

/-- A configuration without work tapes, placed in a machine with `k` of them, only contributes its
state, its input head and its output.
@isnad1 id=eq.0h7v.s6.b78fc527f343 from=translated src=- shape=0cabeae7 vocab=93e9be4f
-/
public lemma embed_noTapes (cfg : Cfg 0 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (noTapes k) cfg tapes heads = ⟨cfg.state, cfg.inputPos, tapes, heads, cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp [embed]

/-- A configuration is its tapeless view, placed back on its tapes.
@isnad1 id=eq.0h5v.s5.d2314fcd7f06 from=translated src=- shape=5f912893 vocab=74cc38e9
-/
public lemma embed_noTapesCfg (cfg : Cfg k Symbol State input) :
    embed (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_noTapes]
  rfl

/-- **Running a machine without work tapes inside a machine with `k` of them.** Only the state, the
input head and the output change; every work tape and work head keeps its starting value.
@isnad1 id=eq.0h7v.s7.ed32bf6eabdc from=translated src=- shape=a64c8160 vocab=632b927b
-/
public lemma runFrom_noTapes (tm : MultiTapeTM 0 Symbol State) (cfg : Cfg k Symbol State input)
    (n : ℕ) :
    (tm.extendTapes (noTapes k)).runFrom cfg n =
      ⟨(tm.runFrom (noTapesCfg cfg) n).state, (tm.runFrom (noTapesCfg cfg) n).inputPos,
        cfg.workTapes, cfg.workTapePos, (tm.runFrom (noTapesCfg cfg) n).output⟩ := by
  rw [← embed_noTapesCfg cfg, runFrom_embed, embed_noTapes]
  simp [embed_noTapesCfg]

/-- **Space bound for a machine without work tapes:** one cell for each tape it does not use.
@isnad1 id=le.0h7v.s5.569aee99e4e2 from=translated src=- shape=d045027a vocab=5a16b4da
-/
public lemma spaceUsed_noTapes_le (tm : MultiTapeTM 0 Symbol State)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (noTapes k)).spaceUsed cfg n ≤ k := by
  conv_lhs => rw [← embed_noTapesCfg cfg]
  simpa using spaceUsed_embed_le tm (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos n

end NoTapes

end Turing.MultiTapeTM
