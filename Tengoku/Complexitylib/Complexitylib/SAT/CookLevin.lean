/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Rename
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Internal
public import Tengoku.Complexitylib.Complexitylib.SAT.Verifier

/-!
# Cook–Levin tableau core

This file defines the Cook–Levin tableau formula and proves its semantic
correctness. The polynomial-time emitter, reductions, and final theorem
`SAT.NPComplete_language` are assembled in `SAT/CookLevin/Assembly.lean`.
Membership `language ∈ NP` is supplied by `SAT/Headline.lean`.

## Completed development

```
NPComplete_language                       (= ⟨language_mem_NP, NPHard_language⟩)
└ NPHard_language                         (unpack any L ∈ NP → its NTM)
  └ cookLevin_reduction               (multi-tape → single-tape, then ↓)
    ├ NTM.exists_singleTape_decidesInTime   (SingleTape.lean)
    └ cookLevin_reduction_singleTape
        ├ reductionFn                 (def: x ↦ (tableauCNFFlat …).encode)
        ├ reductionFn_mem_FP          ✓ poly-time emitter TM
        └ tableauCNF_correct          (= encode_mem_LSAT_iff ∘ B ∘ hdec)
            ├ tableauCNF              ✓ the tableau formula
            ├ tableauCNF_satisfiable_iff  ✓ sat ↔ accepting computation
            └ encode_mem_LSAT_iff     ✓ (CNF.encode injective)
```

All nodes in this outline are proved. The reduction machine and final
NP-hardness/NP-completeness assembly live in `SAT/CookLevin/Assembly.lean`;
the emitter implementation is split across the modules under
`SAT/CookLevin/`.
-/

@[expose] public section

namespace Complexity

open Complexity

namespace SAT

/-! ## Tableau variable encoding

The computation-tableau formula's Boolean variables are indexed by `ℕ`. Each
"atom" of the tableau — a state bit, a nondeterministic choice bit, a tape-cell
bit, or a head-position bit, all indexed by a time-step — is injected into `ℕ`
by iterated `Nat.pair`, so distinct atoms receive distinct SAT variables. -/

namespace Tableau

/-- Inject a tagged 4-tuple of naturals into one natural by iterated `Nat.pair`. -/
def enc (tag a b c d : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair a (Nat.pair b (Nat.pair c d)))

/-- `enc` is injective on each component (it is a composition of bijective pairings).
@isnad1 id=and.1h10v.s5.3c455b2c762c from=translated src=- shape=915a6412 vocab=25c1ad07
-/
theorem enc_inj {tag a b c d tag' a' b' c' d' : ℕ}
    (h : enc tag a b c d = enc tag' a' b' c' d') :
    tag = tag' ∧ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  simp only [enc, Nat.pair_eq_pair] at h
  tauto

/-- Variable: at time `t` the machine is in the state with index `q` (one-hot). -/
def vState (t q : ℕ) : ℕ := enc 0 t q 0 0
/-- Variable: at time `t` the nondeterministic choice bit is `true`. -/
def vChoice (t : ℕ) : ℕ := enc 1 t 0 0 0
/-- Variable: at time `t`, cell `pos` of tape `tp` holds the symbol with index `s`. -/
def vCell (t tp pos s : ℕ) : ℕ := enc 2 t tp (Nat.pair pos s) 0
/-- Variable: at time `t`, the head of tape `tp` is at cell `pos`. -/
def vHead (t tp pos : ℕ) : ℕ := enc 3 t tp pos 0

/-- The symbol index of a tape symbol: `0,1,2,3` for `0,1,□,▷`. Injective, so a
    one-hot encoding over `{0,1,2,3}` faithfully names the four tape symbols. -/
def symIdx : Γ → ℕ
  | Γ.zero => 0
  | Γ.one => 1
  | Γ.blank => 2
  | Γ.start => 3

/-- `symIdx` is injective: distinct tape symbols receive distinct indices.
@isnad1 id=injectiv.0h0v.s2.dbccb6c4c5fc from=translated src=- shape=54c8eceb vocab=f5249e1e
-/
theorem symIdx_inj : Function.Injective symIdx := by
  intro a b h; cases a <;> cases b <;> simp_all [symIdx]

/-- "At least one of `vars` is true": the single disjunction of positive literals. -/
def atLeastOne (vars : List ℕ) : Clause := vars.map (fun v => ⟨true, v⟩)

/-- "At most one of `vars` is true": for every ordered pair `(vᵢ, vⱼ)` the binary
    clause `¬vᵢ ∨ ¬vⱼ`. -/
def atMostOne : List ℕ → List Clause
  | [] => []
  | v :: vs => vs.map (fun w => ([⟨false, v⟩, ⟨false, w⟩] : Clause)) ++ atMostOne vs

/-- "Exactly one of `vars` is true" as a list of clauses (at-least-one and the
    pairwise at-most-one constraints). -/
def exactlyOne (vars : List ℕ) : List Clause := atLeastOne vars :: atMostOne vars

/-- The at-most-one clauses are satisfied iff no two listed variables are both true.
@isnad1 id=iff.0h2v.s5.703c4a444244 from=translated src=- shape=d6f4df5d vocab=dc3e4a8e
-/
theorem atMostOne_sat (α : Assignment) (vars : List ℕ) :
    CNF.eval α (atMostOne vars) = true ↔
      vars.Pairwise (fun v w => ¬(α.get v = true ∧ α.get w = true)) := by
  induction vars with
  | nil => simp [atMostOne]
  | cons v vs ih =>
    rw [atMostOne, CNF.eval_append, Bool.and_eq_true, ih, List.pairwise_cons]
    refine and_congr ?_ Iff.rfl
    simp only [CNF.eval, List.all_map, List.all_eq_true]
    refine forall_congr' fun w => imp_congr Iff.rfl ?_
    simp only [Function.comp_apply, Clause.eval, List.any_cons, List.any_nil,
      Bool.or_false, Lit.eval]
    generalize α.get v = a
    generalize α.get w = b
    cases a <;> cases b <;> simp

/-- Under the at-most-one (pairwise) constraint, any two true listed variables
    coincide — the uniqueness half of one-hot decoding.
@isnad1 id=eq.5h4v.s6.651790526711 from=translated src=- shape=a015071a vocab=fe8912cc
-/
theorem atMostOne_unique {α : Assignment} {vars : List ℕ} {v w : ℕ}
    (h : vars.Pairwise (fun a b => ¬(α.get a = true ∧ α.get b = true)))
    (hv : v ∈ vars) (hw : w ∈ vars) (hvt : α.get v = true) (hwt : α.get w = true) : v = w := by
  by_contra hne
  have hsymm : Std.Symm (fun a b => ¬(α.get a = true ∧ α.get b = true)) :=
    ⟨fun _ _ hab hba => hab ⟨hba.2, hba.1⟩⟩
  exact (h.forall hv hw hne) ⟨hvt, hwt⟩

/-- An implication clause `cond ++ [conseq]` whose `cond` literals are all false is
    satisfied only if its consequent literal is true. (Each active-transition clause
    is of this shape; when the read-config matches, the consequence is forced.)
@isnad1 id=eq.2h3v.s5.106bb05c0728 from=translated src=- shape=eb9a9e41 vocab=45b035ec
-/
theorem clause_cond_conseq (α : Assignment) (cond : Clause) (c : Lit)
    (hsat : Clause.eval α (cond ++ [c]) = true)
    (hcond : cond.any (Lit.eval α) = false) : Lit.eval α c = true := by
  simp only [Clause.eval, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    hcond, Bool.false_or] at hsat
  exact hsat

/-- A satisfied positive literal `⟨true, v⟩` means its variable is true.
@isnad1 id=eq.1h2v.s4.01dee96f7e00 from=translated src=- shape=f26f2355 vocab=ea3fc1e5
-/
theorem litTrue {α : Assignment} {v : ℕ} (h : Lit.eval α ⟨true, v⟩ = true) :
    α.get v = true := by simpa [Lit.eval] using h

/-- A positive unit clause `[v]` is satisfied iff its variable is true.
@isnad1 id=eq.0h2v.s4.5ac527941725 from=translated src=- shape=d3a27c3f vocab=b97e865b
-/
theorem unit_eval (α : Assignment) (v : ℕ) :
    Clause.eval α [(⟨true, v⟩ : Lit)] = α.get v := by
  simp [Clause.eval, Lit.eval]

/-- A list of positive unit clauses is satisfied iff every listed variable is true.
@isnad1 id=iff.0h2v.s5.ace05dfd3560 from=translated src=- shape=5120a08e vocab=64380644
-/
theorem allUnit_eval (α : Assignment) (vs : List ℕ) :
    CNF.eval α (vs.map (fun v => ([⟨true, v⟩] : Clause))) = true ↔ ∀ v ∈ vs, α.get v = true := by
  simp only [CNF.eval, List.all_map, List.all_eq_true, Function.comp_apply, unit_eval]

/-- `CNF.eval` of a `map`-built clause list: every mapped clause holds.
@isnad1 id=eq.0h4v.s4.0a8594017279 from=translated src=- shape=5ad5f9a6 vocab=1d50c3bb
-/
theorem cnf_eval_map {β : Type*} (α : Assignment) (l : List β) (f : β → Clause) :
    CNF.eval α (l.map f) = l.all (fun a => Clause.eval α (f a)) := by
  simp [CNF.eval, List.all_map, Function.comp_def]

/-- `CNF.eval` of a `flatMap`-built clause list: every sub-CNF holds.
@isnad1 id=eq.0h4v.s4.527f71c5727d from=translated src=- shape=02136cf6 vocab=cef147ca
-/
theorem cnf_eval_flatMap {β : Type*} (α : Assignment) (l : List β) (f : β → CNF) :
    CNF.eval α (l.flatMap f) = l.all (fun a => CNF.eval α (f a)) := by
  simp [CNF.eval, List.all_flatMap]

/-- Index of a machine state as a natural, via the canonical `Fintype` enumeration
    of `N.Q`; injective, so a one-hot encoding over `Fin (card Q)` names the states. -/
noncomputable def stateIdx {k : ℕ} (N : NTM k) (q : N.Q) : ℕ := (Fintype.equivFin N.Q q).val

/-- `stateIdx` is injective: distinct machine states receive distinct indices.
@isnad1 id=injectiv.0h2v.s3.6597d21a93ee from=translated src=- shape=6b2da5f5 vocab=e5364dc6
-/
theorem stateIdx_inj {k : ℕ} (N : NTM k) : Function.Injective (stateIdx N) := by
  intro a b h
  exact (Fintype.equivFin N.Q).injective (Fin.val_injective h)

/-- The symbol at position `pos` of tape `tp` in the start configuration on input
    `x`: cell `0` is always `▷`; tape `0` (the input) carries `x` at cells `1…|x|`;
    every other cell is blank. Mirrors `Tape.init` applied to each tape. -/
def initCellSym (x : List Bool) (tp pos : ℕ) : Γ :=
  if pos = 0 then Γ.start
  else if tp = 0 then ((x.map Γ.ofBool)[pos - 1]?).getD Γ.blank
  else Γ.blank

/-- One-hot constraint that every time-step `0…steps` is in exactly one state. -/
noncomputable def oneHotStates {k : ℕ} (N : NTM k) (steps : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    exactlyOne ((List.range (Fintype.card N.Q)).map (vState t))

/-- One-hot constraint that every cell (each tape `0…k+1`, position `0…P`, time
    `0…steps`) holds exactly one of the four symbols. -/
def oneHotCells (k steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        exactlyOne ((List.range 4).map (vCell t tp pos))

/-- One-hot constraint that every tape head (each tape `0…k+1`, time `0…steps`) is
    at exactly one position in `0…P`. -/
def oneHotHeads (k steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      exactlyOne ((List.range (P + 1)).map (vHead t tp))

/-- Unit clauses fixing the start configuration at time `0`: state `qstart`, every
    head at cell `0`, and every cell holding its `initCellSym` value. -/
noncomputable def startClauses {k : ℕ} (N : NTM k) (steps : ℕ) (x : List Bool) :
    List Clause :=
  let P := steps + x.length + 1
  ([⟨true, vState 0 (stateIdx N N.qstart)⟩] : Clause) ::
    ((List.range (k + 2)).map (fun tp => ([⟨true, vHead 0 tp 0⟩] : Clause)) ++
     (List.range (k + 2)).flatMap (fun tp =>
       (List.range (P + 1)).map (fun pos =>
         ([⟨true, vCell 0 tp pos (symIdx (initCellSym x tp pos))⟩] : Clause))))

/-- Unit clauses fixing acceptance at time `steps`: the state is `qhalt` and cell
    `1` of the output tape (index `k+1`) holds `1`. -/
noncomputable def acceptClauses {k : ℕ} (N : NTM k) (steps : ℕ) : List Clause :=
  [[⟨true, vState steps (stateIdx N N.qhalt)⟩],
   [⟨true, vCell steps (k + 1) 1 (symIdx Γ.one)⟩]]

/-- **Transition frame.** A cell not under its tape's head keeps its symbol from
    time `t` to `t+1`. For each tape/position/symbol, the two clauses encode
    `¬(head at pos) → (cellₜ = cellₜ₊₁)` (a head literal disjoined with each
    direction of the `↔`). The complementary "active" clauses (cell under the head
    updated per `N.δ`) are supplied separately. -/
def frameClauses (k steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        (List.range 4).flatMap fun s =>
          [([⟨true, vHead t tp pos⟩, ⟨false, vCell t tp pos s⟩,
              ⟨true, vCell (t + 1) tp pos s⟩] : Clause),
           ([⟨true, vHead t tp pos⟩, ⟨true, vCell t tp pos s⟩,
              ⟨false, vCell (t + 1) tp pos s⟩] : Clause)]

/-- New head position after a move (mirrors `Tape.move`): `left` decrements
    (clamped at `0` by `Nat` subtraction), `right` increments, `stay` keeps. -/
def posMove (pos : ℕ) (d : Dir3) : ℕ :=
  match d with
  | Dir3.left => pos - 1
  | Dir3.right => pos + 1
  | Dir3.stay => pos

/-- The four tape symbols, enumerated. -/
def allSyms : List Γ := [Γ.zero, Γ.one, Γ.blank, Γ.start]

/-- Every tape symbol appears in `allSyms`.
@isnad1 id=mem.0h1v.s3.80628888d59d from=translated src=- shape=dc4ac6e8 vocab=e2439089
-/
@[simp] theorem mem_allSyms (s : Γ) : s ∈ allSyms := by cases s <;> simp [allSyms]

/-- Every Boolean appears in the two-element list `[true, false]`.
@isnad1 id=mem.0h1v.s4.6a46c9239bb8 from=translated src=- shape=7e1d3238 vocab=b619be4b
-/
theorem mem_true_false (b : Bool) : b ∈ [true, false] := by cases b <;> simp

/-- The shared "read-config" condition literals (all negated) of one transition
    tuple: state `q`, the three heads at `pi`/`pw`/`po` reading `si`/`sw`/`so`, and
    choice `b`. When `α` exhibits exactly this read-config every literal is false. -/
noncomputable def activeCond (N : NTM 1) (t : ℕ) (q : N.Q)
    (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ) (po : ℕ) (so : Γ) (b : Bool) : Clause :=
  [⟨false, vState t (stateIdx N q)⟩,
   ⟨false, vHead t 0 pi⟩, ⟨false, vCell t 0 pi (symIdx si)⟩,
   ⟨false, vHead t 1 pw⟩, ⟨false, vCell t 1 pw (symIdx sw)⟩,
   ⟨false, vHead t 2 po⟩, ⟨false, vCell t 2 po (symIdx so)⟩,
   ⟨!b, vChoice t⟩]

/-- The seven transition clauses for one read-config + choice tuple at time `t`,
    encoding **`N.trace`'s step**: if `q = qhalt` the configuration stays (the
    machine has halted), otherwise the next state is `out.1` (`out := N.δ b q …`),
    the work/output cells under their heads become `out`'s writes, and the three
    heads move per `out` (the input cell is read-only). -/
noncomputable def activeClausesAt (N : NTM 1) (t : ℕ) (q : N.Q)
    (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ) (po : ℕ) (so : Γ) (b : Bool) : List Clause :=
  let out := N.δ b q si (fun _ => sw) so
  let nextState := if q = N.qhalt then q else out.1
  -- writing at cell `0` is a no-op (it stays `▷`), so a head at `0` keeps its symbol
  let wSym := if q = N.qhalt then sw else if pw = 0 then sw else (out.2.1 0).toΓ
  let oSym := if q = N.qhalt then so else if po = 0 then so else out.2.2.1.toΓ
  let iH := if q = N.qhalt then pi else posMove pi out.2.2.2.1
  let wH := if q = N.qhalt then pw else posMove pw (out.2.2.2.2.1 0)
  let oH := if q = N.qhalt then po else posMove po out.2.2.2.2.2
  let cond : Clause := activeCond N t q pi si pw sw po so b
  [cond ++ [⟨true, vState (t + 1) (stateIdx N nextState)⟩],
   cond ++ [⟨true, vCell (t + 1) 0 pi (symIdx si)⟩],
   cond ++ [⟨true, vCell (t + 1) 1 pw (symIdx wSym)⟩],
   cond ++ [⟨true, vCell (t + 1) 2 po (symIdx oSym)⟩],
   cond ++ [⟨true, vHead (t + 1) 0 iH⟩],
   cond ++ [⟨true, vHead (t + 1) 1 wH⟩],
   cond ++ [⟨true, vHead (t + 1) 2 oH⟩]]

/-- **Active transition clauses** — `activeClausesAt` for every time `t < steps`,
    state `q`, the three head positions/read symbols, and choice bit `b`. Together
    with the frame clauses these enforce `c_{t+1} = step c_t (choice t)`. -/
noncomputable def activeTransitionClauses (N : NTM 1) (steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (Finset.univ : Finset N.Q).toList.flatMap fun q =>
      (List.range (P + 1)).flatMap fun pi =>
        allSyms.flatMap fun si =>
          (List.range (P + 1)).flatMap fun pw =>
            allSyms.flatMap fun sw =>
              (List.range (P + 1)).flatMap fun po =>
                allSyms.flatMap fun so =>
                  [true, false].flatMap fun b =>
                    activeClausesAt N t q pi si pw sw po so b

/-- The acceptance clauses hold iff the final state is `qhalt` and output cell `1`
    holds `1` (the two facts witnessing an accepting halt).
@isnad1 id=iff.0h3v.s6.9727042854a1 from=translated src=- shape=9e8a0d21 vocab=af44fae2
-/
theorem acceptClauses_sat (N : NTM 1) (steps : ℕ) (α : Assignment) :
    CNF.eval α (acceptClauses N steps) = true ↔
      α.get (vState steps (stateIdx N N.qhalt)) = true ∧
      α.get (vCell steps 2 1 (symIdx Γ.one)) = true := by
  simp [acceptClauses, CNF.eval, Clause.eval, Lit.eval]

/-- The start clauses hold iff time-`0` is the start configuration: state `qstart`,
    every head (tapes `0,1,2`) at cell `0`, and every cell holding its
    `initCellSym` value.
@isnad1 id=iff.0h4v.s7.ba54b51b8094 from=translated src=- shape=0ec3a6ab vocab=7a6f455f
-/
theorem startClauses_sat (N : NTM 1) (steps : ℕ) (x : List Bool) (α : Assignment) :
    CNF.eval α (startClauses N steps x) = true ↔
      (α.get (vState 0 (stateIdx N N.qstart)) = true ∧
       (∀ tp, tp < 3 → α.get (vHead 0 tp 0) = true) ∧
       (∀ tp, tp < 3 → ∀ pos, pos ≤ steps + x.length + 1 →
         α.get (vCell 0 tp pos (symIdx (initCellSym x tp pos))) = true)) := by
  simp only [startClauses, CNF.eval_cons, CNF.eval_append, unit_eval, cnf_eval_map,
    cnf_eval_flatMap, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-- The frame clauses hold iff, whenever a tape head is *not* at a position, that
    cell keeps its symbol from time `t` to `t+1`.
@isnad1 id=iff.0h4v.s6.a3b2dc515cfb from=translated src=- shape=5525d834 vocab=1fd4c6e6
-/
theorem frameClauses_sat (k steps P : ℕ) (α : Assignment) :
    CNF.eval α (frameClauses k steps P) = true ↔
      ∀ t, t < steps → ∀ tp, tp < k + 2 → ∀ pos, pos ≤ P → ∀ s, s < 4 →
        α.get (vHead t tp pos) = false →
        α.get (vCell t tp pos s) = α.get (vCell (t + 1) tp pos s) := by
  simp only [frameClauses, cnf_eval_flatMap, List.all_eq_true, List.mem_range, Nat.lt_succ_iff,
    CNF.eval_cons, CNF.eval_nil, Bool.and_true, Clause.eval, List.any_cons, List.any_nil,
    Bool.or_false, Lit.eval, Bool.and_eq_true]
  refine forall_congr' fun t => imp_congr Iff.rfl <| forall_congr' fun tp => imp_congr Iff.rfl <|
    forall_congr' fun pos => imp_congr Iff.rfl <| forall_congr' fun s => imp_congr Iff.rfl ?_
  generalize α.get (vHead t tp pos) = h
  generalize α.get (vCell t tp pos s) = a
  generalize α.get (vCell (t + 1) tp pos s) = b
  cases h <;> cases a <;> cases b <;> simp

/-- The state one-hot clauses hold iff every time-step satisfies its exactly-one
    state constraint.
@isnad1 id=iff.0h3v.s5.f30de089f5db from=translated src=- shape=83aaa1be vocab=93780e79
-/
theorem oneHotStates_sat (N : NTM 1) (steps : ℕ) (α : Assignment) :
    CNF.eval α (oneHotStates N steps) = true ↔
      ∀ t, t ≤ steps →
        CNF.eval α (exactlyOne ((List.range (Fintype.card N.Q)).map (vState t))) = true := by
  simp only [oneHotStates, cnf_eval_flatMap, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-- The cell one-hot clauses hold iff every cell satisfies its exactly-one symbol
    constraint.
@isnad1 id=iff.0h4v.s6.74acaa3d794a from=translated src=- shape=3d3cf87d vocab=da731da5
-/
theorem oneHotCells_sat (k steps P : ℕ) (α : Assignment) :
    CNF.eval α (oneHotCells k steps P) = true ↔
      ∀ t, t ≤ steps → ∀ tp, tp < k + 2 → ∀ pos, pos ≤ P →
        CNF.eval α (exactlyOne ((List.range 4).map (vCell t tp pos))) = true := by
  simp only [oneHotCells, cnf_eval_flatMap, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-- The head one-hot clauses hold iff every tape head satisfies its exactly-one
    position constraint.
@isnad1 id=iff.0h4v.s6.053b1719987f from=translated src=- shape=59546a7b vocab=73b0faa4
-/
theorem oneHotHeads_sat (k steps P : ℕ) (α : Assignment) :
    CNF.eval α (oneHotHeads k steps P) = true ↔
      ∀ t, t ≤ steps → ∀ tp, tp < k + 2 →
        CNF.eval α (exactlyOne ((List.range (P + 1)).map (vHead t tp))) = true := by
  simp only [oneHotHeads, cnf_eval_flatMap, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-- The active transition clauses hold iff, for every read-config + choice tuple,
    its `activeClausesAt` block holds (which says: if `α` exhibits that read-config
    at time `t`, then time `t+1` is the `N.δ`-step).
@isnad1 id=iff.0h4v.s6.62e6edace3a2 from=translated src=- shape=5964a953 vocab=00ce1353
-/
theorem activeTransitionClauses_sat (N : NTM 1) (steps P : ℕ) (α : Assignment) :
    CNF.eval α (activeTransitionClauses N steps P) = true ↔
      ∀ t, t < steps → ∀ q : N.Q, ∀ pi, pi ≤ P → ∀ si : Γ, ∀ pw, pw ≤ P → ∀ sw : Γ,
        ∀ po, po ≤ P → ∀ so : Γ, ∀ b : Bool,
        CNF.eval α (activeClausesAt N t q pi si pw sw po so b) = true := by
  simp only [activeTransitionClauses, cnf_eval_flatMap, List.all_eq_true, List.mem_range,
    Nat.lt_succ_iff, Finset.mem_toList, Finset.mem_univ, mem_allSyms, mem_true_false,
    forall_true_left]

/-- When `α` exhibits the read-config of a transition tuple — state `q`, the heads
    at `pi`/`pw`/`po` reading `si`/`sw`/`so`, and choice `b` — every literal of
    `activeCond` is false (so each transition clause forces its consequence).
@isnad1 id=eq.8h11v.s7.4bd908aba4b9 from=translated src=- shape=eeb5a3af vocab=716c2e20
-/
theorem activeCond_false (N : NTM 1) (α : Assignment) (t : ℕ) (q : N.Q)
    (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ) (po : ℕ) (so : Γ) (b : Bool)
    (h1 : α.get (vState t (stateIdx N q)) = true)
    (h2 : α.get (vHead t 0 pi) = true) (h3 : α.get (vCell t 0 pi (symIdx si)) = true)
    (h4 : α.get (vHead t 1 pw) = true) (h5 : α.get (vCell t 1 pw (symIdx sw)) = true)
    (h6 : α.get (vHead t 2 po) = true) (h7 : α.get (vCell t 2 po (symIdx so)) = true)
    (h8 : α.get (vChoice t) = b) :
    (activeCond N t q pi si pw sw po so b).any (Lit.eval α) = false := by
  simp only [activeCond, List.any_cons, List.any_nil, Lit.eval, h1, h2, h3, h4, h5, h6, h7, h8]
  cases b <;> simp

end Tableau

/-- **Computation-tableau formula.** `tableauCNF N steps x` is the CNF that is
    satisfiable exactly when the (single-work-tape) machine `N` has an accepting
    computation on input `x` within `steps` steps — variables encode the tape /
    head / state contents at each time-step together with the nondeterministic
    choice bits, and clauses enforce the start configuration, per-step transition
    validity, and acceptance. -/
noncomputable def tableauCNF (N : NTM 1) (steps : ℕ) (x : List Bool) : CNF :=
  let P := steps + x.length + 1
  Tableau.oneHotStates N steps ++ Tableau.oneHotCells 1 steps P ++
    Tableau.oneHotHeads 1 steps P ++ Tableau.startClauses N steps x ++
    Tableau.frameClauses 1 steps P ++ Tableau.activeTransitionClauses N steps P ++
    Tableau.acceptClauses N steps

/-- The tableau is satisfied (by `α`) exactly when all seven clause families are —
    the bridge from `tableauCNF` to the per-family characterizations.
@isnad1 id=iff.0h4v.s7.a62467c7167c from=translated src=- shape=cb1c7746 vocab=1c595488
-/
theorem tableauCNF_eval_split (N : NTM 1) (steps : ℕ) (x : List Bool) (α : Assignment) :
    CNF.eval α (tableauCNF N steps x) = true ↔
      (CNF.eval α (Tableau.oneHotStates N steps) = true ∧
       CNF.eval α (Tableau.oneHotCells 1 steps (steps + x.length + 1)) = true ∧
       CNF.eval α (Tableau.oneHotHeads 1 steps (steps + x.length + 1)) = true ∧
       CNF.eval α (Tableau.startClauses N steps x) = true ∧
       CNF.eval α (Tableau.frameClauses 1 steps (steps + x.length + 1)) = true ∧
       CNF.eval α (Tableau.activeTransitionClauses N steps (steps + x.length + 1)) = true ∧
       CNF.eval α (Tableau.acceptClauses N steps) = true) := by
  rw [tableauCNF]
  simp only [CNF.eval_append, Bool.and_eq_true, and_assoc]

open Tableau in
/-- `α` represents configuration `c` at time `t` (positions bounded by `P`): the
    one-hot state/cell/head variables that hold of `c` are all set true in `α`. The
    invariant carried through the backward (sat → accepts) direction. -/
def Represents (N : NTM 1) (α : Assignment) (P t : ℕ) (c : Cfg 1 N.Q) : Prop :=
  α.get (vState t (stateIdx N c.state)) = true ∧
  (∀ pos, pos ≤ P → α.get (vCell t 0 pos (symIdx (c.input.cells pos))) = true) ∧
  (∀ pos, pos ≤ P → α.get (vCell t 1 pos (symIdx ((c.work 0).cells pos))) = true) ∧
  (∀ pos, pos ≤ P → α.get (vCell t 2 pos (symIdx (c.output.cells pos))) = true) ∧
  α.get (vHead t 0 c.input.head) = true ∧
  α.get (vHead t 1 (c.work 0).head) = true ∧
  α.get (vHead t 2 c.output.head) = true

/-- One step of `N.trace` from configuration `c` with choice bit `b`: stays if
    halted, otherwise applies `N.δ`. (`N.trace (t+1)` is this applied to `N.trace t`.) -/
def traceStep (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool) : Cfg 1 N.Q :=
  if c.state = N.qhalt then c
  else
    let out := N.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
    { state := out.1, input := c.input.move out.2.2.2.1,
      work := fun i => (c.work i).writeAndMove (out.2.1 i) (out.2.2.2.2.1 i),
      output := c.output.writeAndMove out.2.2.1 out.2.2.2.2.2 }

/-- `N.trace 1` is a single `traceStep`.
@isnad1 id=eq.0h3v.s5.1f4c5d6c07bd from=translated src=- shape=1bf1b70b vocab=7e3e2257
-/
theorem trace_one_eq (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool) :
    N.trace 1 (fun _ => b) c = traceStep N c b := by
  simp only [NTM.trace, traceStep]

/-- Peel the last step: `N.trace (t+1)` is one `traceStep` from `N.trace t`.
@isnad1 id=eq.0h4v.s6.d9357ffb8746 from=translated src=- shape=914d2568 vocab=f1d935e4
-/
theorem trace_succ_eq (N : NTM 1) (g : ℕ → Bool) (t : ℕ) (c : Cfg 1 N.Q) :
    N.trace (t + 1) (fun i => g i.val) c = traceStep N (N.trace t (fun i => g i.val) c) (g t) := by
  rw [N.trace_add_fun t 1 g c]
  have : (fun i : Fin 1 => g (t + i.val)) = (fun _ => g t) := by
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0; simp
  rw [this, trace_one_eq]

open Tableau in
/-- Base case: a satisfying assignment for the start clauses represents the initial
    configuration at time `0`.
@isnad1 id=represen.1h4v.s6.16d949c4ff90 from=translated src=- shape=1875b915 vocab=e24a71c1
-/
theorem represents_init (N : NTM 1) (α : Assignment) (steps : ℕ) (x : List Bool)
    (hstart : CNF.eval α (startClauses N steps x) = true) :
    Represents N α (steps + x.length + 1) 0 (N.initCfg x) := by
  rw [startClauses_sat] at hstart
  obtain ⟨hstate, hheads, hcells⟩ := hstart
  have hci : ∀ pos, (N.initCfg x).input.cells pos = initCellSym x 0 pos := by
    intro pos; simp [Tape.init, initCellSym]
  have hcw : ∀ pos, ((N.initCfg x).work 0).cells pos = initCellSym x 1 pos := by
    intro pos; simp [Tape.init, initCellSym]
  have hco : ∀ pos, (N.initCfg x).output.cells pos = initCellSym x 2 pos := by
    intro pos; simp [Tape.init, initCellSym]
  refine ⟨hstate, fun pos hpos => ?_, fun pos hpos => ?_, fun pos hpos => ?_,
    hheads 0 (by norm_num), hheads 1 (by norm_num), hheads 2 (by norm_num)⟩
  · rw [hci]; exact hcells 0 (by norm_num) pos hpos
  · rw [hcw]; exact hcells 1 (by norm_num) pos hpos
  · rw [hco]; exact hcells 2 (by norm_num) pos hpos

/-! Tape `move`/`writeAndMove` cell/head behaviour, used to match `traceStep`'s
    fields against the active-transition consequence variables. -/

/-- `Tape.move` changes the head exactly as `Tableau.posMove` computes.
@isnad1 id=eq.0h2v.s3.719997b187da from=translated src=- shape=778eb112 vocab=553a7dfe
-/
theorem tape_move_head (t : Tape) (d : Dir3) : (t.move d).head = Tableau.posMove t.head d := by
  cases d <;> rfl

/-- `Tape.writeAndMove` changes the head exactly as `Tableau.posMove` computes.
@isnad1 id=eq.0h3v.s4.8bc0a1263f32 from=translated src=- shape=7d0ae30b vocab=e1f60d09
-/
theorem tape_writeAndMove_head (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head = Tableau.posMove t.head d := by
  rw [Tape.writeAndMove, tape_move_head, Tape.write_head]

/-- `Tape.writeAndMove` leaves every cell other than the (old) head position unchanged.
@isnad1 id=eq.1h4v.s4.5fd2cbf84685 from=translated src=- shape=01c2fe96 vocab=e2e0e387
-/
theorem tape_writeAndMove_cells_ne (t : Tape) (s : Γ) (d : Dir3) {pos : ℕ} (h : pos ≠ t.head) :
    (t.writeAndMove s d).cells pos = t.cells pos := by
  rw [Tape.writeAndMove, Tape.move_cells]
  unfold Tape.write; split_ifs with hh
  · rfl
  · exact Function.update_of_ne h s t.cells

/-- `Tape.writeAndMove` sets the (old) head cell to the written symbol, except at cell `0`
    where writing is a no-op.
@isnad1 id=eq.0h3v.s5.8d9220d0a3ab from=translated src=- shape=51210904 vocab=b6e524c3
-/
theorem tape_writeAndMove_cells_self (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).cells t.head = if t.head = 0 then t.cells t.head else s := by
  rw [Tape.writeAndMove, Tape.move_cells]
  unfold Tape.write; split_ifs with hh
  · rfl
  · exact Function.update_self t.head s t.cells

open Tableau in
/-- The seven consequence variables of the matching active-transition tuple are all
    true: when `α` represents `c` at time `t`, the read-config matches, so each
    `activeClausesAt` clause forces its consequence.
@isnad1 id=other.6h6v.s10.d9761fc3e3a7 from=translated src=- shape=a8efe016 vocab=36432364
-/
theorem represents_conseqs (N : NTM 1) (α : Assignment) (steps P : ℕ)
    (hactive : CNF.eval α (activeTransitionClauses N steps P) = true)
    (t : ℕ) (ht : t < steps) (c : Cfg 1 N.Q) (hrep : Represents N α P t c)
    (hhi : c.input.head ≤ P) (hhw : (c.work 0).head ≤ P) (hho : c.output.head ≤ P) :
    let b := α.get (vChoice t)
    let out := N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read
    α.get (vState (t+1) (stateIdx N (if c.state = N.qhalt then c.state else out.1))) = true ∧
    α.get (vCell (t+1) 0 c.input.head (symIdx c.input.read)) = true ∧
    α.get (vCell (t+1) 1 (c.work 0).head (symIdx (if c.state = N.qhalt then (c.work 0).read
      else if (c.work 0).head = 0 then (c.work 0).read else (out.2.1 0).toΓ))) = true ∧
    α.get (vCell (t+1) 2 c.output.head (symIdx (if c.state = N.qhalt then c.output.read
      else if c.output.head = 0 then c.output.read else out.2.2.1.toΓ))) = true ∧
    α.get (vHead (t+1) 0 (if c.state = N.qhalt then c.input.head
      else posMove c.input.head out.2.2.2.1)) = true ∧
    α.get (vHead (t+1) 1 (if c.state = N.qhalt then (c.work 0).head
      else posMove (c.work 0).head (out.2.2.2.2.1 0))) = true ∧
    α.get (vHead (t+1) 2 (if c.state = N.qhalt then c.output.head
      else posMove c.output.head out.2.2.2.2.2)) = true := by
  obtain ⟨hst, hIci, hIcw, hIco, hHi, hHw, hHo⟩ := hrep
  intro b out
  have hcond := activeCond_false N α t c.state c.input.head c.input.read (c.work 0).head
    (c.work 0).read c.output.head c.output.read b
    hst hHi (hIci c.input.head hhi) hHw (hIcw (c.work 0).head hhw) hHo (hIco c.output.head hho) rfl
  have hat := (activeTransitionClauses_sat N steps P α).mp hactive t ht c.state
    c.input.head hhi c.input.read (c.work 0).head hhw (c.work 0).read c.output.head hho
    c.output.read b
  simp only [activeClausesAt, CNF.eval, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hat
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := hat
  exact ⟨litTrue (clause_cond_conseq α _ _ ha1 hcond),
    litTrue (clause_cond_conseq α _ _ ha2 hcond),
    litTrue (clause_cond_conseq α _ _ ha3 hcond),
    litTrue (clause_cond_conseq α _ _ ha4 hcond),
    litTrue (clause_cond_conseq α _ _ ha5 hcond),
    litTrue (clause_cond_conseq α _ _ ha6 hcond),
    litTrue (clause_cond_conseq α _ _ ha7 hcond)⟩

/-- A head move lands at most one cell to the right of where it started.
@isnad1 id=le.0h2v.s4.90177541f525 from=translated src=- shape=44408379 vocab=c3772d2d
-/
theorem posMove_le (pos : ℕ) (d : Dir3) : Tableau.posMove pos d ≤ pos + 1 := by
  cases d <;> simp only [Tableau.posMove] <;> omega

/-- After `t` steps each head has moved at most `t` cells from its start at `0`.
@isnad1 id=and.0h4v.s7.50b0ef45c7ac from=translated src=- shape=a675c2d7 vocab=c68da90b
-/
theorem trace_heads_le (N : NTM 1) (g : ℕ → Bool) (x : List Bool) (t : ℕ) :
    (N.trace t (fun i => g i.val) (N.initCfg x)).input.head ≤ t ∧
    ((N.trace t (fun i => g i.val) (N.initCfg x)).work 0).head ≤ t ∧
    (N.trace t (fun i => g i.val) (N.initCfg x)).output.head ≤ t := by
  induction t with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [NTM.trace, NTM.initCfg, Cfg.init, Tape.init]
  | succ t ih =>
    obtain ⟨ihi, ihw, iho⟩ := ih
    rw [trace_succ_eq]
    refine ⟨?_, ?_, ?_⟩ <;> unfold traceStep <;> split_ifs with hq
    · omega
    · rw [tape_move_head]; exact le_trans (posMove_le _ _) (by omega)
    · omega
    · rw [tape_writeAndMove_head]; exact le_trans (posMove_le _ _) (by omega)
    · omega
    · rw [tape_writeAndMove_head]; exact le_trans (posMove_le _ _) (by omega)

open Tableau in
/-- Symbol indices are below `4`, the number of tape symbols.
@isnad1 id=lt.0h1v.s3.4881835f6c81 from=translated src=- shape=a311c14d vocab=ef88f292
-/
theorem symIdx_lt (s : Γ) : symIdx s < 4 := by cases s <;> decide

open Tableau in
/-- State indices are below the number of machine states.
@isnad1 id=lt.0h3v.s4.028140dded57 from=translated src=- shape=9841dd51 vocab=20d95656
-/
theorem stateIdx_lt {k : ℕ} (N : NTM k) (q : N.Q) : stateIdx N q < Fintype.card N.Q :=
  (Fintype.equivFin N.Q q).isLt

/-- Assignment backed by a function `g`, truncated to `[0, M)`; reads back as `g`
    on that range. The forward direction builds its satisfying witness this way. -/
def assignOf (M : ℕ) (g : ℕ → Bool) : Assignment := (List.range M).map g

/-- `assignOf M g` reads back as `g` on variables below `M`.
@isnad1 id=eq.1h3v.s4.836ac9bd0d28 from=translated src=- shape=fc4f455b vocab=c7935422
-/
theorem assignOf_get {M : ℕ} (g : ℕ → Bool) {v : ℕ} (h : v < M) :
    (assignOf M g).get v = g v := by
  simp [assignOf, Assignment.get, h]

/-- Indicator assignment for a finite list of "true" variables: every listed
    variable reads `true`, every other variable reads `false`. The truncation
    length is one past the list's maximum, so listed variables stay in range while
    unlisted ones are either out of range or decided `false`. -/
def listAssign (l : List ℕ) : Assignment := assignOf (l.foldr max 0 + 1) (fun i => decide (i ∈ l))

/-- `listAssign l` reads `true` on every listed variable.
@isnad1 id=eq.1h2v.s4.64935dd9054b from=translated src=- shape=498ad17b vocab=345ccd2d
-/
theorem listAssign_get_true {l : List ℕ} {v : ℕ} (h : v ∈ l) :
    (listAssign l).get v = true := by
  rw [listAssign, assignOf_get _ (Nat.lt_succ_of_le (List.le_max_of_le' 0 h le_rfl))]
  simp [h]

/-- `listAssign l` reads `false` on every unlisted variable.
@isnad1 id=eq.1h2v.s4.d58b9067f06b from=translated src=- shape=9a8155b8 vocab=66fce5a0
-/
theorem listAssign_get_false {l : List ℕ} {v : ℕ} (h : v ∉ l) :
    (listAssign l).get v = false := by
  by_cases hv : v < l.foldr max 0 + 1
  · rw [listAssign, assignOf_get _ hv]; simp [h]
  · simp only [listAssign, assignOf, Assignment.get]
    rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
    rfl

/-- A variable that `listAssign l` reads as `true` must be listed.
@isnad1 id=mem.1h2v.s4.4222ecec0331 from=translated src=- shape=18c8b61a vocab=345ccd2d
-/
theorem listAssign_mem_of_get {l : List ℕ} {v : ℕ} (h : (listAssign l).get v = true) :
    v ∈ l := by
  by_contra hv; rw [listAssign_get_false hv] at h; exact absurd h (by simp)

/-- The configuration of `N` after `t` steps under the choice function `g`. -/
def fcfg (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t : ℕ) : Cfg 1 N.Q :=
  N.trace t (fun i => g i.val) (N.initCfg x)

/-- Symbol on tape `tp` (0=input, 1=work, 2=output) at position `pos` in `fcfg t`. -/
def fcellSym (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t tp pos : ℕ) : Γ :=
  if tp = 0 then (fcfg N x g t).input.cells pos
  else if tp = 1 then ((fcfg N x g t).work 0).cells pos
  else (fcfg N x g t).output.cells pos

/-- Head position of tape `tp` in `fcfg t`. -/
def fheadPos (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t tp : ℕ) : ℕ :=
  if tp = 0 then (fcfg N x g t).input.head
  else if tp = 1 then ((fcfg N x g t).work 0).head
  else (fcfg N x g t).output.head

open Tableau in
/-- The variables that hold of the run `fcfg` (over `steps` steps, positions `≤ P`):
    the one-hot state/cell/head variables and the true choice bits. The forward
    direction's satisfying assignment marks exactly these true. -/
noncomputable def ftraceVars (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) : List ℕ :=
  (List.range (steps + 1)).map (fun t => vState t (stateIdx N (fcfg N x g t).state)) ++
  (List.range steps).filterMap (fun t => if g t then some (vChoice t) else none) ++
  (List.range (steps + 1)).flatMap (fun t => (List.range 3).flatMap (fun tp =>
    (List.range (P + 1)).map (fun pos => vCell t tp pos (symIdx (fcellSym N x g t tp pos))))) ++
  (List.range (steps + 1)).flatMap (fun t => (List.range 3).map (fun tp =>
    vHead t tp (fheadPos N x g t tp)))

open Tableau in
/-- A state variable is in `ftraceVars` iff it names the run's state at an in-range time.
@isnad1 id=iff.0h7v.s6.f3c275719bac from=translated src=- shape=f81aabf4 vocab=c3c5a7ef
-/
theorem vState_mem_ftraceVars (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) {t q : ℕ} :
    vState t q ∈ ftraceVars N x g steps P ↔ t ≤ steps ∧ q = stateIdx N (fcfg N x g t).state := by
  unfold ftraceVars
  simp only [List.mem_append, List.mem_map, List.mem_filterMap, List.mem_flatMap,
    List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (((⟨t', ht', heq⟩ | ⟨t', ht', heq⟩) | ⟨t', ht', tp, htp, pos, hpos, heq⟩) |
      ⟨t', ht', tp, htp, heq⟩)
    · obtain ⟨_, rfl, hq, _, _⟩ := enc_inj heq; exact ⟨ht', hq.symm⟩
    · split at heq
      · exact absurd (enc_inj (Option.some.inj heq)).1 (by decide)
      · simp at heq
    · exact absurd (enc_inj heq).1 (by decide)
    · exact absurd (enc_inj heq).1 (by decide)
  · rintro ⟨ht, rfl⟩
    exact Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩))

open Tableau in
/-- A choice variable is in `ftraceVars` iff its time is in range and its choice bit is true.
@isnad1 id=iff.0h6v.s5.b274f8b765d3 from=translated src=- shape=6674b719 vocab=6c5645a3
-/
theorem vChoice_mem_ftraceVars (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) {t : ℕ} :
    vChoice t ∈ ftraceVars N x g steps P ↔ t < steps ∧ g t = true := by
  unfold ftraceVars
  simp only [List.mem_append, List.mem_map, List.mem_filterMap, List.mem_flatMap,
    List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (((⟨t', ht', heq⟩ | ⟨t', ht', heq⟩) | ⟨t', ht', tp, htp, pos, hpos, heq⟩) |
      ⟨t', ht', tp, htp, heq⟩)
    · exact absurd (enc_inj heq).1 (by decide)
    · split at heq
      · rename_i hg; obtain ⟨_, rfl, _, _, _⟩ := enc_inj (Option.some.inj heq); exact ⟨ht', hg⟩
      · simp at heq
    · exact absurd (enc_inj heq).1 (by decide)
    · exact absurd (enc_inj heq).1 (by decide)
  · rintro ⟨ht, hg⟩
    exact Or.inl (Or.inl (Or.inr ⟨t, ht, by rw [ite_eq_left hg]⟩))

open Tableau in
/-- A cell variable is in `ftraceVars` iff it names the run's symbol at an in-range cell.
@isnad1 id=iff.0h9v.s6.eef31fcd7b9f from=translated src=- shape=dc2edf51 vocab=2f2401d1
-/
theorem vCell_mem_ftraceVars (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t tp pos s : ℕ} :
    vCell t tp pos s ∈ ftraceVars N x g steps P ↔
      t ≤ steps ∧ tp < 3 ∧ pos ≤ P ∧ s = symIdx (fcellSym N x g t tp pos) := by
  unfold ftraceVars
  simp only [List.mem_append, List.mem_map, List.mem_filterMap, List.mem_flatMap,
    List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (((⟨t', ht', heq⟩ | ⟨t', ht', heq⟩) | ⟨t', ht', tp', htp', pos', hpos', heq⟩) |
      ⟨t', ht', tp', htp', heq⟩)
    · exact absurd (enc_inj heq).1 (by decide)
    · split at heq
      · exact absurd (enc_inj (Option.some.inj heq)).1 (by decide)
      · simp at heq
    · obtain ⟨_, rfl, rfl, hc, _⟩ := enc_inj heq
      obtain ⟨rfl, hs⟩ := Nat.pair_eq_pair.mp hc
      exact ⟨ht', by omega, hpos', hs.symm⟩
    · exact absurd (enc_inj heq).1 (by decide)
  · rintro ⟨ht, htp, hpos, rfl⟩
    exact Or.inl (Or.inr ⟨t, ht, tp, htp, pos, hpos, rfl⟩)

open Tableau in
/-- A head variable is in `ftraceVars` iff it names the run's head position at an
    in-range time and tape.
@isnad1 id=iff.0h8v.s6.3b83db87519f from=translated src=- shape=71dd0bc4 vocab=a2b665ab
-/
theorem vHead_mem_ftraceVars (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t tp pos : ℕ} :
    vHead t tp pos ∈ ftraceVars N x g steps P ↔
      t ≤ steps ∧ tp < 3 ∧ pos = fheadPos N x g t tp := by
  unfold ftraceVars
  simp only [List.mem_append, List.mem_map, List.mem_filterMap, List.mem_flatMap,
    List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (((⟨t', ht', heq⟩ | ⟨t', ht', heq⟩) | ⟨t', ht', tp', htp', pos', hpos', heq⟩) |
      ⟨t', ht', tp', htp', heq⟩)
    · exact absurd (enc_inj heq).1 (by decide)
    · split at heq
      · exact absurd (enc_inj (Option.some.inj heq)).1 (by decide)
      · simp at heq
    · exact absurd (enc_inj heq).1 (by decide)
    · obtain ⟨_, rfl, rfl, hp, _⟩ := enc_inj heq
      exact ⟨ht', by omega, hp.symm⟩
  · rintro ⟨ht, htp, rfl⟩
    exact Or.inr ⟨t, ht, tp, htp, rfl⟩

/-- The forward direction's satisfying assignment: mark exactly the run's variables. -/
noncomputable def fassign (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) : Assignment :=
  listAssign (ftraceVars N x g steps P)

open Tableau in
/-- `fassign` sets a state variable true iff it names the run's state (in range).
@isnad1 id=iff.0h7v.s6.3119e888265e from=translated src=- shape=aef1d7da vocab=2378436d
-/
theorem fassign_get_vState (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) {t q : ℕ} :
    (fassign N x g steps P).get (vState t q) = true ↔
      t ≤ steps ∧ q = stateIdx N (fcfg N x g t).state :=
  ⟨fun h => (vState_mem_ftraceVars N x g steps P).mp (listAssign_mem_of_get h),
   fun h => listAssign_get_true ((vState_mem_ftraceVars N x g steps P).mpr h)⟩

open Tableau in
/-- `fassign` sets a choice variable true iff its time is in range and its bit is true.
@isnad1 id=iff.0h6v.s5.1e9e4a84d065 from=translated src=- shape=650cb5e6 vocab=02d6de67
-/
theorem fassign_get_vChoice (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) {t : ℕ} :
    (fassign N x g steps P).get (vChoice t) = true ↔ t < steps ∧ g t = true :=
  ⟨fun h => (vChoice_mem_ftraceVars N x g steps P).mp (listAssign_mem_of_get h),
   fun h => listAssign_get_true ((vChoice_mem_ftraceVars N x g steps P).mpr h)⟩

open Tableau in
/-- `fassign` sets a cell variable true iff it names the run's symbol (in range).
@isnad1 id=iff.0h9v.s6.d1bb51c19d31 from=translated src=- shape=9bb72028 vocab=2a36b467
-/
theorem fassign_get_vCell (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t tp pos s : ℕ} :
    (fassign N x g steps P).get (vCell t tp pos s) = true ↔
      t ≤ steps ∧ tp < 3 ∧ pos ≤ P ∧ s = symIdx (fcellSym N x g t tp pos) :=
  ⟨fun h => (vCell_mem_ftraceVars N x g steps P).mp (listAssign_mem_of_get h),
   fun h => listAssign_get_true ((vCell_mem_ftraceVars N x g steps P).mpr h)⟩

open Tableau in
/-- `fassign` sets a head variable true iff it names the run's head position (in range).
@isnad1 id=iff.0h8v.s6.77f34a448ed4 from=translated src=- shape=80f3cf0e vocab=71979956
-/
theorem fassign_get_vHead (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t tp pos : ℕ} :
    (fassign N x g steps P).get (vHead t tp pos) = true ↔
      t ≤ steps ∧ tp < 3 ∧ pos = fheadPos N x g t tp :=
  ⟨fun h => (vHead_mem_ftraceVars N x g steps P).mp (listAssign_mem_of_get h),
   fun h => listAssign_get_true ((vHead_mem_ftraceVars N x g steps P).mpr h)⟩

/-- After `t` steps every head position is at most `t`.
@isnad1 id=le.0h5v.s4.1850ea0c7910 from=translated src=- shape=15465078 vocab=e9ddaed0
-/
theorem fheadPos_le (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t tp : ℕ) :
    fheadPos N x g t tp ≤ t := by
  obtain ⟨hi, hw, ho⟩ := trace_heads_le N g x t
  unfold fheadPos fcfg
  split_ifs <;> assumption

/-- At time `0` every head is at cell `0`.
@isnad1 id=eq.0h4v.s5.173da5ccb093 from=translated src=- shape=9a4ea9cb vocab=d693eb6a
-/
theorem fheadPos_zero (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (tp : ℕ) :
    fheadPos N x g 0 tp = 0 := by
  unfold fheadPos fcfg
  split_ifs <;> simp [NTM.trace, NTM.initCfg, Cfg.init, Tape.init]

open Tableau in
/-- At time `0` every cell of the run holds its `initCellSym` value.
@isnad1 id=eq.0h5v.s5.ca93586e068a from=translated src=- shape=df71aaaf vocab=dbf5d636
-/
theorem fcellSym_zero (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (tp pos : ℕ) :
    fcellSym N x g 0 tp pos = initCellSym x tp pos := by
  unfold fcellSym fcfg
  split_ifs with h0 h1
  · subst h0; simp [NTM.trace, NTM.initCfg, Cfg.init, Tape.init, initCellSym]
  · subst h1; simp [NTM.trace, NTM.initCfg, Cfg.init, Tape.init, initCellSym]
  · simp [NTM.trace, NTM.initCfg, Cfg.init, Tape.init, initCellSym, h0]

open Tableau in
/-- `fassign` satisfies the start clauses (with `P = steps + |x| + 1`).
@isnad1 id=eq.1h5v.s6.02be34a05cf4 from=translated src=- shape=336e977f vocab=dd7b80f6
-/
theorem fassign_startClauses (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    (hP : steps + x.length + 1 = P) :
    CNF.eval (fassign N x g steps P) (startClauses N steps x) = true := by
  rw [startClauses_sat]
  refine ⟨?_, fun tp htp => ?_, fun tp htp pos hpos => ?_⟩
  · rw [fassign_get_vState]; exact ⟨Nat.zero_le _, rfl⟩
  · rw [fassign_get_vHead]; exact ⟨Nat.zero_le _, htp, (fheadPos_zero N x g tp).symm⟩
  · rw [fassign_get_vCell]
    exact ⟨Nat.zero_le _, htp, hP ▸ hpos, by rw [fcellSym_zero]⟩

/-- Peel the last step: `fcfg (t + 1)` is one `traceStep` from `fcfg t`.
@isnad1 id=eq.0h4v.s5.44422c45d583 from=translated src=- shape=4332fde3 vocab=660892ea
-/
theorem fcfg_succ (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t : ℕ) :
    fcfg N x g (t + 1) = traceStep N (fcfg N x g t) (g t) :=
  trace_succ_eq N g t (N.initCfg x)

/-- `traceStep` never changes an input-tape cell (the input tape is read-only).
@isnad1 id=eq.0h4v.s5.63384644512b from=translated src=- shape=7e9dc62d vocab=a44a1d72
-/
theorem traceStep_input_cells (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool) (pos : ℕ) :
    (traceStep N c b).input.cells pos = c.input.cells pos := by
  unfold traceStep; split_ifs with hq
  · rfl
  · rw [Tape.move_cells]

/-- `traceStep` leaves every work-tape cell other than the work head's unchanged.
@isnad1 id=eq.1h4v.s7.1584fbce4e97 from=translated src=- shape=513f4e1d vocab=0ccd93cf
-/
theorem traceStep_work_cells_ne (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool) {pos : ℕ}
    (h : pos ≠ (c.work 0).head) : ((traceStep N c b).work 0).cells pos = (c.work 0).cells pos := by
  unfold traceStep; split_ifs with hq
  · rfl
  · exact tape_writeAndMove_cells_ne (c.work 0) _ _ h

/-- `traceStep` leaves every output-tape cell other than the output head's unchanged.
@isnad1 id=eq.1h4v.s6.cdb4deb07a7d from=translated src=- shape=a514f6db vocab=abcc3382
-/
theorem traceStep_output_cells_ne (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool) {pos : ℕ}
    (h : pos ≠ c.output.head) : (traceStep N c b).output.cells pos = c.output.cells pos := by
  unfold traceStep; split_ifs with hq
  · rfl
  · exact tape_writeAndMove_cells_ne c.output _ _ h

section traceStepFields
variable (N : NTM 1) (c : Cfg 1 N.Q) (b : Bool)

private theorem ts_hout : (fun i : Fin 1 => (c.work i).read) = fun _ => (c.work 0).read := by
  funext i; rw [Subsingleton.elim i 0]

/-- The state after `traceStep`: unchanged when halted, otherwise `N.δ`'s next state.
@isnad1 id=eq.0h3v.s7.8f4dd37f45ea from=translated src=- shape=1dcc6e20 vocab=6e0779a1
-/
theorem traceStep_state : (traceStep N c b).state =
    if c.state = N.qhalt then c.state
    else (N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).1 := by
  unfold traceStep; rw [ts_hout]; split_ifs <;> rfl

/-- The input head after `traceStep`: unchanged when halted, otherwise moved per `N.δ`
    (`posMove`).
@isnad1 id=eq.0h3v.s8.543e0765c944 from=translated src=- shape=5277266a vocab=4de570ef
-/
theorem traceStep_input_head : (traceStep N c b).input.head =
    if c.state = N.qhalt then c.input.head
    else Tableau.posMove c.input.head
      (N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).2.2.2.1 := by
  unfold traceStep; rw [ts_hout]; split_ifs with hq
  · rfl
  · exact tape_move_head c.input _

/-- The work head after `traceStep`: unchanged when halted, otherwise moved per `N.δ`
    (`posMove`).
@isnad1 id=eq.0h3v.s8.cd6a2fd742a0 from=translated src=- shape=1d4222c8 vocab=4de570ef
-/
theorem traceStep_work_head : ((traceStep N c b).work 0).head =
    if c.state = N.qhalt then (c.work 0).head
    else Tableau.posMove (c.work 0).head
      ((N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).2.2.2.2.1 0) := by
  unfold traceStep; rw [ts_hout]; split_ifs with hq
  · rfl
  · exact tape_writeAndMove_head (c.work 0) _ _

/-- The output head after `traceStep`: unchanged when halted, otherwise moved per `N.δ`
    (`posMove`).
@isnad1 id=eq.0h3v.s8.785829862a74 from=translated src=- shape=7f429e7d vocab=42702ec6
-/
theorem traceStep_output_head : (traceStep N c b).output.head =
    if c.state = N.qhalt then c.output.head
    else Tableau.posMove c.output.head
      (N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).2.2.2.2.2 := by
  unfold traceStep; rw [ts_hout]; split_ifs with hq
  · rfl
  · exact tape_writeAndMove_head c.output _ _

/-- The work cell under the head after `traceStep`: unchanged when halted or at cell `0`
    (writes there are no-ops), otherwise the symbol `N.δ` writes.
@isnad1 id=eq.0h3v.s8.cea681d09c04 from=translated src=- shape=5acfae6f vocab=8e009523
-/
theorem traceStep_work_cells_self : ((traceStep N c b).work 0).cells (c.work 0).head =
    if c.state = N.qhalt then (c.work 0).read
    else if (c.work 0).head = 0 then (c.work 0).read
    else ((N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).2.1 0).toΓ := by
  unfold traceStep; rw [ts_hout]; split_ifs with hq h0
  · rfl
  · rw [tape_writeAndMove_cells_self, ite_eq_left h0]; rfl
  · rw [tape_writeAndMove_cells_self, ite_eq_right h0]

/-- The output cell under the head after `traceStep`: unchanged when halted or at cell `0`
    (writes there are no-ops), otherwise the symbol `N.δ` writes.
@isnad1 id=eq.0h3v.s8.9c656a54d7e5 from=translated src=- shape=9e2203e8 vocab=8e009523
-/
theorem traceStep_output_cells_self : (traceStep N c b).output.cells c.output.head =
    if c.state = N.qhalt then c.output.read
    else if c.output.head = 0 then c.output.read
    else (N.δ b c.state c.input.read (fun _ => (c.work 0).read) c.output.read).2.2.1.toΓ := by
  unfold traceStep; rw [ts_hout]; split_ifs with hq h0
  · rfl
  · rw [tape_writeAndMove_cells_self, ite_eq_left h0]; rfl
  · rw [tape_writeAndMove_cells_self, ite_eq_right h0]

end traceStepFields

/-- In the run, a cell not under its tape's head keeps its symbol from time `t` to `t+1`.
@isnad1 id=eq.1h6v.s5.cdb015f49bf6 from=translated src=- shape=81edfa95 vocab=985183fc
-/
theorem fcellSym_succ_ne (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (t tp pos : ℕ)
    (h : pos ≠ fheadPos N x g t tp) :
    fcellSym N x g (t + 1) tp pos = fcellSym N x g t tp pos := by
  unfold fcellSym; rw [fcfg_succ]; unfold fheadPos at h
  split_ifs at h ⊢ with h0 h1
  · exact traceStep_input_cells N (fcfg N x g t) (g t) pos
  · exact traceStep_work_cells_ne N (fcfg N x g t) (g t) h
  · exact traceStep_output_cells_ne N (fcfg N x g t) (g t) h

open Tableau in
/-- `fassign` satisfies the acceptance clauses when the run halts at time `steps` with
    output cell `1` holding `1`.
@isnad1 id=eq.3h5v.s6.c0d3935f3c12 from=translated src=- shape=ad00496d vocab=74e6a292
-/
theorem fassign_acceptClauses (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    (hP : 1 ≤ P) (hhalt : (fcfg N x g steps).state = N.qhalt)
    (hout : (fcfg N x g steps).output.cells 1 = Γ.one) :
    CNF.eval (fassign N x g steps P) (acceptClauses N steps) = true := by
  rw [acceptClauses_sat]
  refine ⟨?_, ?_⟩
  · rw [fassign_get_vState]; exact ⟨le_refl _, by rw [hhalt]⟩
  · rw [fassign_get_vCell]
    refine ⟨le_refl _, by norm_num, hP, ?_⟩
    congr 1
    unfold fcellSym
    rw [ite_eq_right (by decide : ¬(2:ℕ) = 0), ite_eq_right (by decide : ¬(2:ℕ) = 1)]
    exact hout.symm

open Tableau in
/-- On in-range cell variables, `fassign` reads `true` exactly when the symbol index is
    the run's symbol at that cell.
@isnad1 id=eq.3h9v.s6.ec4f0c44cea6 from=translated src=- shape=83d6d5bb vocab=6ed4b4c5
-/
theorem fassign_get_vCell_eq (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t tp pos s : ℕ} (ht : t ≤ steps) (htp : tp < 3) (hpos : pos ≤ P) :
    (fassign N x g steps P).get (vCell t tp pos s) =
      decide (s = symIdx (fcellSym N x g t tp pos)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, fassign_get_vCell]
  exact ⟨fun h => h.2.2.2, fun h => ⟨ht, htp, hpos, h⟩⟩

open Tableau in
/-- `fassign` satisfies the frame clauses: in the run, off-head cells keep their symbols.
@isnad1 id=eq.0h5v.s5.8fe872adc874 from=translated src=- shape=c7dd0e07 vocab=9ee08b14
-/
theorem fassign_frameClauses (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) :
    CNF.eval (fassign N x g steps P) (frameClauses 1 steps P) = true := by
  rw [frameClauses_sat]
  intro t ht tp htp pos hpos s hs hhead
  have hne : pos ≠ fheadPos N x g t tp := by
    intro he
    rw [(fassign_get_vHead N x g steps P).mpr ⟨by omega, by omega, he⟩] at hhead
    exact Bool.noConfusion hhead
  have e1 := fassign_get_vCell_eq N x g steps P (t := t) (tp := tp) (pos := pos) (s := s)
    (by omega) (by omega) hpos
  have e2 := fassign_get_vCell_eq N x g steps P (t := t + 1) (tp := tp) (pos := pos) (s := s)
    (by omega) (by omega) hpos
  rw [e1, e2, fcellSym_succ_ne N x g t tp pos hne]

open Tableau in
/-- On in-range choice variables, `fassign` reads back the choice function `g`.
@isnad1 id=eq.1h6v.s5.f7b7cc26a49f from=translated src=- shape=154bddcf vocab=907264c0
-/
theorem fassign_get_vChoice_eq (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    {t : ℕ} (ht : t < steps) : (fassign N x g steps P).get (vChoice t) = g t := by
  rw [Bool.eq_iff_iff, fassign_get_vChoice]
  exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

open Tableau in
/-- `fassign` satisfies each `activeClausesAt` block: either the read-config does not match
    the run (some condition literal is true), or it does and the consequence variables hold
    because the run takes exactly that `traceStep`.
@isnad1 id=eq.4h14v.s6.1ed91d4f0a5c from=translated src=- shape=7b145141 vocab=5a19f9c0
-/
theorem fassign_activeClausesAt (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ)
    (t : ℕ) (ht : t < steps) (q : N.Q) (pi : ℕ) (hpi : pi ≤ P) (si : Γ) (pw : ℕ) (hpw : pw ≤ P)
    (sw : Γ) (po : ℕ) (hpo : po ≤ P) (so : Γ) (b : Bool) :
    CNF.eval (fassign N x g steps P) (activeClausesAt N t q pi si pw sw po so b) = true := by
  by_cases hcond : (activeCond N t q pi si pw sw po so b).any
      (Lit.eval (fassign N x g steps P)) = true
  · simp only [activeClausesAt, CNF.eval, List.all_cons, List.all_nil, Bool.and_true,
      Clause.eval, List.any_append, hcond, Bool.true_or]
  · rw [Bool.not_eq_true] at hcond
    have hfacts := hcond
    simp only [activeCond, List.any_cons, List.any_nil, Bool.or_eq_false_iff, Lit.eval,
      beq_eq_false_iff_ne, ne_eq, Bool.not_eq_false] at hfacts
    obtain ⟨hsv, hhi, hcvi, hhw, hcvw, hho, hcvo, hbv, _⟩ := hfacts
    -- decode the read-config: the tuple equals `fcfg t`'s state/heads/reads and `b = g t`
    have hq : q = (fcfg N x g t).state :=
      stateIdx_inj N ((fassign_get_vState N x g steps P).mp hsv).2
    have hpi : pi = (fcfg N x g t).input.head := ((fassign_get_vHead N x g steps P).mp hhi).2.2
    have hpw : pw = ((fcfg N x g t).work 0).head := ((fassign_get_vHead N x g steps P).mp hhw).2.2
    have hpo : po = (fcfg N x g t).output.head := ((fassign_get_vHead N x g steps P).mp hho).2.2
    have hsi : si = (fcfg N x g t).input.read := by
      rw [symIdx_inj ((fassign_get_vCell N x g steps P).mp hcvi).2.2.2]
      unfold fcellSym Tape.read; rw [ite_eq_left rfl, hpi]
    have hsw : sw = ((fcfg N x g t).work 0).read := by
      rw [symIdx_inj ((fassign_get_vCell N x g steps P).mp hcvw).2.2.2]
      unfold fcellSym Tape.read; rw [ite_eq_right (by decide : (1:ℕ) ≠ 0), ite_eq_left rfl, hpw]
    have hso : so = (fcfg N x g t).output.read := by
      rw [symIdx_inj ((fassign_get_vCell N x g steps P).mp hcvo).2.2.2]
      unfold fcellSym Tape.read
      rw [ite_eq_right (by decide : (2:ℕ) ≠ 0), ite_eq_right (by decide : (2:ℕ) ≠ 1), hpo]
    have hb : b = g t := by
      have hbv' : (fassign N x g steps P).get (vChoice t) = b := by
        cases hgc : (fassign N x g steps P).get (vChoice t) <;> cases b <;> simp_all
      rw [← hbv', fassign_get_vChoice_eq N x g steps P ht]
    subst hq hpi hpw hpo hsi hsw hso hb
    simp only [activeClausesAt, CNF.eval, List.all_cons, List.all_nil, Clause.eval,
      List.any_append, hcond, Bool.false_or, List.any_cons, List.any_nil, Bool.or_false,
      Lit.eval, beq_iff_eq, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (fassign_get_vState N x g steps P).mpr ⟨by omega, by rw [fcfg_succ, traceStep_state]⟩
    · refine (fassign_get_vCell N x g steps P).mpr ⟨by omega, by omega, hpi, ?_⟩
      congr 1; unfold fcellSym Tape.read; rw [ite_eq_left rfl, fcfg_succ, traceStep_input_cells]
    · refine (fassign_get_vCell N x g steps P).mpr ⟨by omega, by omega, hpw, ?_⟩
      congr 1; unfold fcellSym
      rw [ite_eq_right (by decide : (1:ℕ) ≠ 0), ite_eq_left rfl, fcfg_succ,
        traceStep_work_cells_self]
    · refine (fassign_get_vCell N x g steps P).mpr ⟨by omega, by omega, hpo, ?_⟩
      congr 1; unfold fcellSym
      rw [ite_eq_right (by decide : (2:ℕ) ≠ 0), ite_eq_right (by decide : (2:ℕ) ≠ 1), fcfg_succ,
        traceStep_output_cells_self]
    · refine (fassign_get_vHead N x g steps P).mpr ⟨by omega, by omega, ?_⟩
      unfold fheadPos; rw [ite_eq_left rfl, fcfg_succ, traceStep_input_head]
    · refine (fassign_get_vHead N x g steps P).mpr ⟨by omega, by omega, ?_⟩
      unfold fheadPos
      rw [ite_eq_right (by decide : (1:ℕ) ≠ 0), ite_eq_left rfl, fcfg_succ, traceStep_work_head]
    · refine (fassign_get_vHead N x g steps P).mpr ⟨by omega, by omega, ?_⟩
      unfold fheadPos
      rw [ite_eq_right (by decide : (2:ℕ) ≠ 0), ite_eq_right (by decide : (2:ℕ) ≠ 1), fcfg_succ,
        traceStep_output_head]

open Tableau in
/-- `fassign` satisfies the active transition clauses.
@isnad1 id=eq.0h5v.s5.09fcbf6a4be1 from=translated src=- shape=c4168f7d vocab=a98476de
-/
theorem fassign_activeTransitionClauses (N : NTM 1) (x : List Bool) (g : ℕ → Bool) (steps P : ℕ) :
    CNF.eval (fassign N x g steps P) (activeTransitionClauses N steps P) = true := by
  rw [activeTransitionClauses_sat]
  exact fun t ht q pi hpi si pw hpw sw po hpo so b =>
    fassign_activeClausesAt N x g steps P t ht q pi hpi si pw hpw sw po hpo so b

/-- An encoded CNF is in `language` iff it is satisfiable (`CNF.encode` is injective,
    via `CNF.decode?_encode`).
@isnad1 id=iff.0h1v.s3.7ccd14133c75 from=translated src=- shape=0daa9ccf vocab=26ceaf1e
-/
theorem encode_mem_LSAT_iff (φ : CNF) : φ.encode ∈ language ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨φ', hφ', hsat⟩
    have hφ : φ = φ' := by
      have h := CNF.decode?_encode φ
      rw [hφ'] at h
      exact Option.some.inj (h.symm.trans (CNF.decode?_encode φ'))
    rw [hφ]; exact hsat
  · exact fun hsat => ⟨φ, rfl, hsat⟩

/-! ### Flat variable re-indexing

The `enc`-based variable indices are `Nat.pair` towers — convenient for the
injectivity bookkeeping of the correctness proof, but a Turing machine
computing them would need comparison-and-branch arithmetic. The *flat*
mixed-radix scheme below needs only multiplication and addition (unary
machine-trivial), and transports satisfiability along the injective
re-encoding `flatToEnc` (`SAT.CNF.satisfiable_mapVar_iff`). The reduction
emits the flat formula. -/

namespace Tableau

/-- Mixed-radix flat variable index: `tag` at the top, then components
    `(a, b, c, d)` with radices `(A, B, C, D)`. -/
def flatVar (A B C D tag a b c d : ℕ) : ℕ :=
  (((tag * A + a) * B + b) * C + c) * D + d

/-- One mixed-radix layer decodes: the remainder is the digit, the quotient
    the rest. -/
private theorem layer_decode {X d D : ℕ} (hd : d < D) :
    (X * D + d) % D = d ∧ (X * D + d) / D = X := by
  constructor
  · rw [Nat.mul_comm X D, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  · rw [Nat.mul_comm X D, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hd, Nat.add_zero]

/-- The flat components decode by iterated division and remainder.
@isnad1 id=and.4h9v.s7.257539494da6 from=translated src=- shape=d1076bea vocab=83fbab49
-/
theorem flatVar_decode {A B C D tag a b c d : ℕ}
    (ha : a < A) (hb : b < B) (hc : c < C) (hd : d < D) :
    flatVar A B C D tag a b c d % D = d ∧
    flatVar A B C D tag a b c d / D % C = c ∧
    flatVar A B C D tag a b c d / D / C % B = b ∧
    flatVar A B C D tag a b c d / D / C / B % A = a ∧
    flatVar A B C D tag a b c d / D / C / B / A = tag := by
  obtain ⟨h1, h1'⟩ := layer_decode (X := (tag * A + a) * B + b) (d := c) hc
  obtain ⟨h2, h2'⟩ := layer_decode (X := tag * A + a) (d := b) hb
  obtain ⟨h3, h3'⟩ := layer_decode (X := tag) (d := a) ha
  obtain ⟨h0, h0'⟩ := layer_decode (X := ((tag * A + a) * B + b) * C + c) (d := d) hd
  exact ⟨h0, by rw [flatVar, h0', h1], by rw [flatVar, h0', h1', h2],
    by rw [flatVar, h0', h1', h2', h3], by rw [flatVar, h0', h1', h2', h3']⟩

/-- Mixed-radix re-composition is the identity (unconditionally — the
    div/mod identity at each layer).
@isnad1 id=eq.0h5v.s7.e1da57786abe from=translated src=- shape=098579d5 vocab=8d19e913
-/
theorem flatVar_recompose (A B C D v : ℕ) :
    flatVar A B C D (v / D / C / B / A) (v / D / C / B % A) (v / D / C % B)
      (v / D % C) (v % D) = v := by
  have l1 : ∀ w m : ℕ, (w / m) * m + w % m = w := fun w m => by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod w m
  rw [flatVar, l1 (v / D / C / B) A, l1 (v / D / C) B, l1 (v / D) C, l1 v D]

/-- **The injective re-encoding** from flat indices to the `Nat.pair`-based
    `enc` indices: decode the mixed-radix components, re-encode per tag
    (tag `2` — the cell variables — pairs its position and symbol, matching
    `vCell`). -/
def flatToEnc (A B C D : ℕ) (v : ℕ) : ℕ :=
  if v / D / C / B / A = 2 then
    enc 2 (v / D / C / B % A) (v / D / C % B) (Nat.pair (v / D % C) (v % D)) 0
  else
    enc (v / D / C / B / A) (v / D / C / B % A) (v / D / C % B) (v / D % C) (v % D)

/-- `flatToEnc` is injective: the mixed-radix components recompose the flat index.
@isnad1 id=injectiv.0h4v.s4.9cc65ea9ee1c from=translated src=- shape=b43e9b92 vocab=f68bc291
-/
theorem flatToEnc_injective (A B C D : ℕ) :
    Function.Injective (flatToEnc A B C D) := by
  intro v v' h
  simp only [flatToEnc] at h
  split at h <;> split at h
  · -- both tag 2
    next ht ht' =>
      obtain ⟨-, ha, hb, hcd, -⟩ := enc_inj h
      obtain ⟨hc, hd⟩ := Nat.pair_eq_pair.mp hcd
      rw [← flatVar_recompose A B C D v, ← flatVar_recompose A B C D v',
        ht, ht', ha, hb, hc, hd]
  · next ht ht' => exact absurd (enc_inj h).1.symm ht'
  · next ht ht' => exact absurd (enc_inj h).1 ht
  · next ht ht' =>
      obtain ⟨htag, ha, hb, hc, hd⟩ := enc_inj h
      rw [← flatVar_recompose A B C D v, ← flatVar_recompose A B C D v',
        htag, ha, hb, hc, hd]

section FlatVars

-- Flat-variable moduli for a tableau with `Qc` states, `steps` time-steps,
-- and positions `≤ P + 1` (head-move consequences reach `P + 1`).
variable (Qc steps P : ℕ)

/-- Flat tableau variables: same roles as `vState`/`vChoice`/`vCell`/`vHead`,
    mixed-radix indices. -/
def vStateF (t q : ℕ) : ℕ := flatVar (steps + 1) (max Qc 3) (P + 2) 4 0 t q 0 0
@[inherit_doc vStateF]
def vChoiceF (t : ℕ) : ℕ := flatVar (steps + 1) (max Qc 3) (P + 2) 4 1 t 0 0 0
@[inherit_doc vStateF]
def vCellF (t tp pos s : ℕ) : ℕ := flatVar (steps + 1) (max Qc 3) (P + 2) 4 2 t tp pos s
@[inherit_doc vStateF]
def vHeadF (t tp pos : ℕ) : ℕ := flatVar (steps + 1) (max Qc 3) (P + 2) 4 3 t tp pos 0

/-- `flatToEnc` carries each in-range flat variable to its `enc` counterpart.
@isnad1 id=eq.2h5v.s6.d4b64343600f from=translated src=- shape=6f39b939 vocab=772db448
-/
theorem flatToEnc_vStateF {t q : ℕ} (ht : t ≤ steps) (hq : q < Qc) :
    flatToEnc (steps + 1) (max Qc 3) (P + 2) 4 (vStateF Qc steps P t q) = vState t q := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := flatVar_decode (A := steps + 1) (B := max Qc 3)
    (C := P + 2) (D := 4) (tag := 0) (a := t) (b := q) (c := 0) (d := 0)
    (by omega) (lt_of_lt_of_le hq (le_max_left _ _)) (by omega) (by omega)
  rw [vStateF, flatToEnc, ite_eq_right (by rw [h4]; omega), h4, h3, h2, h1, h0, vState]

/--
@isnad1 id=eq.1h4v.s6.63f547af7cba from=translated src=- shape=0ee4ab6a vocab=806fce27
-/
@[inherit_doc flatToEnc_vStateF]
theorem flatToEnc_vChoiceF {t : ℕ} (ht : t ≤ steps) :
    flatToEnc (steps + 1) (max Qc 3) (P + 2) 4 (vChoiceF Qc steps P t) = vChoice t := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := flatVar_decode (A := steps + 1) (B := max Qc 3)
    (C := P + 2) (D := 4) (tag := 1) (a := t) (b := 0) (c := 0) (d := 0)
    (by omega) (by omega) (by omega) (by omega)
  rw [vChoiceF, flatToEnc, ite_eq_right (by rw [h4]; omega), h4, h3, h2, h1, h0, vChoice]

/--
@isnad1 id=eq.4h7v.s6.eb63d3b21f9b from=translated src=- shape=8fadbabd vocab=901094db
-/
@[inherit_doc flatToEnc_vStateF]
theorem flatToEnc_vCellF {t tp pos s : ℕ} (ht : t ≤ steps) (htp : tp < 3)
    (hpos : pos < P + 2) (hs : s < 4) :
    flatToEnc (steps + 1) (max Qc 3) (P + 2) 4 (vCellF Qc steps P t tp pos s)
      = vCell t tp pos s := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := flatVar_decode (A := steps + 1) (B := max Qc 3)
    (C := P + 2) (D := 4) (tag := 2) (a := t) (b := tp) (c := pos) (d := s)
    (by omega) (lt_of_lt_of_le htp (le_max_right _ _)) hpos hs
  rw [vCellF, flatToEnc, ite_eq_left h4, h3, h2, h1, h0, vCell]

/--
@isnad1 id=eq.3h6v.s6.d7aab02ab063 from=translated src=- shape=c3f482c1 vocab=53b8e77b
-/
@[inherit_doc flatToEnc_vStateF]
theorem flatToEnc_vHeadF {t tp pos : ℕ} (ht : t ≤ steps) (htp : tp < 3)
    (hpos : pos < P + 2) :
    flatToEnc (steps + 1) (max Qc 3) (P + 2) 4 (vHeadF Qc steps P t tp pos)
      = vHead t tp pos := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := flatVar_decode (A := steps + 1) (B := max Qc 3)
    (C := P + 2) (D := 4) (tag := 3) (a := t) (b := tp) (c := pos) (d := 0)
    (by omega) (lt_of_lt_of_le htp (le_max_right _ _)) hpos (by omega)
  rw [vHeadF, flatToEnc, ite_eq_right (by rw [h4]; omega), h4, h3, h2, h1, h0, vHead]

end FlatVars

-- ── Renaming plumbing ──────────────────────────────────────────────────────

private theorem flatMap_congr' {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- `CNF.mapVar` distributes over `flatMap`.
@isnad1 id=eq.0h4v.s5.987b3f6b54a2 from=translated src=- shape=8c867ec1 vocab=8104c177
-/
theorem mapVar_flatMap {α : Type _} (f : ℕ → ℕ) (l : List α) (g : α → CNF) :
    CNF.mapVar f (l.flatMap g) = l.flatMap (fun a => CNF.mapVar f (g a)) :=
  List.map_flatMap ..

/-- Variable renaming commutes with `atLeastOne`.
@isnad1 id=eq.0h2v.s4.6f2fd32d1909 from=translated src=- shape=a8d82793 vocab=5250fa64
-/
theorem mapVar_atLeastOne (f : ℕ → ℕ) (vars : List ℕ) :
    Clause.mapVar f (atLeastOne vars) = atLeastOne (vars.map f) := by
  simp [Clause.mapVar, atLeastOne, List.map_map, Function.comp_def, Lit.mapVar]

/-- Variable renaming commutes with `atMostOne`.
@isnad1 id=eq.0h2v.s4.48a2eea7611b from=translated src=- shape=a8d82793 vocab=dad44dfa
-/
theorem mapVar_atMostOne (f : ℕ → ℕ) (vars : List ℕ) :
    CNF.mapVar f (atMostOne vars) = atMostOne (vars.map f) := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    show CNF.mapVar f
        (vs.map (fun w => ([⟨false, v⟩, ⟨false, w⟩] : Clause)) ++ atMostOne vs)
      = (vs.map f).map (fun w => ([⟨false, f v⟩, ⟨false, w⟩] : Clause))
          ++ atMostOne (vs.map f)
    rw [CNF.mapVar_append, ih]
    congr 1
    rw [CNF.mapVar, List.map_map, List.map_map]
    exact List.map_congr_left fun w _ => rfl

/-- Variable renaming commutes with `exactlyOne`.
@isnad1 id=eq.0h2v.s4.7897197a4d11 from=translated src=- shape=a8d82793 vocab=8b463d49
-/
theorem mapVar_exactlyOne (f : ℕ → ℕ) (vars : List ℕ) :
    CNF.mapVar f (exactlyOne vars) = exactlyOne (vars.map f) := by
  rw [exactlyOne, exactlyOne, ← mapVar_atLeastOne f vars, ← mapVar_atMostOne f vars]
  rfl

/-- A head move lands within one cell of where it started.
@isnad1 id=le.0h2v.s4.90177541f525 from=translated src=- shape=44408379 vocab=c3772d2d
-/
theorem posMove_le_succ (pos : ℕ) (d : Dir3) : posMove pos d ≤ pos + 1 := by
  cases d
  · exact le_trans (Nat.sub_le pos 1) (Nat.le_succ pos)
  · exact le_refl _
  · exact Nat.le_succ pos

-- ── The flat tableau families ──────────────────────────────────────────────

/-- Flat-variable mirror of `oneHotStates`. -/
noncomputable def oneHotStatesF (N : NTM 1) (steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    exactlyOne ((List.range (Fintype.card N.Q)).map
      (vStateF (Fintype.card N.Q) steps P t))

/-- Flat-variable mirror of `oneHotCells` (at `k = 1`). -/
def oneHotCellsF (Qc steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (1 + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        exactlyOne ((List.range 4).map (vCellF Qc steps P t tp pos))

/-- Flat-variable mirror of `oneHotHeads` (at `k = 1`). -/
def oneHotHeadsF (Qc steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (1 + 2)).flatMap fun tp =>
      exactlyOne ((List.range (P + 1)).map (vHeadF Qc steps P t tp))

/-- Flat-variable mirror of `startClauses` (at `k = 1`). -/
noncomputable def startClausesF (N : NTM 1) (steps : ℕ) (x : List Bool) :
    List Clause :=
  let P := steps + x.length + 1
  let Qc := Fintype.card N.Q
  ([⟨true, vStateF Qc steps P 0 (stateIdx N N.qstart)⟩] : Clause) ::
    ((List.range (1 + 2)).map (fun tp => ([⟨true, vHeadF Qc steps P 0 tp 0⟩] : Clause)) ++
     (List.range (1 + 2)).flatMap (fun tp =>
       (List.range (P + 1)).map (fun pos =>
         ([⟨true, vCellF Qc steps P 0 tp pos (symIdx (initCellSym x tp pos))⟩] : Clause))))

/-- Flat-variable mirror of `acceptClauses` (at `k = 1`). -/
noncomputable def acceptClausesF (N : NTM 1) (steps P : ℕ) : List Clause :=
  [[⟨true, vStateF (Fintype.card N.Q) steps P steps (stateIdx N N.qhalt)⟩],
   [⟨true, vCellF (Fintype.card N.Q) steps P steps (1 + 1) 1 (symIdx Γ.one)⟩]]

-- ── The flat families map onto the `enc` families ──────────────────────────

section FamilyEq

variable (N : NTM 1) (steps P : ℕ)

/-- The re-encoding at this tableau's moduli. -/
noncomputable def encOf : ℕ → ℕ :=
  flatToEnc (steps + 1) (max (Fintype.card N.Q) 3) (P + 2) 4

/-- `encOf` is injective (it is `flatToEnc` at fixed moduli).
@isnad1 id=injectiv.0h3v.s4.e775a720d94a from=translated src=- shape=7713f799 vocab=0e091d47
-/
theorem encOf_injective : Function.Injective (encOf N steps P) :=
  flatToEnc_injective ..

/-- Re-indexing by `encOf` carries `oneHotStatesF` to `oneHotStates`.
@isnad1 id=eq.0h3v.s4.a042a4f687ad from=translated src=- shape=5167c313 vocab=346765ef
-/
theorem mapVar_oneHotStatesF :
    CNF.mapVar (encOf N steps P) (oneHotStatesF N steps P) = oneHotStates N steps := by
  rw [oneHotStatesF, oneHotStates, encOf, mapVar_flatMap]
  refine flatMap_congr' fun t ht => ?_
  rw [mapVar_exactlyOne, List.map_map]
  congr 1
  refine List.map_congr_left fun q hq => ?_
  rw [List.mem_range] at ht hq
  exact flatToEnc_vStateF _ _ _ (by omega) hq

/-- Re-indexing by `encOf` carries `oneHotCellsF` to `oneHotCells`.
@isnad1 id=eq.0h3v.s5.caa53a3028f5 from=translated src=- shape=2649fce0 vocab=ba33805d
-/
theorem mapVar_oneHotCellsF :
    CNF.mapVar (encOf N steps P) (oneHotCellsF (Fintype.card N.Q) steps P)
      = oneHotCells 1 steps P := by
  rw [oneHotCellsF, oneHotCells, encOf, mapVar_flatMap]
  refine flatMap_congr' fun t ht => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun tp htp => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun pos hpos => ?_
  rw [mapVar_exactlyOne, List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  rw [List.mem_range] at ht htp hpos hs
  exact flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (by omega)

/-- Re-indexing by `encOf` carries `oneHotHeadsF` to `oneHotHeads`.
@isnad1 id=eq.0h3v.s5.382b483be09e from=translated src=- shape=2649fce0 vocab=f6e765cf
-/
theorem mapVar_oneHotHeadsF :
    CNF.mapVar (encOf N steps P) (oneHotHeadsF (Fintype.card N.Q) steps P)
      = oneHotHeads 1 steps P := by
  rw [oneHotHeadsF, oneHotHeads, encOf, mapVar_flatMap]
  refine flatMap_congr' fun t ht => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun tp htp => ?_
  rw [mapVar_exactlyOne, List.map_map]
  congr 1
  refine List.map_congr_left fun pos hpos => ?_
  rw [List.mem_range] at ht htp hpos
  exact flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega)

/-- Re-indexing by `encOf` carries `acceptClausesF` to `acceptClauses`.
@isnad1 id=eq.0h3v.s4.3bbd11372931 from=translated src=- shape=5167c313 vocab=c21376f4
-/
theorem mapVar_acceptClausesF :
    CNF.mapVar (encOf N steps P) (acceptClausesF N steps P) = acceptClauses N steps := by
  rw [acceptClausesF, acceptClauses, encOf]
  simp only [CNF.mapVar, Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
  rw [flatToEnc_vStateF _ _ _ (le_refl _) (stateIdx_lt N _),
    flatToEnc_vCellF _ _ _ (le_refl _) (by omega) (by omega) (symIdx_lt _)]

/-- Flat-variable mirror of `frameClauses` (at `k = 1`). -/
def frameClausesF (Qc steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (List.range (1 + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        (List.range 4).flatMap fun s =>
          [([⟨true, vHeadF Qc steps P t tp pos⟩, ⟨false, vCellF Qc steps P t tp pos s⟩,
              ⟨true, vCellF Qc steps P (t + 1) tp pos s⟩] : Clause),
           ([⟨true, vHeadF Qc steps P t tp pos⟩, ⟨true, vCellF Qc steps P t tp pos s⟩,
              ⟨false, vCellF Qc steps P (t + 1) tp pos s⟩] : Clause)]

/-- Flat-variable mirror of `activeCond`. -/
noncomputable def activeCondF (N : NTM 1) (steps P : ℕ) (t : ℕ) (q : N.Q)
    (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ) (po : ℕ) (so : Γ) (b : Bool) : Clause :=
  [⟨false, vStateF (Fintype.card N.Q) steps P t (stateIdx N q)⟩,
   ⟨false, vHeadF (Fintype.card N.Q) steps P t 0 pi⟩,
   ⟨false, vCellF (Fintype.card N.Q) steps P t 0 pi (symIdx si)⟩,
   ⟨false, vHeadF (Fintype.card N.Q) steps P t 1 pw⟩,
   ⟨false, vCellF (Fintype.card N.Q) steps P t 1 pw (symIdx sw)⟩,
   ⟨false, vHeadF (Fintype.card N.Q) steps P t 2 po⟩,
   ⟨false, vCellF (Fintype.card N.Q) steps P t 2 po (symIdx so)⟩,
   ⟨!b, vChoiceF (Fintype.card N.Q) steps P t⟩]

/-- Flat-variable mirror of `activeClausesAt`. -/
noncomputable def activeClausesAtF (N : NTM 1) (steps P : ℕ) (t : ℕ) (q : N.Q)
    (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ) (po : ℕ) (so : Γ) (b : Bool) : List Clause :=
  let out := N.δ b q si (fun _ => sw) so
  let nextState := if q = N.qhalt then q else out.1
  let wSym := if q = N.qhalt then sw else if pw = 0 then sw else (out.2.1 0).toΓ
  let oSym := if q = N.qhalt then so else if po = 0 then so else out.2.2.1.toΓ
  let iH := if q = N.qhalt then pi else posMove pi out.2.2.2.1
  let wH := if q = N.qhalt then pw else posMove pw (out.2.2.2.2.1 0)
  let oH := if q = N.qhalt then po else posMove po out.2.2.2.2.2
  let cond : Clause := activeCondF N steps P t q pi si pw sw po so b
  [cond ++ [⟨true, vStateF (Fintype.card N.Q) steps P (t + 1) (stateIdx N nextState)⟩],
   cond ++ [⟨true, vCellF (Fintype.card N.Q) steps P (t + 1) 0 pi (symIdx si)⟩],
   cond ++ [⟨true, vCellF (Fintype.card N.Q) steps P (t + 1) 1 pw (symIdx wSym)⟩],
   cond ++ [⟨true, vCellF (Fintype.card N.Q) steps P (t + 1) 2 po (symIdx oSym)⟩],
   cond ++ [⟨true, vHeadF (Fintype.card N.Q) steps P (t + 1) 0 iH⟩],
   cond ++ [⟨true, vHeadF (Fintype.card N.Q) steps P (t + 1) 1 wH⟩],
   cond ++ [⟨true, vHeadF (Fintype.card N.Q) steps P (t + 1) 2 oH⟩]]

/-- Flat-variable mirror of `activeTransitionClauses`. -/
noncomputable def activeTransitionClausesF (N : NTM 1) (steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (Finset.univ : Finset N.Q).toList.flatMap fun q =>
      (List.range (P + 1)).flatMap fun pi =>
        allSyms.flatMap fun si =>
          (List.range (P + 1)).flatMap fun pw =>
            allSyms.flatMap fun sw =>
              (List.range (P + 1)).flatMap fun po =>
                allSyms.flatMap fun so =>
                  [true, false].flatMap fun b =>
                    activeClausesAtF N steps P t q pi si pw sw po so b

/-- Re-indexing by `encOf` carries `startClausesF` to `startClauses`.
@isnad1 id=eq.0h3v.s5.132101d4e8f0 from=translated src=- shape=59c8d63d vocab=fbc1efe4
-/
theorem mapVar_startClausesF (x : List Bool) :
    CNF.mapVar (encOf N steps (steps + x.length + 1)) (startClausesF N steps x)
      = startClauses N steps x := by
  simp only [startClausesF, startClauses, encOf]
  rw [CNF.mapVar_cons, CNF.mapVar_append]
  congr 1
  · simp only [Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
    rw [flatToEnc_vStateF _ _ _ (by omega) (stateIdx_lt N _)]
  congr 1
  · rw [CNF.mapVar, List.map_map]
    refine List.map_congr_left fun tp htp => ?_
    rw [List.mem_range] at htp
    simp only [Function.comp_def, Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
    rw [flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega)]
  · rw [mapVar_flatMap]
    refine flatMap_congr' fun tp htp => ?_
    rw [CNF.mapVar, List.map_map]
    refine List.map_congr_left fun pos hpos => ?_
    rw [List.mem_range] at htp hpos
    simp only [Function.comp_def, Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
    rw [flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt _)]

/-- Re-indexing by `encOf` carries `frameClausesF` to `frameClauses`.
@isnad1 id=eq.0h3v.s5.f157b9a5e256 from=translated src=- shape=2649fce0 vocab=59bdbb25
-/
theorem mapVar_frameClausesF :
    CNF.mapVar (encOf N steps P) (frameClausesF (Fintype.card N.Q) steps P)
      = frameClauses 1 steps P := by
  rw [frameClausesF, frameClauses, encOf, mapVar_flatMap]
  refine flatMap_congr' fun t ht => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun tp htp => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun pos hpos => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun s hs => ?_
  rw [List.mem_range] at ht htp hpos hs
  simp only [CNF.mapVar, Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
  rw [flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (by omega),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (by omega)]

/-- Re-indexing by `encOf` carries `activeCondF` to `activeCond` (for in-range tuples).
@isnad1 id=eq.4h12v.s6.5fbeb22c9790 from=translated src=- shape=28d7269b vocab=54494342
-/
theorem mapVar_activeCondF (t : ℕ) (q : N.Q) (pi : ℕ) (si : Γ) (pw : ℕ) (sw : Γ)
    (po : ℕ) (so : Γ) (b : Bool) (ht : t < steps) (hpi : pi ≤ P) (hpw : pw ≤ P)
    (hpo : po ≤ P) :
    Clause.mapVar (encOf N steps P) (activeCondF N steps P t q pi si pw sw po so b)
      = activeCond N t q pi si pw sw po so b := by
  rw [activeCondF, activeCond, encOf]
  simp only [Clause.mapVar, List.map_cons, List.map_nil, Lit.mapVar]
  rw [flatToEnc_vStateF _ _ _ (by omega) (stateIdx_lt N q),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt si),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt sw),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (by omega),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt so),
    flatToEnc_vChoiceF _ _ _ (by omega)]

/-- Re-indexing by `encOf` carries `activeClausesAtF` to `activeClausesAt` (for in-range
    tuples).
@isnad1 id=eq.4h12v.s6.957570abcc0c from=translated src=- shape=28d7269b vocab=08e7c067
-/
theorem mapVar_activeClausesAtF (t : ℕ) (q : N.Q) (pi : ℕ) (si : Γ) (pw : ℕ)
    (sw : Γ) (po : ℕ) (so : Γ) (b : Bool) (ht : t < steps) (hpi : pi ≤ P)
    (hpw : pw ≤ P) (hpo : po ≤ P) :
    CNF.mapVar (encOf N steps P) (activeClausesAtF N steps P t q pi si pw sw po so b)
      = activeClausesAt N t q pi si pw sw po so b := by
  have hposM : ∀ (p : ℕ) (d : Dir3), p ≤ P →
      (if q = N.qhalt then p else posMove p d) < P + 2 := by
    intro p d hp
    split
    · omega
    · exact Nat.lt_of_le_of_lt (posMove_le_succ p d) (by omega)
  have hcond := mapVar_activeCondF N steps P t q pi si pw sw po so b ht hpi hpw hpo
  have happ : ∀ (c : Clause) (l : Lit), Clause.mapVar (encOf N steps P) (c ++ [l])
      = Clause.mapVar (encOf N steps P) c ++ [Lit.mapVar (encOf N steps P) l] :=
    fun c l => List.map_append ..
  simp only [activeClausesAtF, activeClausesAt, CNF.mapVar, List.map_cons, List.map_nil]
  rw [happ, happ, happ, happ, happ, happ, happ, hcond]
  simp only [Lit.mapVar, encOf]
  rw [flatToEnc_vStateF _ _ _ (by omega) (stateIdx_lt N _),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt _),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt _),
    flatToEnc_vCellF _ _ _ (by omega) (by omega) (by omega) (symIdx_lt _),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (hposM _ _ hpi),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (hposM _ _ hpw),
    flatToEnc_vHeadF _ _ _ (by omega) (by omega) (hposM _ _ hpo)]

/-- Re-indexing by `encOf` carries `activeTransitionClausesF` to `activeTransitionClauses`.
@isnad1 id=eq.0h3v.s4.812c46850646 from=translated src=- shape=c2397fb9 vocab=c3b3d1b8
-/
theorem mapVar_activeTransitionClausesF :
    CNF.mapVar (encOf N steps P) (activeTransitionClausesF N steps P)
      = activeTransitionClauses N steps P := by
  rw [activeTransitionClausesF, activeTransitionClauses, mapVar_flatMap]
  refine flatMap_congr' fun t ht => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun q _ => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun pi hpi => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun si _ => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun pw hpw => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun sw _ => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun po hpo => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun so _ => ?_
  rw [mapVar_flatMap]
  refine flatMap_congr' fun b _ => ?_
  rw [List.mem_range] at ht hpi hpw hpo
  exact mapVar_activeClausesAtF N steps P t q pi si pw sw po so b ht (by omega)
    (by omega) (by omega)

end FamilyEq

end Tableau

/-- **The flat computation-tableau formula**: `tableauCNF` with mixed-radix
    variable indices in place of the `Nat.pair`-based ones. Satisfiability is
    identical (`tableauCNFFlat_satisfiable_iff`); this is the formula the
    reduction machine emits, since its indices need only multiplication and
    addition. -/
noncomputable def tableauCNFFlat (N : NTM 1) (steps : ℕ) (x : List Bool) : CNF :=
  let P := steps + x.length + 1
  Tableau.oneHotStatesF N steps P ++
    Tableau.oneHotCellsF (Fintype.card N.Q) steps P ++
    Tableau.oneHotHeadsF (Fintype.card N.Q) steps P ++
    Tableau.startClausesF N steps x ++
    Tableau.frameClausesF (Fintype.card N.Q) steps P ++
    Tableau.activeTransitionClausesF N steps P ++
    Tableau.acceptClausesF N steps P

/-- The flat tableau is the `enc` tableau, re-indexed.
@isnad1 id=eq.0h3v.s5.505ef16b5c4b from=translated src=- shape=952893a4 vocab=d4cc4dbc
-/
theorem tableauCNFFlat_mapVar (N : NTM 1) (steps : ℕ) (x : List Bool) :
    CNF.mapVar (Tableau.encOf N steps (steps + x.length + 1)) (tableauCNFFlat N steps x)
      = tableauCNF N steps x := by
  rw [tableauCNFFlat, tableauCNF]
  simp only [CNF.mapVar_append]
  rw [Tableau.mapVar_oneHotStatesF, Tableau.mapVar_oneHotCellsF,
    Tableau.mapVar_oneHotHeadsF, Tableau.mapVar_startClausesF,
    Tableau.mapVar_frameClausesF, Tableau.mapVar_activeTransitionClausesF,
    Tableau.mapVar_acceptClausesF]

/-- The Cook–Levin reduction function: map each input to the encoding of its
    (flat-variable) computation-tableau formula. -/
noncomputable def reductionFn (N : NTM 1) (T : ℕ → ℕ) : List Bool → List Bool :=
  fun x => (tableauCNFFlat N (T x.length) x).encode

/-! The reduction machine, its polynomial running time, and the headline
theorems `reductionFn_mem_FP`, `cookLevin_reduction`, `NPHard_language`, and
`NPComplete_language` live in `Complexitylib.SAT.CookLevin.Assembly`, built on
the emitter development under `Complexitylib.SAT.CookLevin/`. -/

end SAT

end Complexity
