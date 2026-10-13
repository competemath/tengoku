/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.UTM.Internal.Body
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Body machine: step reduction

The single lemma every phase proof of the body correctness uses:
`bodyTM.step` on a non-halted configuration, when the transition arm is a
`mkAct` (they all are, by `bodyδ_shape`), produces the configuration whose
work tapes act per `acts`, whose real input idles, and whose real output
write-backs — in closed form.
-/

public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

/-- Closed form of one `bodyTM` step whose transition arm is `mkAct q' acts`
    (every arm is — `bodyδ_shape`). The real input tape idle-moves, the real
    output tape write-backs and idle-moves, and work tape `i` performs
    `acts i` (with the `▷ ⇒ right` sanitization) or idles.
@isnad1 id=eq.2h3v.s8.be7b026421b4 from=translated src=- shape=1296ae9e vocab=f80d5bb8
-/
theorem step_mkAct {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {acts : TapeActs}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = mkAct q' c.input.read (fun i => (c.work i).read) c.output.read acts) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i => match acts i with
          | some (w, d) => (c.work i).writeAndMove w.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d)
          | none => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  have hne' : c.state ≠ bodyTM.qhalt := hne
  simp only [step, ite_eq_right hne', Option.some.injEq]
  show (let (q'', wW, oW, iD, wD, oD) :=
      bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
    ({ state := q'', input := c.input.move iD,
       work := fun i => (c.work i).writeAndMove (wW i).toΓ (wD i),
       output := c.output.writeAndMove oW.toΓ oD } : Cfg 6 bodyTM.Q)) = _
  rw [h]
  simp only [mkAct]
  congr 1
  funext i
  cases acts i with
  | none => rfl
  | some wd => rfl

/-- An idle work tape is exactly preserved by a `mkAct` step when it reads
    a non-`▷` symbol (its action is precisely `transitionTape`).
@isnad1 id=eq.1h1v.s4.9d65899c15de from=translated src=- shape=3850961c vocab=155aac5a
-/
theorem idle_tape_id {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t :=
  transitionTape_eq_self h

/-- The idled real input tape is exactly preserved when reading non-`▷`.
@isnad1 id=eq.1h1v.s4.18369d5a30ec from=translated src=- shape=3281b7fe vocab=3d5fe084
-/
theorem idle_input_id {t : Tape} (h : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t :=
  transitionInput_eq_self h

-- ════════════════════════════════════════════════════════════════════════
-- Generic rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Closed form of a step whose arm is `act1` (one active tape).
@isnad1 id=eq.2h5v.s8.83ced83449fa from=translated src=- shape=0fd9361a vocab=a9bc4813
-/
theorem step_act1 {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {t : Fin 6} {w : Γw} {d : Dir3}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = act1 q' c.input.read (fun i => (c.work i).read) c.output.read t w d) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i =>
          if i = t then
            (c.work i).writeAndMove w.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d)
          else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
            (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  rw [step_mkAct hne h]
  refine congrArg some ?_
  congr 1
  funext i
  by_cases hi : i = t <;> simp [hi]

/-- Closed form of a step whose arm is `act2` (two active tapes).
@isnad1 id=eq.2h8v.s9.80c19a49f275 from=translated src=- shape=7dd5641b vocab=4b8b6951
-/
theorem step_act2 {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {t₁ t₂ : Fin 6} {w₁ w₂ : Γw} {d₁ d₂ : Dir3}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = act2 q' c.input.read (fun i => (c.work i).read) c.output.read
          t₁ w₁ d₁ t₂ w₂ d₂) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i =>
          if i = t₁ then
            (c.work i).writeAndMove w₁.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d₁)
          else if i = t₂ then
            (c.work i).writeAndMove w₂.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d₂)
          else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
            (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  rw [step_mkAct hne h]
  refine congrArg some ?_
  congr 1
  funext i
  by_cases h1 : i = t₁
  · simp [h1]
  · by_cases h2 : i = t₂
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- Closed form of a step whose arm is `act3` (three active tapes).
@isnad1 id=eq.2h11v.s9.b436a6a2cb8d from=translated src=- shape=6f9367d3 vocab=c86c7ed4
-/
theorem step_act3 {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {t₁ t₂ t₃ : Fin 6} {w₁ w₂ w₃ : Γw} {d₁ d₂ d₃ : Dir3}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = act3 q' c.input.read (fun i => (c.work i).read) c.output.read
          t₁ w₁ d₁ t₂ w₂ d₂ t₃ w₃ d₃) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i =>
          if i = t₁ then
            (c.work i).writeAndMove w₁.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d₁)
          else if i = t₂ then
            (c.work i).writeAndMove w₂.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d₂)
          else if i = t₃ then
            (c.work i).writeAndMove w₃.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d₃)
          else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
            (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  rw [step_mkAct hne h]
  refine congrArg some ?_
  congr 1
  funext i
  by_cases h1 : i = t₁
  · simp [h1]
  · by_cases h2 : i = t₂
    · subst h2; simp [h1]
    · by_cases h3 : i = t₃
      · subst h3; simp [h1, h2]
      · simp [h1, h2, h3]

/-- **Generic rewind loop** for any pair of states whose transition is
    `rewStep cur next · t`: from state `cur` with work-tape-`t` head at `p`
    (cells `W`, well-formed), reach state `next` with head 1 in `p + 1`
    steps; tape `t`'s cells and every other tape are exactly preserved.
@isnad1 id=ex.10h6v.s8.4f0ce1c15371 from=translated src=- shape=1089a783 vocab=973ff9b4
-/
theorem rewStep_loop {cur next : BodyQ} {t : Fin 6}
    (hcur : cur ≠ bodyDone)
    (hδ : ∀ iH wH oH, bodyδ cur iH wH oH = rewStep cur next iH wH oH t)
    (W : ℕ → Γ) (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (p : ℕ) (c : Cfg 6 bodyTM.Q),
      c.state = cur →
      (c.work t).cells = W → (c.work t).head = p →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ t → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (p + 1) c c' ∧
        c'.state = next ∧
        c'.work t = ⟨1, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ t → c'.work i = c.work i) := by
  intro p
  induction p with
  | zero =>
    intro c hst hcW hhead hin hout hoth
    have hread : (c.work t).read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [rewStep, ite_eq_left hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (if t = t then _ else _) = _
      rw [ite_eq_left rfl, ite_eq_left hread]
      have hwr : (c.work t).write (readBackWrite ((c.work t).read)).toΓ = c.work t := by
        unfold Tape.write
        rw [ite_eq_left hhead]
      show ((c.work t).write _).move .right = _
      rw [hwr]
      simp only [Tape.move, Tape.mk.injEq]
      exact ⟨by rw [hhead], hcW⟩
    · intro i hi
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)
  | succ p ih =>
    intro c hst hcW hhead hin hout hoth
    have hread : (c.work t).read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (p + 1) (by omega)
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [rewStep, ite_eq_right hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwt', hin', hout', hoth'⟩ :=
      ih { state := cur
           input := c.input.move (idleDir c.input.read)
           work := fun i =>
             if i = t then
               (c.work i).writeAndMove (readBackWrite ((c.work t).read)).toΓ
                 (if (c.work i).read = Γ.start then Dir3.right else Dir3.left)
             else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
               (idleDir ((c.work i).read))
           output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
             (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread,
            tape_readBackWrite_preserves _ _ (Or.inr hread), hcW])
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread]
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
          omega)
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi => by
          dsimp only
          rw [ite_eq_right hi, idle_tape_id (hoth i hi)]
          exact hoth i hi)
    refine ⟨c', .step hstep hreach, hst', hwt', ?_, ?_, ?_⟩
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi
      rw [hoth' i hi]
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)

-- ════════════════════════════════════════════════════════════════════════
-- Generic blank-rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- **Generic blank-rewind loop** for any pair of states whose transition is
    `blankRewStep cur next · t`: from state `cur` with work-tape-`t` head at
    `p`, reach state `next` with head 1 in `p + 1` steps, with cells `1..p`
    blanked; every other tape exactly preserved.
@isnad1 id=ex.10h6v.s9.bdaf232454de from=translated src=- shape=9d4f01f1 vocab=151d0cd3
-/
theorem blankRewStep_loop {cur next : BodyQ} {t : Fin 6}
    (hcur : cur ≠ bodyDone)
    (hδ : ∀ iH wH oH, bodyδ cur iH wH oH = blankRewStep cur next iH wH oH t) :
    ∀ (p : ℕ) (W : ℕ → Γ), W 0 = Γ.start → (∀ j, 1 ≤ j → W j ≠ Γ.start) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = cur →
      (c.work t).cells = W → (c.work t).head = p →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ t → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (p + 1) c c' ∧
        c'.state = next ∧
        c'.work t = ⟨1, fun j => if 1 ≤ j ∧ j ≤ p then Γ.blank else W j⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ t → c'.work i = c.work i) := by
  intro p
  induction p with
  | zero =>
    intro W hW0 hWns c hst hcW hhead hin hout hoth
    have hread : (c.work t).read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [blankRewStep, ite_eq_left hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (if t = t then _ else _) = (⟨1, _⟩ : Tape)
      rw [ite_eq_left rfl, ite_eq_left hread]
      have hwr : (c.work t).write (readBackWrite ((c.work t).read)).toΓ = c.work t := by
        unfold Tape.write
        rw [ite_eq_left hhead]
      show ((c.work t).write _).move .right = _
      rw [hwr]
      simp only [Tape.move, Tape.mk.injEq]
      refine ⟨by rw [hhead], ?_⟩
      rw [hcW]
      funext j
      rw [ite_eq_right (by omega)]
    · intro i hi
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)
  | succ p ih =>
    intro W hW0 hWns c hst hcW hhead hin hout hoth
    have hread : (c.work t).read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (p + 1) (by omega)
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [blankRewStep, ite_eq_right hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    -- cells after blanking cell p+1
    have hupd0 : Function.update W (p + 1) Γ.blank 0 = Γ.start := by
      rw [Function.update_of_ne (by omega)]; exact hW0
    have hupdns : ∀ j, 1 ≤ j → Function.update W (p + 1) Γ.blank j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = p + 1
      · subst hje; rw [Function.update_self]; simp
      · rw [Function.update_of_ne hje]; exact hWns j hj
    obtain ⟨c', hreach, hst', hwt', hin', hout', hoth'⟩ :=
      ih (Function.update W (p + 1) Γ.blank) hupd0 hupdns
        { state := cur
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = t then
              (c.work i).writeAndMove Γw.blank.toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.left)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread]
          show (((c.work t).write _).move Dir3.left).cells = _
          have : (c.work t).write Γw.blank.toΓ
              = { c.work t with cells :=
                    Function.update (c.work t).cells (c.work t).head Γw.blank.toΓ } := by
            unfold Tape.write
            rw [ite_eq_right (by omega)]
          rw [this]
          show Function.update (c.work t).cells (c.work t).head Γw.blank.toΓ = _
          rw [hcW, hhead]
          rfl)
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread]
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
          omega)
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi => by
          dsimp only
          rw [ite_eq_right hi, idle_tape_id (hoth i hi)]
          exact hoth i hi)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_⟩
    · rw [hwt']
      refine congrArg _ ?_
      funext j
      by_cases hj1 : 1 ≤ j ∧ j ≤ p
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
      · rw [ite_eq_right hj1]
        by_cases hje : j = p + 1
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi
      rw [hoth' i hi]
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)

-- ════════════════════════════════════════════════════════════════════════
-- Generic scan-right loop
-- ════════════════════════════════════════════════════════════════════════

/-- **Generic scan-right loop** for any pair of states whose transition is
    `act1 (if □ then next else cur) · t readBack right` — the machine walks
    right to the first `□` and steps past it. `k` is the distance to that
    `□`. Cells are preserved exactly; every other tape untouched.
@isnad1 id=ex.12h7v.s9.e9f74c89d8b3 from=translated src=- shape=212d43a8 vocab=1eb5ee7f
-/
theorem scanRight_loop {cur next : BodyQ} {t : Fin 6}
    (hcur : cur ≠ bodyDone)
    (hδ : ∀ iH wH oH, bodyδ cur iH wH oH
      = act1 (if wH t = Γ.blank then next else cur) iH wH oH t
          (readBackWrite (wH t)) .right)
    (W : ℕ → Γ) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (k h : ℕ), 1 ≤ h →
      (∀ j, j < k → W (h + j) ≠ Γ.blank) → W (h + k) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = cur →
      (c.work t).cells = W → (c.work t).head = h →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ t → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (k + 1) c c' ∧
        c'.state = next ∧
        c'.work t = ⟨h + k + 1, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ t → c'.work i = c.work i) := by
  intro k
  induction k with
  | zero =>
    intro h hh hnb hbl c hst hcW hhead hin hout hoth
    have hread : (c.work t).read = Γ.blank := by
      simp only [Tape.read, hhead, hcW]
      simpa using hbl
    have hread' : (c.work t).read ≠ Γ.start := by rw [hread]; simp
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_left hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (if t = t then _ else _) = (⟨h + 0 + 1, W⟩ : Tape)
      rw [ite_eq_left rfl, ite_eq_right hread']
      show ((c.work t).write _).move .right = _
      have hcells := tape_readBackWrite_preserves (c.work t) Dir3.right (Or.inr hread')
      simp only [Tape.writeAndMove] at hcells
      simp only [Tape.move, Tape.mk.injEq, Tape.write_head]
      refine ⟨by rw [hhead], ?_⟩
      have : ((c.work t).write (readBackWrite ((c.work t).read)).toΓ).cells
          = (c.work t).cells := by
        have := tape_readBackWrite_preserves (c.work t) Dir3.stay (Or.inr hread')
        simpa [Tape.writeAndMove, Tape.move] using this
      rw [this, hcW]
    · intro i hi
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)
  | succ k ih =>
    intro h hh hnb hbl c hst hcW hhead hin hout hoth
    have hread : (c.work t).read = W h := by
      simp [Tape.read, hhead, hcW]
    have hreadnb : (c.work t).read ≠ Γ.blank := by
      rw [hread]
      simpa using hnb 0 (by omega)
    have hread' : (c.work t).read ≠ Γ.start := by
      rw [hread]; exact hWns h hh
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_right hreadnb] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwt', hin', hout', hoth'⟩ :=
      ih (h + 1) (by omega)
        (fun j hj => by
          have := hnb (j + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
        (by
          have : h + 1 + k = h + (k + 1) := by omega
          rw [this]; exact hbl)
        { state := cur
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = t then
              (c.work i).writeAndMove (readBackWrite ((c.work t).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl,
            tape_readBackWrite_preserves _ _ (Or.inr hread'), hcW])
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hhead])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi => by
          dsimp only
          rw [ite_eq_right hi, idle_tape_id (hoth i hi)]
          exact hoth i hi)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_⟩
    · rw [hwt']
      exact congrArg (fun n => (⟨n, W⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi
      rw [hoth' i hi]
      show (if i = t then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)

-- ════════════════════════════════════════════════════════════════════════
-- Arm-shape instantiations (all definitional)
-- ════════════════════════════════════════════════════════════════════════

section Arms
variable (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) (f : VFlags)

/--
@isnad1 id=eq.0h3v.s5.772cfa09d5f0 from=translated src=- shape=3e67e170 vocab=7e23771f
-/
theorem arm_haltRewS : bodyδ haltRewS iH wH oH = rewStep haltRewS haltRewD iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.42d4beb77e2d from=translated src=- shape=3e67e170 vocab=ff2c45c9
-/
theorem arm_haltRewD : bodyδ haltRewD iH wH oH = rewStep haltRewD bodyDone iH wH oH dsT := rfl
/--
@isnad1 id=eq.0h3v.s5.419c97808f22 from=translated src=- shape=3e67e170 vocab=4bdc8bc7
-/
theorem arm_preRewS : bodyδ preRewS iH wH oH = rewStep preRewS preRewD iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.7c5eaaee9766 from=translated src=- shape=3e67e170 vocab=4c0a44b5
-/
theorem arm_preRewD : bodyδ preRewD iH wH oH = rewStep preRewD peek1 iH wH oH dsT := rfl
/--
@isnad1 id=eq.0h4v.s5.84cc800af1ea from=translated src=- shape=340d7ce1 vocab=58075131
-/
theorem arm_rewindSt :
    bodyδ (rewindSt f) iH wH oH = rewStep (rewindSt f) (cmpQ f) iH wH oH stT := rfl
/--
@isnad1 id=eq.0h4v.s5.66b11fcedb77 from=translated src=- shape=340d7ce1 vocab=6419299a
-/
theorem arm_appRewScr :
    bodyδ (appRewScr f) iH wH oH = rewStep (appRewScr f) (appQ' f) iH wH oH scT := rfl
/--
@isnad1 id=eq.0h3v.s5.ab585f368beb from=translated src=- shape=3e67e170 vocab=6d85a680
-/
theorem arm_dfStRew : bodyδ dfStRew iH wH oH = rewStep dfStRew dfBlank iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.498e3cf3a68e from=translated src=- shape=3e67e170 vocab=f02e4569
-/
theorem arm_dfStRew2 : bodyδ dfStRew2 iH wH oH = rewStep dfStRew2 dfDescRew iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.a4242ab053d7 from=translated src=- shape=3e67e170 vocab=2fba435d
-/
theorem arm_dfDescRew : bodyδ dfDescRew iH wH oH = rewStep dfDescRew dfSkip iH wH oH dsT := rfl
/--
@isnad1 id=eq.0h3v.s5.93b6f4c5de11 from=translated src=- shape=3e67e170 vocab=c41a8b83
-/
theorem arm_dfStRew3 : bodyδ dfStRew3 iH wH oH = rewStep dfStRew3 dfDescRew2 iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.50844bb1943c from=translated src=- shape=3e67e170 vocab=80252450
-/
theorem arm_dfDescRew2 :
    bodyδ dfDescRew2 iH wH oH = rewStep dfDescRew2 bodyDone iH wH oH dsT := rfl
/--
@isnad1 id=eq.0h3v.s5.468ca43748c1 from=translated src=- shape=3e67e170 vocab=82383214
-/
theorem arm_clSt : bodyδ clSt iH wH oH = rewStep clSt clDesc iH wH oH stT := rfl
/--
@isnad1 id=eq.0h3v.s5.0898f1da31ce from=translated src=- shape=3e67e170 vocab=7576ceff
-/
theorem arm_clDesc : bodyδ clDesc iH wH oH = rewStep clDesc bodyDone iH wH oH dsT := rfl

/--
@isnad1 id=eq.0h4v.s5.187acbcef59e from=translated src=- shape=340d7ce1 vocab=5f427886
-/
theorem arm_mmScr :
    bodyδ (mmScr f) iH wH oH = blankRewStep (mmScr f) (rewindSt f) iH wH oH scT := rfl
/--
@isnad1 id=eq.0h3v.s5.968a38cc10a4 from=translated src=- shape=3e67e170 vocab=81269f33
-/
theorem arm_dfScr : bodyδ dfScr iH wH oH = blankRewStep dfScr dfStRew iH wH oH scT := rfl
/--
@isnad1 id=eq.0h3v.s5.744fb85c0b07 from=translated src=- shape=3e67e170 vocab=854f494b
-/
theorem arm_clScr : bodyδ clScr iH wH oH = blankRewStep clScr clSt iH wH oH scT := rfl

/--
@isnad1 id=eq.0h3v.s6.53b78abc3fcf from=translated src=- shape=aaa4b99a vocab=4367af68
-/
theorem arm_hc0 : bodyδ hc0 iH wH oH
    = act1 (if wH dsT = Γ.blank then hc1 else hc0) iH wH oH dsT
        (readBackWrite (wH dsT)) .right := rfl
/--
@isnad1 id=eq.0h4v.s6.ef9f6461fdc1 from=translated src=- shape=4c4b38c6 vocab=3a7d8f70
-/
theorem arm_seek1 : bodyδ (seek1 f) iH wH oH
    = act1 (if wH dsT = Γ.blank then seek2 f else seek1 f) iH wH oH dsT
        (readBackWrite (wH dsT)) .right := rfl
/--
@isnad1 id=eq.0h4v.s6.2018468f648a from=translated src=- shape=4c4b38c6 vocab=47be837e
-/
theorem arm_seek2 : bodyδ (seek2 f) iH wH oH
    = act1 (if wH dsT = Γ.blank then cmpQ f else seek2 f) iH wH oH dsT
        (readBackWrite (wH dsT)) .right := rfl
/--
@isnad1 id=eq.0h4v.s6.3a105c06e308 from=translated src=- shape=4c4b38c6 vocab=a2c920b7
-/
theorem arm_skipSeg : bodyδ (skipSeg f) iH wH oH
    = act1 (if wH dsT = Γ.blank then segCheck f else skipSeg f) iH wH oH dsT
        (readBackWrite (wH dsT)) .right := rfl
/--
@isnad1 id=eq.0h3v.s6.8e468ea47c4d from=translated src=- shape=aaa4b99a vocab=fda02d03
-/
theorem arm_dfSkip : bodyδ dfSkip iH wH oH
    = act1 (if wH dsT = Γ.blank then dfCopy else dfSkip) iH wH oH dsT
        (readBackWrite (wH dsT)) .right := rfl

/--
@isnad1 id=eq.0h3v.s7.831770fdf391 from=translated src=- shape=94e07fbe vocab=cb4db79c
-/
theorem arm_hc1 : bodyδ hc1 iH wH oH
    = if wH stT = Γ.blank ∧ wH dsT = Γ.blank then idle haltRewS iH wH oH
      else if wH stT ≠ Γ.blank ∧ wH dsT ≠ Γ.blank ∧ wH stT = wH dsT then
        act2 hc1 iH wH oH stT (readBackWrite (wH stT)) .right
          dsT (readBackWrite (wH dsT)) .right
      else idle preRewS iH wH oH := rfl

/--
@isnad1 id=eq.0h3v.s6.1aeb37f3ba50 from=translated src=- shape=d13fef69 vocab=cac209e9
-/
theorem arm_peek1 : bodyδ peek1 iH wH oH
    = act3 peek2 iH wH oH
        vIn (readBackWrite (wH vIn)) .left
        vWk (readBackWrite (wH vWk)) .left
        vOut (readBackWrite (wH vOut)) .left := rfl

/--
@isnad1 id=eq.0h3v.s6.2d291468423a from=translated src=- shape=054f027b vocab=2bfefbe2
-/
theorem arm_peek2 : bodyδ peek2 iH wH oH
    = act3 (seek1 (wH vIn = Γ.start, wH vWk = Γ.start, wH vOut = Γ.start)) iH wH oH
        vIn (readBackWrite (wH vIn)) .right
        vWk (readBackWrite (wH vWk)) .right
        vOut (readBackWrite (wH vOut)) .right := rfl

/--
@isnad1 id=eq.0h4v.s7.27c00407e750 from=translated src=- shape=61f5596a vocab=69fcfada
-/
theorem arm_cmpQ : bodyδ (cmpQ f) iH wH oH
    = if wH stT = Γ.blank then idle (cmpS f 0) iH wH oH
      else if wH dsT ≠ Γ.blank ∧ wH stT = wH dsT then
        act2 (cmpQ f) iH wH oH stT (readBackWrite (wH stT)) .right
          dsT (readBackWrite (wH dsT)) .right
      else idle (skipSeg f) iH wH oH := rfl

/--
@isnad1 id=eq.0h5v.s8.3f0b91b1ec7d from=translated src=- shape=d66aff10 vocab=70e877cb
-/
theorem arm_cmpS (idx : Fin 6) : bodyδ (cmpS f idx) iH wH oH
    = if wH dsT = keyCell f (wH vIn) (wH vWk) (wH vOut) idx ∧ wH dsT ≠ Γ.blank then
        if h : idx.val < 5 then
          act1 (cmpS f ⟨idx.val + 1, by omega⟩) iH wH oH dsT
            (readBackWrite (wH dsT)) .right
        else
          act2 (copyQ' f) iH wH oH dsT (readBackWrite (wH dsT)) .right
            stT (readBackWrite (wH stT)) .left
      else idle (skipSeg f) iH wH oH := rfl

/--
@isnad1 id=eq.0h4v.s7.114a40f152a6 from=translated src=- shape=000472c0 vocab=28eb3e4b
-/
theorem arm_copyQ' : bodyδ (copyQ' f) iH wH oH
    = if wH stT = Γ.start then
        act1 (copyAct f 0) iH wH oH stT (readBackWrite (wH stT)) .right
      else if wH dsT = Γ.blank then idle (skipSeg f) iH wH oH
      else
        act3 (copyQ' f) iH wH oH
          scT (readBackWrite (wH dsT)) .right
          dsT (readBackWrite (wH dsT)) .right
          stT (readBackWrite (wH stT)) .left := rfl

/--
@isnad1 id=eq.0h5v.s7.af82e483b8f1 from=translated src=- shape=6767ce78 vocab=43ce7253
-/
theorem arm_copyAct (j : Fin 10) : bodyδ (copyAct f j) iH wH oH
    = if wH dsT = Γ.blank then idle (skipSeg f) iH wH oH
      else
        act2 (if h : j.val < 9 then copyAct f ⟨j.val + 1, by omega⟩ else appRewScr f)
          iH wH oH scT (readBackWrite (wH dsT)) .right
          dsT (readBackWrite (wH dsT)) .right := rfl

/--
@isnad1 id=eq.0h4v.s7.bd6ebd49c444 from=translated src=- shape=c4445e9e vocab=136c59f9
-/
theorem arm_segCheck : bodyδ (segCheck f) iH wH oH
    = if wH dsT = Γ.blank then
        act3 dfScr iH wH oH
          vIn (readBackWrite (wH vIn)) (if f.1 then .right else .stay)
          vWk (readBackWrite (wH vWk)) (if f.2.1 then .right else .stay)
          vOut (readBackWrite (wH vOut)) (if f.2.2 then .right else .stay)
      else idle (mmScr f) iH wH oH := rfl

/--
@isnad1 id=eq.0h4v.s6.6d2a1380de24 from=translated src=- shape=6770ce7a vocab=fa342b15
-/
theorem arm_appQ' : bodyδ (appQ' f) iH wH oH
    = if wH stT = Γ.blank then idle (appAct f 0 none) iH wH oH
      else
        act2 (appQ' f) iH wH oH
          stT (readBackWrite (wH scT)) .right
          scT (readBackWrite (wH scT)) .right := rfl

/--
@isnad1 id=eq.0h5v.s6.f430be705b2a from=translated src=- shape=357fe470 vocab=3e94d3d2
-/
theorem arm_appAct_none (g : Fin 5) : bodyδ (appAct f g none) iH wH oH
    = act1 (appAct f g (some (cellBit (wH scT)))) iH wH oH
        scT (readBackWrite (wH scT)) .right := rfl

/--
@isnad1 id=eq.0h5v.s7.f28b31bead8f from=translated src=- shape=886057ef vocab=97d21cd0
-/
theorem arm_appAct0 (b₀ : Bool) : bodyδ (appAct f 0 (some b₀)) iH wH oH
    = act2 (appAct f 1 none) iH wH oH
        scT (readBackWrite (wH scT)) .right
        vWk (if f.2.1 then Γw.blank else grpΓw b₀ (cellBit (wH scT))) .stay := rfl

/--
@isnad1 id=eq.0h5v.s7.95b4a84957a2 from=translated src=- shape=87a44855 vocab=34abffcd
-/
theorem arm_appAct1 (b₀ : Bool) : bodyδ (appAct f 1 (some b₀)) iH wH oH
    = act2 (appAct f 2 none) iH wH oH
        scT (readBackWrite (wH scT)) .right
        vOut (if f.2.2 then Γw.blank else grpΓw b₀ (cellBit (wH scT))) .stay := rfl

/--
@isnad1 id=eq.0h5v.s7.a1ebcd273d27 from=translated src=- shape=0562b74c vocab=cc20e86d
-/
theorem arm_appAct2 (b₀ : Bool) : bodyδ (appAct f 2 (some b₀)) iH wH oH
    = act2 (appAct f 3 none) iH wH oH
        scT (readBackWrite (wH scT)) .right
        vIn (readBackWrite (wH vIn))
          (if f.1 then .right else grpDir b₀ (cellBit (wH scT))) := rfl

/--
@isnad1 id=eq.0h5v.s7.12a0682a06aa from=translated src=- shape=3ed2e7da vocab=2c0bca41
-/
theorem arm_appAct3 (b₀ : Bool) : bodyδ (appAct f 3 (some b₀)) iH wH oH
    = act2 (appAct f 4 none) iH wH oH
        scT (readBackWrite (wH scT)) .right
        vWk (readBackWrite (wH vWk))
          (if f.2.1 then .right else grpDir b₀ (cellBit (wH scT))) := rfl

/--
@isnad1 id=eq.0h5v.s6.e047cafb88e5 from=translated src=- shape=6679df15 vocab=ad341b3f
-/
theorem arm_appAct4 (b₀ : Bool) : bodyδ (appAct f 4 (some b₀)) iH wH oH
    = act2 clScr iH wH oH
        scT (readBackWrite (wH scT)) .right
        vOut (readBackWrite (wH vOut))
          (if f.2.2 then .right else grpDir b₀ (cellBit (wH scT))) := rfl

/--
@isnad1 id=eq.0h3v.s6.fe5105a94bbd from=translated src=- shape=a9dab11a vocab=c2943662
-/
theorem arm_dfBlank : bodyδ dfBlank iH wH oH
    = if wH stT = Γ.blank then idle dfStRew2 iH wH oH
      else act1 dfBlank iH wH oH stT Γw.blank .right := rfl

/--
@isnad1 id=eq.0h3v.s6.e47ba10d6056 from=translated src=- shape=fad4b19e vocab=a950f2ff
-/
theorem arm_dfCopy : bodyδ dfCopy iH wH oH
    = if wH dsT = Γ.blank then idle dfStRew3 iH wH oH
      else
        act2 dfCopy iH wH oH
          stT (readBackWrite (wH dsT)) .right
          dsT (readBackWrite (wH dsT)) .right := rfl

end Arms

-- ════════════════════════════════════════════════════════════════════════
-- Blank-rightward loop (dfBlank)
-- ════════════════════════════════════════════════════════════════════════

/-- The default path's state-tape blanking: from `dfBlank` with the state
    head at `h ≥ 1` and the first `□` at distance `k`, blank cells
    `h..h+k-1` and stop on the `□` (head at `h + k`, one idle transition
    step) in `k + 1` steps. All other tapes exactly preserved.
@isnad1 id=ex.10h4v.s8.ce307c6688f4 from=translated src=- shape=0f581d8e vocab=5cd0cfb7
-/
theorem dfBlank_loop :
    ∀ (k : ℕ) (W : ℕ → Γ), (∀ j, 1 ≤ j → W j ≠ Γ.start) →
      ∀ (h : ℕ), 1 ≤ h →
      (∀ j, j < k → W (h + j) ≠ Γ.blank) → W (h + k) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = dfBlank →
      (c.work stT).cells = W → (c.work stT).head = h →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (k + 1) c c' ∧
        c'.state = dfStRew2 ∧
        c'.work stT = ⟨h + k, fun j => if h ≤ j ∧ j < h + k then Γ.blank else W j⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → c'.work i = c.work i) := by
  intro k
  induction k with
  | zero =>
    intro W hWns h hh hnb hbl c hst hcW hhead hin hout hoth
    have hread : (c.work stT).read = Γ.blank := by
      simp only [Tape.read, hhead, hcW]
      simpa using hbl
    have harm := arm_dfBlank c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_left hread] at harm
    have hstep := step_mkAct (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, idle_input_id hin, idle_tape_id hout,
      fun i hi => idle_tape_id (hoth i hi)⟩
    show (c.work stT).writeAndMove _ _ = _
    rw [idle_tape_id (by rw [hread]; simp)]
    have : (fun j => if h ≤ j ∧ j < h + 0 then Γ.blank else W j) = W := by
      funext j
      rw [ite_eq_right (by omega)]
    rw [this, ← hcW, show h + 0 = (c.work stT).head from by rw [hhead]; omega]
  | succ k ih =>
    intro W hWns h hh hnb hbl c hst hcW hhead hin hout hoth
    have hread : (c.work stT).read = W h := by
      simp [Tape.read, hhead, hcW]
    have hreadnb : (c.work stT).read ≠ Γ.blank := by
      rw [hread]
      simpa using hnb 0 (by omega)
    have harm := arm_dfBlank c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_right hreadnb] at harm
    have hread' : (c.work stT).read ≠ Γ.start := by
      rw [hread]; exact hWns h hh
    have hstep := step_act1 (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    -- the blanked-one-cell ghost
    have hupdns : ∀ j, 1 ≤ j → Function.update W h Γ.blank j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = h
      · subst hje; rw [Function.update_self]; simp
      · rw [Function.update_of_ne hje]; exact hWns j hj
    obtain ⟨c', hreach, hst', hwt', hin', hout', hoth'⟩ :=
      ih (Function.update W h Γ.blank) hupdns (h + 1) (by omega)
        (fun j hj => by
          rw [Function.update_of_ne (by omega)]
          have := hnb (j + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
        (by
          rw [Function.update_of_ne (by omega)]
          have : h + 1 + k = h + (k + 1) := by omega
          rw [this]; exact hbl)
        { state := dfBlank
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = stT then
              (c.work i).writeAndMove Γw.blank.toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread']
          show (((c.work stT).write Γw.blank.toΓ).move Dir3.right).cells = _
          have hw : (c.work stT).write Γw.blank.toΓ
              = { c.work stT with
                  cells := Function.update (c.work stT).cells (c.work stT).head Γw.blank.toΓ } := by
            unfold Tape.write
            rw [ite_eq_right (by omega)]
          rw [hw]
          show Function.update (c.work stT).cells (c.work stT).head Γw.blank.toΓ = _
          rw [hcW, hhead]
          rfl)
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hread']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hhead])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi => by
          dsimp only
          rw [ite_eq_right hi, idle_tape_id (hoth i hi)]
          exact hoth i hi)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_⟩
    · rw [hwt']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext j
      by_cases hj1 : h + 1 ≤ j ∧ j < h + 1 + k
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
      · rw [ite_eq_right hj1]
        by_cases hje : j = h
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi
      rw [hoth' i hi]
      show (if i = stT then _ else _) = _
      rw [ite_eq_right hi]
      exact idle_tape_id (hoth i hi)

-- ════════════════════════════════════════════════════════════════════════
-- Copy-field loop (dfCopy)
-- ════════════════════════════════════════════════════════════════════════

/-- The default path's qhalt-field copy: from `dfCopy` with the state head
    at `a ≥ 1` and the desc head at `b ≥ 1`, where the desc field ends at
    distance `k` (first `□`), copy the field onto state cells `a..a+k-1`
    and stop (one idle transition on the `□`) in `k + 1` steps. Desc cells
    and all other tapes exactly preserved.
@isnad1 id=ex.14h6v.s9.1925e35f738c from=translated src=- shape=b7ac2b9c vocab=7c1ebce8
-/
theorem dfCopy_loop (W : ℕ → Γ) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (k : ℕ) (V : ℕ → Γ), (∀ j, 1 ≤ j → V j ≠ Γ.start) →
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
      (∀ j, j < k → W (b + j) ≠ Γ.blank) → W (b + k) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = dfCopy →
      (c.work stT).cells = V → (c.work stT).head = a →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (k + 1) c c' ∧
        c'.state = dfStRew3 ∧
        c'.work stT = ⟨a + k, fun j => if a ≤ j ∧ j < a + k then W (b + (j - a)) else V j⟩ ∧
        c'.work dsT = ⟨b + k, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  intro k
  induction k with
  | zero =>
    intro V hVns a b ha hb hnb hbl c hst hcV hheadV hcW hheadW hin hout hoth
    have hreadd : (c.work dsT).read = Γ.blank := by
      simp only [Tape.read, hheadW, hcW]
      simpa using hbl
    have hreads : (c.work stT).read ≠ Γ.start := by
      simp only [Tape.read, hheadV, hcV]
      exact hVns a ha
    have harm := arm_dfCopy c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_left hreadd] at harm
    have hstep := step_mkAct (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, idle_input_id hin, idle_tape_id hout,
      fun i hi hi' => idle_tape_id (hoth i hi hi')⟩
    · show (c.work stT).writeAndMove _ _ = _
      rw [idle_tape_id hreads]
      have hV : (fun j => if a ≤ j ∧ j < a + 0 then W (b + (j - a)) else V j) = V := by
        funext j
        rw [ite_eq_right (by omega)]
      rw [hV, ← hcV, show a + 0 = (c.work stT).head from by rw [hheadV]; omega]
    · show (c.work dsT).writeAndMove _ _ = _
      rw [idle_tape_id (by rw [hreadd]; simp)]
      rw [← hcW, show b + 0 = (c.work dsT).head from by rw [hheadW]; omega]
  | succ k ih =>
    intro V hVns a b ha hb hnb hbl c hst hcV hheadV hcW hheadW hin hout hoth
    have hreadd : (c.work dsT).read = W b := by
      simp [Tape.read, hheadW, hcW]
    have hreadnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadd]
      simpa using hnb 0 (by omega)
    have hreadd' : (c.work dsT).read ≠ Γ.start := by
      rw [hreadd]; exact hWns b hb
    have hreads : (c.work stT).read ≠ Γ.start := by
      simp only [Tape.read, hheadV, hcV]
      exact hVns a ha
    have harm := arm_dfCopy c.input.read (fun i => (c.work i).read) c.output.read
    rw [ite_eq_right hreadnb] at harm
    have hstep := step_act2 (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadd', hreadd]
    have hVupd : ∀ j, 1 ≤ j → Function.update V a (W b) j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = a
      · subst hje; rw [Function.update_self]; exact hWns b hb
      · rw [Function.update_of_ne hje]; exact hVns j hj
    obtain ⟨c', hreach, hst', hwtS', hwtD', hin', hout', hoth'⟩ :=
      ih (Function.update V a (W b)) hVupd (a + 1) (b + 1) (by omega) (by omega)
        (fun j hj => by
          have := hnb (j + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
        (by
          have : b + 1 + k = b + (k + 1) := by omega
          rw [this]; exact hbl)
        { state := dfCopy
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = stT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hreads]
          show (((c.work stT).write _).move Dir3.right).cells = _
          have hw : (c.work stT).write (readBackWrite ((c.work dsT).read)).toΓ
              = { c.work stT with
                  cells := Function.update (c.work stT).cells (c.work stT).head
                    (readBackWrite ((c.work dsT).read)).toΓ } := by
            unfold Tape.write
            rw [ite_eq_right (by omega)]
          rw [hw]
          show Function.update (c.work stT).cells (c.work stT).head _ = _
          rw [hcV, hheadV, hWb])
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hreads]
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadV])
        (by
          dsimp only
          rw [ite_eq_right (by decide : dsT ≠ stT), ite_eq_left rfl, ite_eq_right hreadd',
            tape_readBackWrite_preserves _ _ (Or.inr hreadd'), hcW])
        (by
          dsimp only
          rw [ite_eq_right (by decide : dsT ≠ stT), ite_eq_left rfl, ite_eq_right hreadd']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi hi' => by
          dsimp only
          rw [ite_eq_right hi, ite_eq_right hi', idle_tape_id (hoth i hi hi')]
          exact hoth i hi hi')
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtS']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext j
      by_cases hj1 : a + 1 ≤ j ∧ j < a + 1 + k
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [ite_eq_right hj1]
        by_cases hje : j = a
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg W (by omega)
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hwtD']
      exact congrArg (fun n => (⟨n, W⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi hi'
      rw [hoth' i hi hi']
      show (if i = stT then _ else if i = dsT then _ else _) = _
      rw [ite_eq_right hi, ite_eq_right hi']
      exact idle_tape_id (hoth i hi hi')

end TM.UTMBody

end Complexity
