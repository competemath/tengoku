/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine
public import Tengoku

/-!
# TM–NTM embedding: proof internals

Helper lemmas for `TM.toNTM_accepts_iff`, showing that the DTM step function
and the NTM trace on `toNTM` compute the same thing.
-/

public section

namespace Complexity

variable {n : ℕ}

private lemma TM.toNTM_trace_step (tm : TM n) {c : Cfg n tm.Q}
    (T : ℕ) (choices : Fin (T + 1) → Bool) (hne : c.state ≠ tm.qhalt) :
    tm.toNTM.trace (T + 1) choices c =
    tm.toNTM.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
      ((tm.step c).get (by simp [TM.step, hne])) := by
  simp [NTM.trace, hne, TM.toNTM, TM.step]

private lemma TM.reaches_toNTM_trace (tm : TM n) {a c' : Cfg n tm.Q}
    (hreach : tm.reaches a c') :
    ∃ T, ∀ (ch : Fin T → Bool), tm.toNTM.trace T ch a = c' := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => rfl⟩
  | @head a₀ b₀ hstep _ ih =>
    obtain ⟨T, hT⟩ := ih
    have hne : a₀.state ≠ tm.qhalt := by
      rw [TM.stepRel] at hstep; exact state_ne_qhalt_of_step hstep
    refine ⟨T + 1, fun ch => ?_⟩
    rw [tm.toNTM_trace_step T ch hne]
    have : (tm.step a₀).get (by simp [TM.step, hne]) = b₀ := by
      simp [TM.stepRel] at hstep; simp [hstep]
    rw [this]; exact hT _

/--
@isnad1 id=reaches.0h5v.s4.16df23b7d248 from=translated src=- shape=fc0a941d vocab=1ceb5903
-/
lemma TM.toNTM_trace_reaches (tm : TM n) (c : Cfg n tm.Q)
    (T : ℕ) (choices : Fin T → Bool) :
    tm.reaches c (tm.toNTM.trace T choices c) := by
  induction T generalizing c with
  | zero => exact Relation.ReflTransGen.refl
  | succ T ih =>
    dsimp only [NTM.trace, TM.toNTM]
    split
    · exact Relation.ReflTransGen.refl
    · next hne =>
      have hne : c.state ≠ tm.qhalt := hne
      exact Relation.ReflTransGen.head
        (show tm.stepRel c _ by simp [TM.stepRel, TM.step, hne])
        (ih _ _)

/-- For `toNTM`, the trace is independent of the choice sequence since both
    transition functions are identical.
@isnad1 id=eq.0h6v.s5.4b048567a03e from=translated src=- shape=1f81c1f8 vocab=37958248
-/
lemma TM.toNTM_trace_choice_irrel (tm : TM n) (T : ℕ) (c : Cfg n tm.Q)
    (ch₁ ch₂ : Fin T → Bool) :
    tm.toNTM.trace T ch₁ c = tm.toNTM.trace T ch₂ c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    dsimp only [NTM.trace, TM.toNTM]
    split
    · rfl
    · exact ih _ _ _

/-- If a DTM halts within `t ≤ T` steps, then `toNTM.trace T` reaches the same
    halted configuration regardless of choices.
@isnad1 id=eq.3h7v.s5.201f80d6d95b from=translated src=- shape=fe0e1954 vocab=8cc4f4e9
-/
lemma TM.toNTM_trace_of_reachesIn (tm : TM n) {c c' : Cfg n tm.Q}
    {t T : ℕ} (h : tm.reachesIn t c c') (hhalt : tm.halted c')
    (hle : t ≤ T) (ch : Fin T → Bool) :
    tm.toNTM.trace T ch c = c' := by
  induction T generalizing c t with
  | zero =>
    have : t = 0 := by omega
    subst this; cases h; rfl
  | succ T ih =>
    by_cases hh : c.state = tm.qhalt
    · -- c is halted → t = 0 → c = c'
      have : t = 0 := by
        by_contra hp; obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
        cases h with | step hs _ => simp [TM.step, hh] at hs
      subst this; cases h; simp [NTM.trace, TM.toNTM, hh]
    · -- c not halted → t > 0 → peel one step
      have ht_pos : t ≠ 0 := by
        intro h0; subst h0; cases h; exact hh hhalt
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_pos
      obtain ⟨c_mid, hstep, hrest⟩ :
          ∃ c_mid, tm.step c = some c_mid ∧ tm.reachesIn t' c_mid c' := by
        cases h with | step hs hr => exact ⟨_, hs, hr⟩
      rw [tm.toNTM_trace_step T ch hh]
      have : (tm.step c).get (by simp [TM.step, hh]) = c_mid := by
        simp [hstep]
      rw [this]
      exact ih hrest (by omega) _

/-- The DTM and its NTM embedding agree on acceptance.
@isnad1 id=iff.0h3v.s4.94967f81840c from=translated src=- shape=6789761e vocab=39f6a5ba
-/
theorem TM.toNTM_accepts_iff (tm : TM n) (x : List Bool) :
    tm.Accepts x ↔ (tm.toNTM).Accepts x := by
  constructor
  · rintro ⟨c', hreach, hhalt, hout⟩
    obtain ⟨T, hT⟩ := tm.reaches_toNTM_trace hreach
    exact ⟨T, fun _ => false,
      by change (tm.toNTM.trace T _ (tm.initCfg x)).state = _; rw [hT]; exact hhalt,
      by change (tm.toNTM.trace T _ (tm.initCfg x)).output.cells 1 = _; rw [hT]; exact hout⟩
  · rintro ⟨T, choices, hhalt, hout⟩
    exact ⟨_, tm.toNTM_trace_reaches _ T choices, hhalt, hout⟩

/-- If a DTM decides `L` in time `f`, then its NTM embedding also decides `L`
    in time `f`. This is the key internal lemma for `DTIME ⊆ NTIME`.
@isnad1 id=decidesi.1h4v.s4.5acce4d4534e from=translated src=- shape=0e599073 vocab=5edc26d8
-/
theorem TM.toNTM_decidesInTime (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (h : tm.DecidesInTime L f) : tm.toNTM.DecidesInTime L f := by
  refine ⟨?_, ?_⟩
  · -- AllPathsHaltIn
    intro x choices
    obtain ⟨c', t, hle, hreach, hhalt, _, _⟩ := h x
    have htrace := tm.toNTM_trace_of_reachesIn hreach hhalt hle choices
    change (tm.toNTM.trace _ choices (tm.initCfg x)).state = tm.qhalt
    rw [htrace]; exact hhalt
  · -- x ∈ L ↔ AcceptsInTime
    intro x; constructor
    · -- x ∈ L → AcceptsInTime
      intro hx
      obtain ⟨c', t, hle, hreach, hhalt, hyes, _⟩ := h x
      refine ⟨fun _ => false, ?_, ?_⟩
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).state = _
        rw [tm.toNTM_trace_of_reachesIn hreach hhalt hle]; exact hhalt
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).output.cells 1 = _
        rw [tm.toNTM_trace_of_reachesIn hreach hhalt hle]; exact hyes hx
    · -- AcceptsInTime → x ∈ L
      intro ⟨choices, hhalt_ch, hout_ch⟩
      obtain ⟨c', t, hle, hreach, hhalt, _, hno⟩ := h x
      by_contra hxL
      have htrace := tm.toNTM_trace_of_reachesIn hreach hhalt hle choices
      change (tm.toNTM.trace _ choices (tm.initCfg x)).output.cells 1 = _ at hout_ch
      rw [htrace] at hout_ch
      have := hno hxL
      simp_all

/-- Work tape heads grow by at most 1 per step. -/
private lemma TM.work_head_step_bound (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.step c = some c') (i : Fin n) :
    (c'.work i).head ≤ (c.work i).head + 1 := by
  simp only [TM.step] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact Tape.head_writeAndMove_le _ _ _

/-- The input head grows by at most one in a machine step. -/
private lemma TM.input_head_step_bound (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.step c = some c') : c'.input.head ≤ c.input.head + 1 := by
  simp only [TM.step] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact Tape.head_move_le _ _

/-- The output head grows by at most one in a machine step. -/
private lemma TM.output_head_step_bound (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.step c = some c') : c'.output.head ≤ c.output.head + 1 := by
  simp only [TM.step] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact Tape.head_writeAndMove_le _ _ _

/-- After `t` steps, each work tape head is at most `t` plus its initial value.
@isnad1 id=le.1h6v.s5.ae388bfa7736 from=translated src=- shape=0a4cc04f vocab=2e761ced
-/
theorem TM.work_head_reachesIn_bound (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') (i : Fin n) :
    (c'.work i).head ≤ (c.work i).head + t := by
  induction h with
  | zero => omega
  | @step c₀ c_mid _ _ hstep _ ih =>
    have := tm.work_head_step_bound hstep i
    omega

/-- After `t` steps, the input head is at most `t` plus its initial value.
@isnad1 id=le.1h5v.s5.32d5016547e6 from=translated src=- shape=aff3bac1 vocab=eea1ff0b
-/
theorem TM.input_head_reachesIn_bound (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') : c'.input.head ≤ c.input.head + t := by
  induction h with
  | zero => omega
  | @step c₀ c_mid _ _ hstep _ ih =>
    have := tm.input_head_step_bound hstep
    omega

/-- After `t` steps, the output head is at most `t` plus its initial value.
@isnad1 id=le.1h5v.s5.f6a004535585 from=translated src=- shape=aff3bac1 vocab=c36d5fd0
-/
theorem TM.output_head_reachesIn_bound (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') : c'.output.head ≤ c.output.head + t := by
  induction h with
  | zero => omega
  | @step c₀ c_mid _ _ hstep _ ih =>
    have := tm.output_head_step_bound hstep
    omega

/-- Deterministic runs have unique endpoints: reaching two configurations in
    the same number of steps forces them to coincide.
@isnad1 id=eq.2h6v.s5.fef47077ae35 from=translated src=- shape=973fa831 vocab=303cafe7
-/
theorem TM.reachesIn_right_unique {tm : TM n} {t : ℕ} {c c' c'' : Cfg n tm.Q}
    (h₁ : tm.reachesIn t c c') (h₂ : tm.reachesIn t c c'') : c' = c'' := by
  induction h₁ with
  | zero => cases h₂; rfl
  | step hs₁ _ ih₁ =>
    cases h₂ with
    | step hs₂ h₂' =>
      have heq : some _ = some _ := hs₁.symm.trans hs₂
      simp only [Option.some.injEq] at heq; subst heq
      exact ih₁ h₂'

/-- Convert `reaches` to `reachesIn`.
@isnad1 id=ex.1h4v.s5.84f688699334 from=translated src=- shape=7310073c vocab=2087c9c7
-/
theorem TM.reaches_to_reachesIn (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.reaches c c') : ∃ t, tm.reachesIn t c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero⟩
  | head hstep _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + 1, .step hstep ht⟩

/-- A DTM step is deterministic: `step` is a function. -/
private lemma TM.step_det (tm : TM n) {c c₁ c₂ : Cfg n tm.Q}
    (h₁ : tm.step c = some c₁) (h₂ : tm.step c = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- If a DTM halts at step `t_halt`, then any `reachesIn t` has `t ≤ t_halt`.
@isnad1 id=le.3h7v.s5.df2250a6bd16 from=translated src=- shape=4bf82da9 vocab=3f7239c9
-/
theorem TM.reachesIn_le_halt (tm : TM n) {c c' c_halt : Cfg n tm.Q}
    {t t_halt : ℕ} (hr : tm.reachesIn t c c')
    (hh : tm.reachesIn t_halt c c_halt) (hhalt : tm.halted c_halt) :
    t ≤ t_halt := by
  induction t generalizing c t_halt with
  | zero => omega
  | succ t ih =>
    cases hr with | @step c₀ c_mid _ _ hs hr' =>
    cases t_halt with
    | zero =>
      cases hh
      simp [TM.step, hhalt] at hs
    | succ t_halt' =>
      cases hh with | step hs' hh' =>
      have := tm.step_det hs hs'
      subst this
      exact Nat.succ_le_succ (ih hr' hh')

/-- Initial work tape heads are all at position 0.
@isnad1 id=eq.0h4v.s4.d0dcd7788c39 from=translated src=- shape=e501a8c2 vocab=459ee58d
-/
lemma TM.initCfg_work_head_zero (tm : TM n) (x : List Bool) (i : Fin n) :
    ((tm.initCfg x).work i).head = 0 := by
  simp [Tape.init]

/-- The initial input head is at position zero.
@isnad1 id=eq.0h3v.s4.7a7c8a1c4955 from=translated src=- shape=5285afd9 vocab=8d3f0d8e
-/
lemma TM.initCfg_input_head_zero (tm : TM n) (x : List Bool) :
    (tm.initCfg x).input.head = 0 := rfl

/-- The initial output head is at position zero.
@isnad1 id=eq.0h3v.s4.f6d357706e4f from=translated src=- shape=5285afd9 vocab=21ebe32e
-/
lemma TM.initCfg_output_head_zero (tm : TM n) (x : List Bool) :
    (tm.initCfg x).output.head = 0 := rfl

/-- If a DTM is a transducer, so is its NTM embedding.
@isnad1 id=istransd.1h2v.s3.c16f39533571 from=translated src=- shape=08ded1e7 vocab=7ad2b7f6
-/
theorem TM.toNTM_isTransducer (tm : TM n) (h : tm.IsTransducer) : tm.toNTM.IsTransducer := by
  intro b q iHead wHeads oHead
  simp only [TM.toNTM]
  exact h q iHead wHeads oHead

/-- If a DTM decides `L` in space `f`, then its NTM embedding also decides `L`
    in space `f`. The uniform time bound is constructed as the maximum halting
    time over all inputs of each length.
@isnad1 id=decidesi.1h4v.s4.0c5ffd0f702c from=translated src=- shape=0e599073 vocab=262ac4eb
-/
theorem TM.toNTM_decidesInSpace (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (h : tm.DecidesInSpace L f) : tm.toNTM.DecidesInSpace L f := by
  -- Extract per-input halting times
  have hdata : ∀ x, ∃ t c', tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero) := by
    intro x
    obtain ⟨c', hreach, hhalt, hyes, hno⟩ := h.2 x
    obtain ⟨t, hreachIn⟩ := tm.reaches_to_reachesIn hreach
    exact ⟨t, c', hreachIn, hhalt, hyes, hno⟩
  choose t_fn c_fn hreachIn hhalt hyes hno using hdata
  -- Uniform time bound: max halting time over all inputs of each length
  let T : ℕ → ℕ := fun m =>
    Finset.sup (Finset.univ : Finset (Fin m → Bool)) (fun v => t_fn (List.ofFn v))
  have hle_T : ∀ x, t_fn x ≤ T x.length := by
    intro x
    show t_fn x ≤ Finset.sup Finset.univ (fun v => t_fn (List.ofFn v))
    conv_lhs => rw [show x = List.ofFn (fun i : Fin x.length => x[↑i]) from
      (List.ofFn_getElem (xs := x)).symm]
    exact Finset.le_sup (f := fun v => t_fn (List.ofFn v))
      (Finset.mem_univ (fun i : Fin x.length => x[↑i]))
  refine ⟨T, ⟨?_, ?_⟩, ?_⟩
  · -- AllPathsHaltIn
    intro x choices
    have htrace := tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x) choices
    change (tm.toNTM.trace _ choices (tm.initCfg x)).state = tm.qhalt
    rw [htrace]; exact hhalt x
  · -- x ∈ L ↔ AcceptsInTime
    intro x; constructor
    · intro hx
      refine ⟨fun _ => false, ?_, ?_⟩
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).state = tm.qhalt
        rw [tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x)]
        exact hhalt x
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).output.cells 1 = Γ.one
        rw [tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x)]
        exact hyes x hx
    · intro ⟨choices, hhalt_ch, hout_ch⟩
      by_contra hxL
      have htrace := tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x) choices
      change (tm.toNTM.trace _ choices (tm.initCfg x)).output.cells 1 = _ at hout_ch
      rw [htrace] at hout_ch
      have := hno x hxL
      simp_all
  · -- Space bound
    intro x choices t' ht'
    have hreach := tm.toNTM_trace_reaches (tm.initCfg x) t'
      (fun j : Fin t' => choices ⟨j.val, by omega⟩)
    exact h.1 x _ hreach

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Tape invariant helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Cell 0 stays Γ.start after write + move. -/
private theorem tape_cell0_preserved (t : Tape) (s : Γ) (d : Dir3)
    (h0 : t.cells 0 = Γ.start) :
    ((t.write s).move d).cells 0 = Γ.start := by
  rw [Tape.move_cells]; simp only [Tape.write]
  split
  · exact h0
  · simp only [Function.update, dite_eq_right (show (0 : ℕ) ≠ t.head from fun h => by omega)]
    exact h0

/-- Cells ≥ 1 stay non-Γ.start after writing a non-Γ.start value. -/
private theorem tape_noStart_preserved (t : Tape) (s : Γ) (d : Dir3)
    (hs : s ≠ Γ.start) (hno : ∀ i, i ≥ 1 → t.cells i ≠ Γ.start) :
    ∀ i, i ≥ 1 → ((t.write s).move d).cells i ≠ Γ.start := by
  intro i hi; rw [Tape.move_cells]; simp only [Tape.write]
  split
  · exact hno i hi
  · simp only [Function.update]; split
    · next heq => subst heq; exact hs
    · exact hno i hi

/-- Output cell 0 = Γ.start is preserved by one TM step. -/
private theorem output_cell0_step {tm : TM n} {c c' : Cfg n tm.Q}
    (hs : tm.step c = some c') (h0 : c.output.cells 0 = Γ.start) :
    c'.output.cells 0 = Γ.start := by
  have hne := state_ne_qhalt_of_step hs
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hs; subst hs
  exact tape_cell0_preserved _ _ _ h0

/-- Work-tape cell 0 is preserved by one TM step. -/
private theorem work_cell0_step {tm : TM n} {c c' : Cfg n tm.Q}
    (idx : Fin n) (hs : tm.step c = some c')
    (h0 : (c.work idx).cells 0 = Γ.start) :
    (c'.work idx).cells 0 = Γ.start := by
  have hne := state_ne_qhalt_of_step hs
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hs
  subst hs
  exact tape_cell0_preserved _ _ _ h0

/-- Output cells ≥ 1 ≠ Γ.start is preserved by one TM step. -/
private theorem output_noStart_step {tm : TM n} {c c' : Cfg n tm.Q}
    (hs : tm.step c = some c') (hno : ∀ i, i ≥ 1 → c.output.cells i ≠ Γ.start) :
    ∀ i, i ≥ 1 → c'.output.cells i ≠ Γ.start := by
  have hne := state_ne_qhalt_of_step hs
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hs; subst hs
  exact tape_noStart_preserved _ _ _ (Γw.toΓ_ne_start _) hno

/--
@isnad1 id=eq.2h5v.s5.43b93565d997 from=translated src=- shape=7ac19dc1 vocab=dcb91789
-/
theorem output_cells_zero_eq_start_of_reachesIn {tm : TM n} {t : ℕ} {c₀ c : Cfg n tm.Q}
    (h : tm.reachesIn t c₀ c) (h0 : c₀.output.cells 0 = Γ.start) :
    c.output.cells 0 = Γ.start := by
  induction h with
  | zero => exact h0
  | step hs _ ih => exact ih (output_cell0_step hs h0)

/-- Cell zero of any named work tape remains the left-end marker throughout a
deterministic run.
@isnad1 id=eq.2h6v.s5.5a67add7f007 from=translated src=- shape=e08df6fe vocab=e2bf0172
-/
theorem work_cells_zero_eq_start_of_reachesIn {tm : TM n} {t : ℕ}
    {c₀ c : Cfg n tm.Q} (idx : Fin n) (h : tm.reachesIn t c₀ c)
    (h0 : (c₀.work idx).cells 0 = Γ.start) :
    (c.work idx).cells 0 = Γ.start := by
  induction h with
  | zero => exact h0
  | step hs _ ih => exact ih (work_cell0_step idx hs h0)

/--
@isnad1 id=ne.3h6v.s6.a328b6d7b954 from=translated src=- shape=72831b3b vocab=562b51b9
-/
theorem output_cells_ne_start_of_reachesIn {tm : TM n} {t : ℕ} {c₀ c : Cfg n tm.Q}
    (h : tm.reachesIn t c₀ c)
    (hno : ∀ i, i ≥ 1 → c₀.output.cells i ≠ Γ.start) :
    ∀ i, i ≥ 1 → c.output.cells i ≠ Γ.start := by
  induction h with
  | zero => exact hno
  | step hs _ ih => exact ih (output_noStart_step hs hno)

/--
@isnad1 id=eq.1h4v.s5.3ad5cd541679 from=translated src=- shape=6ac49ebf vocab=4abdcd25
-/
theorem input_cells_eq_of_step {tm : TM n} {c c' : Cfg n tm.Q}
    (hs : tm.step c = some c') : c'.input.cells = c.input.cells := by
  have hne := state_ne_qhalt_of_step hs
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hs; subst hs
  exact Tape.move_cells _ _

/--
@isnad1 id=eq.1h5v.s5.519a112b1f42 from=translated src=- shape=96cd9589 vocab=6a7f0ea1
-/
theorem input_cells_eq_of_reachesIn {tm : TM n} {t : ℕ} {c₀ c : Cfg n tm.Q}
    (h : tm.reachesIn t c₀ c) : c.input.cells = c₀.input.cells := by
  induction h with
  | zero => rfl
  | step hs _ ih => rw [ih, input_cells_eq_of_step hs]

/-- After one step, each tape head increases by at most 1. -/
private theorem step_head_bound (tm : TM n) (c c' : Cfg n tm.Q)
    (hs : tm.step c = some c') :
    c'.input.head ≤ c.input.head + 1 ∧
    c'.output.head ≤ c.output.head + 1 ∧
    ∀ i, (c'.work i).head ≤ (c.work i).head + 1 := by
  unfold TM.step at hs
  split at hs
  · simp at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    dsimp only []
    set δr := tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    refine ⟨Tape.head_move_le _ δr.2.2.2.1, ?_, fun i => ?_⟩
    · have hm := Tape.head_move_le (c.output.write δr.2.2.1.toΓ) δr.2.2.2.2.2
      simp only [Tape.write_head] at hm
      exact hm
    · have hm := Tape.head_move_le ((c.work i).write (δr.2.1 i).toΓ) (δr.2.2.2.2.1 i)
      simp only [Tape.write_head] at hm
      exact hm

/-- A tape head moves at most one cell per step, relative to an arbitrary
starting configuration.
@isnad1 id=and.1h5v.s6.1cca60d4a2d6 from=translated src=- shape=9c91d1c8 vocab=44e444f8
-/
theorem head_le_start_add_of_reachesIn (tm : TM n)
    {t : ℕ} {c₀ c : Cfg n tm.Q}
    (hreach : tm.reachesIn t c₀ c) :
    c.input.head ≤ c₀.input.head + t ∧
    c.output.head ≤ c₀.output.head + t ∧
    ∀ i, (c.work i).head ≤ (c₀.work i).head + t := by
  induction hreach with
  | zero => simp
  | step hstep _ ih =>
    obtain ⟨ih_in, ih_out, ih_work⟩ := ih
    obtain ⟨hs_in, hs_out, hs_work⟩ := step_head_bound tm _ _ hstep
    exact ⟨by omega, by omega, fun i => by
      have := hs_work i
      have := ih_work i
      omega⟩

/-- A tape head moves at most 1 cell per step. After `t` steps starting
    from `initCfg`, the head is at position ≤ `t`.
@isnad1 id=and.1h5v.s6.4331fe491eb3 from=translated src=- shape=e84903cf vocab=ea2a5053
-/
theorem head_le_of_reachesIn (tm : TM n)
    {t : ℕ} {c : Cfg n tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c) :
    c.input.head ≤ t ∧ c.output.head ≤ t ∧ ∀ i, (c.work i).head ≤ t := by
  have h := head_le_start_add_of_reachesIn tm hreach
  simpa [Tape.init] using h
end TM

/-- The invariant is preserved across one DTM step, on every tape.
@isnad1 id=and.4h4v.s6.36dc80df5b5c from=translated src=- shape=fd8bdc35 vocab=e8c09c90
-/
theorem Tape.StartInvariant.step {n : ℕ} (tm : TM n)
    {c c' : Cfg n tm.Q} (hstep : tm.step c = some c')
    (hinp : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
    c'.output.StartInvariant := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · show (c.input.move _).cells 0 = _
        rw [Tape.move_cells]; exact hinp.1
      · intro j hj
        show (c.input.move _).cells j ≠ _
        rw [Tape.move_cells]; exact hinp.2 j hj
    · intro i
      exact Tape.StartInvariant.writeAndMove (hwork i) _ _
    · exact Tape.StartInvariant.writeAndMove hout _ _

namespace NTM

variable {n : ℕ}

/-- NTM traces never alter input tape cells; the input tape is read-only and
    only its head moves.
@isnad1 id=eq.0h5v.s5.a98c6b18347b from=translated src=- shape=8615ea41 vocab=04a370ac
-/
theorem input_cells_trace (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q) :
    (tm.trace T choices c).input.cells = c.input.cells := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      by_cases hhalt : c.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, ite_false]
        rw [ih]
        cases (tm.δ (choices ⟨0, Nat.zero_lt_succ T⟩) c.state c.input.read
          (fun i => (c.work i).read) c.output.read).2.2.2.1 <;> rfl

/-- During an NTM trace, the input head increases by at most one per step.
@isnad1 id=le.0h5v.s5.c0e1d1d9d223 from=translated src=- shape=b6e444e6 vocab=26e2f0c9
-/
theorem input_head_trace_le (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q) :
    (tm.trace T choices c).input.head ≤ c.input.head + T := by
  induction T generalizing c with
  | zero =>
      simp [NTM.trace]
  | succ T ih =>
      by_cases hhalt : c.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, ite_false]
        let b := choices ⟨0, Nat.zero_lt_succ T⟩
        let tr := tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
        let c' : Cfg n tm.Q :=
          { state := tr.1
            input := c.input.move tr.2.2.2.1
            work := fun i => (c.work i).writeAndMove (tr.2.1 i) (tr.2.2.2.2.1 i)
            output := c.output.writeAndMove tr.2.2.1 tr.2.2.2.2.2 }
        have hrec := ih (fun i => choices ⟨i.val + 1, by omega⟩) c'
        have hstep : c'.input.head ≤ c.input.head + 1 := by
          exact Tape.head_move_le c.input tr.2.2.2.1
        change (tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c').input.head ≤
          c.input.head + (T + 1)
        calc
          (tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c').input.head
              ≤ c'.input.head + T := hrec
          _ ≤ (c.input.head + 1) + T := by omega
          _ ≤ c.input.head + (T + 1) := by omega

/-- During an NTM trace, every work-tape head increases by at most one per step.
@isnad1 id=le.0h6v.s5.883f93be91c3 from=translated src=- shape=1923d92f vocab=7f6cc55a
-/
theorem work_head_trace_le (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q) (i : Fin n) :
    ((tm.trace T choices c).work i).head ≤ (c.work i).head + T := by
  induction T generalizing c with
  | zero => simp [NTM.trace]
  | succ T ih =>
      by_cases hhalt : c.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, ite_false]
        let b := choices ⟨0, Nat.zero_lt_succ T⟩
        let tr := tm.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read
        let c' : Cfg n tm.Q :=
          { state := tr.1
            input := c.input.move tr.2.2.2.1
            work := fun j => (c.work j).writeAndMove (tr.2.1 j) (tr.2.2.2.2.1 j)
            output := c.output.writeAndMove tr.2.2.1 tr.2.2.2.2.2 }
        have hrec := ih (fun j => choices ⟨j.val + 1, by omega⟩) c'
        have hstep : (c'.work i).head ≤ (c.work i).head + 1 := by
          exact Tape.head_writeAndMove_le _ _ _
        change ((tm.trace T (fun j => choices ⟨j.val + 1, by omega⟩) c').work i).head ≤
          (c.work i).head + (T + 1)
        omega

/-- During an NTM trace, the output-tape head increases by at most one per step.
@isnad1 id=le.0h5v.s5.de77ba0188cc from=translated src=- shape=b6e444e6 vocab=4cc6cac1
-/
theorem output_head_trace_le (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q) :
    (tm.trace T choices c).output.head ≤ c.output.head + T := by
  induction T generalizing c with
  | zero => simp [NTM.trace]
  | succ T ih =>
      by_cases hhalt : c.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, ite_false]
        let b := choices ⟨0, Nat.zero_lt_succ T⟩
        let tr := tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
        let c' : Cfg n tm.Q :=
          { state := tr.1
            input := c.input.move tr.2.2.2.1
            work := fun i => (c.work i).writeAndMove (tr.2.1 i) (tr.2.2.2.2.1 i)
            output := c.output.writeAndMove tr.2.2.1 tr.2.2.2.2.2 }
        have hrec := ih (fun i => choices ⟨i.val + 1, by omega⟩) c'
        have hstep : c'.output.head ≤ c.output.head + 1 := by
          exact Tape.head_writeAndMove_le _ _ _
        change (tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c').output.head ≤
          c.output.head + (T + 1)
        omega

/-- Split a two-step trace into two one-step traces.
@isnad1 id=eq.0h4v.s6.44d45498ff2d from=translated src=- shape=9e4a9481 vocab=47237d27
-/
theorem trace_two (tm : NTM n) (choices : Fin 2 → Bool) (c : Cfg n tm.Q) :
    tm.trace 2 choices c =
      tm.trace 1 (fun _ => choices ⟨1, by omega⟩)
        (tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c) := by
  by_cases hhalt : c.state = tm.qhalt
  · simp [NTM.trace, hhalt]
  · simp [NTM.trace, hhalt]

/-- Split the first step off a nonzero trace. If the machine is already
    halted, both sides reduce to the starting configuration.
@isnad1 id=eq.0h5v.s7.f3386e80bff2 from=translated src=- shape=78a67545 vocab=762bd132
-/
theorem trace_succ (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 1) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 1) choices c =
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c) := by
  by_cases hhalt : c.state = tm.qhalt
  · simp [NTM.trace, hhalt]
    exact (tm.trace_halted T (fun i => choices ⟨i.val + 1, by omega⟩) hhalt).symm
  · simp [NTM.trace, hhalt]

/-- Split the first two steps off a trace.
@isnad1 id=eq.0h5v.s7.6df98b74c1d7 from=translated src=- shape=3ebc1d1f vocab=fc87a864
-/
theorem trace_add_two (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 2) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 2) choices c =
      tm.trace T (fun i => choices ⟨i.val + 2, by omega⟩)
        (tm.trace 2 (fun i => choices ⟨i.val, by omega⟩) c) := by
  change tm.trace ((T + 1) + 1) choices c = _
  rw [trace_succ tm (T + 1) choices c]
  rw [trace_succ tm T
    (fun i : Fin (T + 1) => choices ⟨i.val + 1, by omega⟩)
    (tm.trace 1 (fun x => choices ⟨0, by omega⟩) c)]
  rw [← trace_two tm (fun i : Fin 2 => choices ⟨i.val, by omega⟩) c]

/-- Reindex a trace along an equality of time bounds.
@isnad1 id=eq.1h6v.s5.27e1394a9d38 from=translated src=- shape=0b590995 vocab=b4855a8a
-/
theorem trace_cast (tm : NTM n) {T T' : ℕ} (h : T = T')
    (choices : Fin T → Bool) (c : Cfg n tm.Q) :
    tm.trace T choices c =
      tm.trace T' (fun i => choices (Fin.cast h.symm i)) c := by
  cases h
  rfl

/-- Split the first `T` steps off a trace.

This version uses `Fin.castLE`/`Fin.natAdd` for the prefix and suffix choice
sequences, which keeps later proofs away from ad-hoc dependent index casts.
@isnad1 id=eq.0h6v.s6.3bbb48bd4031 from=translated src=- shape=9da69ddb vocab=c6867e7e
-/
theorem trace_add (tm : NTM n) (T U : ℕ)
    (choices : Fin (T + U) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + U) choices c =
      tm.trace U (fun i => choices (Fin.natAdd T i))
        (tm.trace T (fun i => choices (Fin.castLE (Nat.le_add_right T U) i)) c) := by
  induction T generalizing U c with
  | zero =>
    have h := trace_cast tm (Nat.zero_add U) choices c
    rw [h]
    congr 1
    funext i
    apply congrArg choices
    exact Fin.ext (by simp [Fin.natAdd])
  | succ T ih =>
    let choicesCast : Fin ((T + U) + 1) → Bool :=
      fun i => choices (Fin.cast (by omega : (T + U) + 1 = (T + 1) + U) i)
    have hcast := trace_cast tm (by omega : (T + 1) + U = (T + U) + 1) choices c
    rw [hcast]
    rw [trace_succ tm (T + U) choicesCast c]
    rw [ih U (fun i : Fin (T + U) => choicesCast ⟨i.val + 1, by omega⟩)
      (tm.trace 1 (fun _ => choicesCast ⟨0, by omega⟩) c)]
    let prefixFinal : Fin (T + 1) → Bool :=
      fun i => choices (Fin.castLE (Nat.le_add_right (T + 1) U) i)
    have hprefix :
        tm.trace (T + 1) prefixFinal c =
          tm.trace T
            (fun i : Fin T =>
              choicesCast ⟨(Fin.castLE (Nat.le_add_right T U) i).val + 1, by omega⟩)
            (tm.trace 1 (fun _ => choicesCast ⟨0, by omega⟩) c) := by
      simpa [choicesCast, prefixFinal, Fin.castLE, Fin.cast] using
        trace_succ tm T prefixFinal c
    rw [← hprefix]
    congr 1
    funext i
    apply congrArg choices
    exact Fin.ext (by simp [Fin.val_natAdd]; omega)

/-- Split a trace driven by an infinite choice stream at a natural-number
offset. This is the cast-free form used by fixed-schedule simulations.
@isnad1 id=eq.0h6v.s6.675305db5bce from=translated src=- shape=81ceaa13 vocab=7587ecfd
-/
theorem trace_add_fun (tm : NTM n) (T U : ℕ)
    (choices : ℕ → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + U) (fun i => choices i.val) c =
      tm.trace U (fun i => choices (T + i.val))
        (tm.trace T (fun i => choices i.val) c) := by
  simpa [Fin.castLE, Fin.natAdd] using
    tm.trace_add T U (fun i => choices i.val) c

end NTM

end Complexity
