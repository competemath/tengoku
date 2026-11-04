import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Logic.Function.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms State.frontier` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms step_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms terminal_started_complete` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms terminal_complete` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms progress` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms State.score_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms step_score` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bounded_recovery` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms initial_wellFormed` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms recover_from_roots` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Abstract recovery scheduling — partial formalization.
This models a combinatorial subproblem of `lem:resolve`, not that lemma.
There are no words, de Bruijn edges or signed rules in this module.
ConcreteProgress and ConcreteRecovery realize this scheduling on stored letters;
GeneratingRecovery derives the needed data from generating edited-word families.
The existence of a complete recovery trace is proved, not assumed as an
input hypothesis. Checked with Lean 4.34.0; ManuscriptCounting completes the
catalogue generating-set bound using this scheduling argument.
-/
namespace DeletionCode.Recovery

abbrev Slot := Fin 3

def AdjSlot (a b : Slot) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

inductive Reach {B : Type*} (adj : B → B → Prop) : B → B → Prop
  | refl (b : B) : Reach adj b b
  | tail {a b c : B} : Reach adj a b → adj b c → Reach adj a c

/-- `none` denotes x; `some a` denotes an earlier supplying bubble.-/
structure Data (B : Type*) where
  rank : B → ℕ
  source : B → Slot → Option B
  earlier : ∀ b w a, source b w = some a → rank a < rank b
  adjacent : B → B → Prop
  root : B → Prop
  rooted : ∀ b, ∃ r, root r ∧ Reach adjacent r b

structure State (B : Type*) where
  seed : B → Option Slot
  filled : Finset (B × Slot)

variable {B : Type*} [DecidableEq B]
namespace State

def Started (s : State B) (b : B) : Prop := s.seed b ≠ none

def Done (s : State B) (b : B) (w : Slot) : Prop := (b, w) ∈ s.filled

def Complete (s : State B) (b : B) : Prop := ∀ w, s.Done b w

def Ready (s : State B) (b : B) (w : Slot) : Prop :=
  s.seed b = some w ∨ ∃ v, s.Done b v ∧ AdjSlot v w

def start (s : State B) (b : B) (w : Slot) : State B :=
  ⟨Function.update s.seed b (some w), s.filled⟩

def fill (s : State B) (b : B) (w : Slot) : State B :=
  ⟨s.seed, insert (b, w) s.filled⟩

def WellFormed (M : Data B) (s : State B) : Prop :=
  (∀ b w, s.Done b w → s.Started b) ∧
  (∀ b, M.root b → s.Complete b)

/--
@isnad1 id=started.0h4v.s4.3cd0b0cefe88 from=translated src=- shape=684d6ce2 vocab=33e6e623
-/
theorem started_start (s : State B) (b : B) (w : Slot) :
    (s.start b w).Started b := by simp [Started, start]

/--
@isnad1 id=started.1h5v.s4.81001560c60f from=translated src=- shape=182cd232 vocab=33e6e623
-/
theorem started_start_mono (s : State B) (b a : B) (w : Slot)
    (h : s.Started a) : (s.start b w).Started a := by
  by_cases hab : a = b
  · subst a
    exact started_start s b w
  · have hba : b ≠ a := Ne.symm hab
    simpa [Started, start, hab, hba] using h

/--
@isnad1 id=complete.1h5v.s4.9fa31ece25c9 from=translated src=- shape=182cd232 vocab=987a15db
-/
theorem complete_start (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.start b w).Complete a := h

/--
@isnad1 id=complete.1h5v.s4.a5157cab69fd from=translated src=- shape=182cd232 vocab=fd603cd8
-/
theorem complete_fill (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.fill b w).Complete a := by
  intro v
  exact Finset.mem_insert_of_mem (h v)

/--
@isnad1 id=started.2h5v.s4.92bb2872d141 from=translated src=- shape=9591d3a9 vocab=8c47d063
-/
theorem ready_started (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (h : s.Ready b w) :
    s.Started b := by
  rcases h with hseed | ⟨v, hv, _⟩
  · simp [Started, hseed]
  · exact hs.1 b v hv

/--
@isnad1 id=wellform.1h5v.s4.cf14b300f84e from=translated src=- shape=88b5bb5d vocab=555a05e6
-/
theorem start_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) :
    WellFormed M (s.start b w) := by
  constructor
  · intro a v hav
    exact started_start_mono s b a w (hs.1 a v hav)
  · intro a ha
    exact complete_start s b a w (hs.2 a ha)

/--
@isnad1 id=wellform.2h5v.s5.399a8f6cbb5e from=translated src=- shape=c6a90a2a vocab=d1da1054
-/
theorem fill_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (hb : s.Started b) :
    WellFormed M (s.fill b w) := by
  constructor
  · intro a v hav
    have hmem : (a, v) ∈ insert (b, w) s.filled := hav
    rcases Finset.mem_insert.mp hmem with heq | hold
    · have hab : a = b := congrArg Prod.fst heq
      subst a
      exact hb
    · exact hs.1 a v hold
  · intro a ha
    exact complete_fill s b a w (hs.2 a ha)

/-- An incomplete started bubble has a ready unfilled window.
@isnad1 id=ex.2h3v.s5.889835527e95 from=translated src=- shape=595f4fb8 vocab=359c8a93
-/
theorem frontier (s : State B) (b : B)
    (hb : s.Started b) (hi : ¬ s.Complete b) :
    ∃ w, s.Ready b w ∧ ¬ s.Done b w := by
  classical
  by_contra hn
  have hclosed : ∀ w, s.Ready b w → s.Done b w := by
    intro w hw
    by_contra hnot
    exact hn ⟨w, hw, hnot⟩
  cases hseed : s.seed b with
  | none => exact hb hseed
  | some v =>
    have hv : s.Done b v := hclosed v (Or.inl hseed)
    apply hi
    fin_cases v
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨0, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨2, hv, by norm_num [AdjSlot]⟩)
      have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
end State

open State

/--
Abstract transitions. Any seed-window index is permitted in this model.
A concrete realization must choose one containing a REAL transferred
stretch, so an abstract trace is not automatically a valid decoding.-/
inductive Step (M : Data B) : State B → State B → Prop
  | startAdjacent (s : State B) (a b : B) (w : Slot)
      (ha : s.Complete a) (hab : M.adjacent a b) (hb : ¬ s.Started b) :
      Step M s (s.start b w)
  | startSupplier (s : State B) (b a : B) (w v : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : ¬ s.Started a) :
      Step M s (s.start a v)
  | fillBase (s : State B) (b : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = none) : Step M s (s.fill b w)
  | fillSupplier (s : State B) (b a : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : s.Complete a) :
      Step M s (s.fill b w)

/--
@isnad1 id=wellform.2h4v.s4.b4bdd51e572d from=translated src=- shape=99635e93 vocab=69713565
-/
theorem step_preserves (M : Data B) {s s' : State B}
    (h : Step M s s') (hs : s.WellFormed M) : s'.WellFormed M := by
  cases h with
  | startAdjacent a b w ha hab hb =>
      exact State.start_wellFormed M s hs b w
  | startSupplier b a w v hr hn hsrc ha =>
      exact State.start_wellFormed M s hs a v
  | fillBase b w hr hn hsrc =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)
  | fillSupplier b a w hr hn hsrc ha =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)

/-- Rank induction rules out incomplete started bubbles in a terminal state.
@isnad1 id=complete.2h4v.s5.c725bb5f22f3 from=translated src=- shape=8966ce1d vocab=f90444e8
-/
theorem terminal_started_complete (M : Data B) (s : State B)
    (hstop : ∀ s', ¬ Step M s s') : ∀ b, s.Started b → s.Complete b := by
  classical
  have aux : ∀ r : ℕ, ∀ b, M.rank b = r → s.Started b → s.Complete b := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hr hb
      by_contra hnot
      obtain ⟨w, hw, hmissing⟩ := State.frontier s b hb hnot
      cases hsrc : M.source b w with
      | none => exact hstop _ (Step.fillBase s b w hw hmissing hsrc)
      | some a =>
        by_cases ha : s.Started a
        · have hsmall : M.rank a < r := by
            have he := M.earlier b w a hsrc
            omega
          have hac : s.Complete a := ih (M.rank a) hsmall a rfl ha
          exact hstop _ (Step.fillSupplier s b a w hw hmissing hsrc hac)
        · exact hstop _ (Step.startSupplier s b a w 0 hw hmissing hsrc ha)
  intro b hb
  exact aux (M.rank b) b rfl hb

/--
@isnad1 id=complete.2h4v.s5.3479e5cbb863 from=translated src=- shape=ebc5a71b vocab=7e9ba60f
-/
theorem terminal_complete (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hstop : ∀ s', ¬ Step M s s') :
    ∀ b, s.Complete b := by
  classical
  have hstarted := terminal_started_complete M s hstop
  have along : ∀ {a b}, Reach M.adjacent a b →
      s.Complete a → s.Complete b := by
    intro a b hpath
    induction hpath with
    | refl => exact fun h => h
    | @tail b c hpath hadj ih =>
      intro ha
      have hb : s.Complete b := ih ha
      by_cases hc : s.Started c
      · exact hstarted c hc
      · exact False.elim (hstop _ (Step.startAdjacent s b c 0 hb hadj hc))
  intro b
  obtain ⟨r, hr, hpath⟩ := M.rooted b
  exact along hpath (hs.2 r hr)

/--
@isnad1 id=ex.2h3v.s5.1b35d1b4d344 from=translated src=- shape=3c7239f0 vocab=7e9ba60f
-/
theorem progress (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hincomplete : ¬ ∀ b, s.Complete b) :
    ∃ s', Step M s s' := by
  classical
  by_contra hn
  have hstop : ∀ s', ¬ Step M s s' := by
    intro s' hstep
    exact hn ⟨s', hstep⟩
  exact hincomplete (terminal_complete M s hs hstop)

section Finite
variable [Fintype B]
namespace State

def startedSet (s : State B) : Finset B :=
  Finset.univ.filter (fun b => s.seed b ≠ none)

def score (s : State B) : ℕ := s.startedSet.card + s.filled.card

/--
@isnad1 id=le.0h2v.s5.e193ca2505dc from=translated src=- shape=33e92d3c vocab=e864aeea
-/
theorem score_le (s : State B) : s.score ≤ 4 * Fintype.card B := by
  have h1 : s.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  have h2 : s.filled.card ≤ Fintype.card (B × Slot) := Finset.card_le_univ _
  have h3 : s.filled.card ≤ 3 * Fintype.card B := by
    simpa [Slot, Fintype.card_prod, Nat.mul_comm] using h2
  unfold score
  omega

/--
@isnad1 id=eq.1h4v.s5.bbcad22e5963 from=translated src=- shape=5634bb7c vocab=e2410d1d
-/
theorem score_start (s : State B) (b : B) (w : Slot)
    (hb : ¬ s.Started b) : (s.start b w).score = s.score + 1 := by
  classical
  have heq : (s.start b w).startedSet = insert b s.startedSet := by
    apply Finset.ext
    intro a
    change (a ∈ Finset.univ.filter
      (fun x => Function.update s.seed b (some w) x ≠ none)) ↔
      a ∈ insert b (Finset.univ.filter (fun x => s.seed x ≠ none))
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hab : a = b
    · subst a
      simp
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba]
  have hnot : b ∉ s.startedSet := by
    simpa [startedSet, Started] using hb
  change (s.start b w).startedSet.card + s.filled.card = s.score + 1
  rw [heq, Finset.card_insert_of_notMem hnot]
  unfold score
  omega

/--
@isnad1 id=eq.1h4v.s5.b0d9afac999b from=translated src=- shape=24005c0a vocab=6275eb49
-/
theorem score_fill (s : State B) (b : B) (w : Slot)
    (hn : ¬ s.Done b w) : (s.fill b w).score = s.score + 1 := by
  have hnot : (b, w) ∉ s.filled := hn
  change s.startedSet.card + (insert (b, w) s.filled).card = s.score + 1
  rw [Finset.card_insert_of_notMem hnot]
  unfold score
  omega
end State

/--
@isnad1 id=eq.1h4v.s5.9e5b0a55f095 from=translated src=- shape=38ebaaed vocab=0785bb52
-/
theorem step_score (M : Data B) {s s' : State B}
    (h : Step M s s') : s'.score = s.score + 1 := by
  cases h with
  | startAdjacent a b w ha hab hb => exact State.score_start s b w hb
  | startSupplier b a w v hr hn hsrc ha => exact State.score_start s a v ha
  | fillBase b w hr hn hsrc => exact State.score_fill s b w hn
  | fillSupplier b a w hr hn hsrc ha => exact State.score_fill s b w hn

inductive Trace (M : Data B) : ℕ → State B → State B → Prop
  | nil (s : State B) : Trace M 0 s s
  | cons {m : ℕ} {s s' s'' : State B} :
      Step M s s' → Trace M m s' s'' → Trace M (m + 1) s s''

/-- Abstract recovery, NOT the manuscript's counting lemma.
@isnad1 id=ex.1h3v.s6.dfcf7d14cd2a from=translated src=- shape=03097d62 vocab=cf944202
-/
theorem bounded_recovery (M : Data B) (s : State B)
    (hs : s.WellFormed M) :
    ∃ m s', Trace M m s s' ∧ (∀ b, s'.Complete b) ∧
      m + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ q : State B, N - q.score = d → q.WellFormed M →
      ∃ m q', Trace M m q q' ∧ (∀ b, q'.Complete b) ∧ m + q.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd hq
      by_cases hdone : ∀ b, q.Complete b
      · exact ⟨0, q, Trace.nil q, hdone, by
          have hbound := State.score_le q
          dsimp [N]
          omega⟩
      · obtain ⟨q', hstep⟩ := progress M q hq hdone
        have hq' : q'.WellFormed M := step_preserves M hstep hq
        have hscore : q'.score = q.score + 1 := step_score M hstep
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨m, q'', htrace, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' rfl hq'
        exact ⟨m + 1, q'', Trace.cons hstep htrace, hcomplete, by omega⟩
  exact aux (N - s.score) s rfl hs

noncomputable def initial (M : Data B) : State B := by
  classical
  exact ⟨fun b => if M.root b then some 0 else none,
    Finset.univ.filter (fun p : B × Slot => M.root p.1)⟩

/--
@isnad1 id=wellform.0h2v.s4.8849e0d827f3 from=translated src=- shape=fe3051fb vocab=81145c07
-/
theorem initial_wellFormed (M : Data B) : (initial M).WellFormed M := by
  classical
  constructor
  · intro b w h
    have hr : M.root b := by simpa [State.Done, initial] using h
    simp [State.Started, initial, hr]
  · intro b hr w
    simp [State.Done, initial, hr]

/-- Starts with just the roots, not an assumed completely recovered state.
@isnad1 id=ex.0h2v.s5.30952597386c from=translated src=- shape=9c41a770 vocab=a64e3192
-/
theorem recover_from_roots (M : Data B) :
    ∃ m s', Trace M m (initial M) s' ∧ (∀ b, s'.Complete b) ∧
      m ≤ 4 * Fintype.card B := by
  obtain ⟨m, s', ht, hc, hm⟩ :=
    bounded_recovery M (initial M) (initial_wellFormed M)
  exact ⟨m, s', ht, hc, by omega⟩
end Finite

end DeletionCode.Recovery
