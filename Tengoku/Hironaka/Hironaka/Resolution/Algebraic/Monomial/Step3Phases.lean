/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Resolution.Algebraic.Monomial.Measure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kollár's Step 3 on the monomial state, and its termination

The phases `3.1, …, 3.n` of [Kol07, 111, Step 3] on the combinatorial state of
`Hironaka/Resolution/Algebraic/Monomial/State.lean`. `phase r st hs` runs phase `r` (Kollár's Step
3.r): while Kollár's choice at phase `r` is nonempty, blow up its centre. The recursion is well
founded on `measure r`, which decreases at every blow-up (`measure_blowUp_lt` of
`Hironaka/Resolution/Algebraic/Monomial/Measure.lean`), and the hypothesis `hs`, `(∗_s)` for `s <
r`, is carried along by `star_blowUp`. `step3 st` runs the phases `1, …, n` in order (structural
recursion on the number of phases; `(∗_1)`, …, `(∗_r)` hold when phase `r + 1` starts). The result
is the final state and the list of centres, in order.

Postconditions, Kollár's "eventually we reach the stage where the property `(∗_r)` also holds"
and the end of Step 3.n: `step3_star` gives `(∗_s)` for every `s`, hence every face of the
final nerve has sum `< m` (`step3_maxOrd_lt`, the combinatorial form of
`max-ord (M(I), m) < m`). The run is recorded by `IsRun`: each centre of the list is Kollár's
nonempty choice at some phase `r ∈ [1, n]` of the state reached before it, and the final state
is the fold of the centres (`step3_isRun`, `IsRun.fold`).

`phaseFuel`/`step3Fuel` are executable copies with a fuel parameter (structural recursion) that
agree with `phase`/`step3` whenever the fuel suffices (`phase_eq_of_phaseFuel`,
`step3_eq_of_step3Fuel`); the example computations of `HironakaExamples/Monomial/Example112.lean`
and `HironakaExamples/MonomialState.lean` run them by `decide`, since a definition by well-founded
recursion does not reduce in the kernel.

Kollár's text is the source of the phases and of the measure; the run as a list of centres, the
predicate `IsRun` and the fuelled copies are bookkeeping not in the sources. The geometric
realisation of a run, blow-up by blow-up, is `Hironaka.Monomial.PieceFamily.realize`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`); functoriality of `step3` under
restriction and refinement of the state is `Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`
and its submodules.
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### One phase -/

/-- Phase `r` of Step 3 ([Kol07, 111, Step 3.r]): while Kollár's choice at phase `r` is
nonempty, blow up its centre; well-founded recursion on `measure r`, with `(∗_s)` for `s < r`
preserved along the run (`star_blowUp`). Returns the final state of the phase and its list of
centres.-/
def phase (r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    MonomialState × List (Finset (Finset ℕ)) :=
  if (st.choice r).Nonempty then
    let res := phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr
    (res.1, st.choice r :: res.2)
  else (st, [])
termination_by st.measure r
decreasing_by exact st.measure_blowUp_lt hs ‹_›

variable {r : ℕ}

/--
@isnad1 id=eq.2h2v.s6.67c21c620aed from=translated src=- shape=f8aa96b3 vocab=ad5e47cd
-/
theorem phase_of_nonempty (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (h : (st.choice r).Nonempty) :
    phase r st hs = ((phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr).1,
      st.choice r :: (phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr).2) := by
  rw [phase, ite_eq_left h]

/--
@isnad1 id=eq.2h2v.s5.a86e32a15e2a from=translated src=- shape=53b8fc7f vocab=9c102a5c
-/
theorem phase_of_not_nonempty (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (h : ¬ (st.choice r).Nonempty) : phase r st hs = (st, []) := by
  rw [phase, ite_eq_right h]

/-- A run of Step 3: each centre is Kollár's nonempty choice at some phase `r`, `1 ≤ r ≤ n`, of
the state reached before it.-/
inductive IsRun : MonomialState → List (Finset (Finset ℕ)) → MonomialState → Prop
  | nil (st : MonomialState) : IsRun st [] st
  | cons {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (r : ℕ) (hr : 1 ≤ r)
      (hrn : r ≤ st.n) (h : (st.choice r).Nonempty)
      (hL : IsRun (st.blowUp (st.choice r)) L st') : IsRun st (st.choice r :: L) st'

/-- Every centre of a run is Kollár's choice at some size `r` on the state reached so far (the
fold of the preceding centres), nonempty and within the dimension bound.
@isnad1 id=ex.1h4v.s6.a5d77e3628f0 from=translated src=- shape=f2d81dcb vocab=1bace02e
-/
theorem IsRun.exists_get_eq_choice {st st' : MonomialState}
    {L : List (Finset (Finset ℕ))} (h : MonomialState.IsRun st L st') (i : Fin L.length) :
    ∃ r, 1 ≤ r ∧ r ≤ ((L.take i).foldl MonomialState.blowUp st).n ∧
      (((L.take i).foldl MonomialState.blowUp st).choice r).Nonempty ∧
      L.get i = ((L.take i).foldl MonomialState.blowUp st).choice r := by
  induction h with
  | nil st => exact i.elim0
  | cons r hr hrn hne _ ih =>
    rcases i with ⟨_ | j, hj⟩
    · exact ⟨r, hr, hrn, hne, rfl⟩
    · obtain ⟨r', hr', hrn', hne', hget⟩ := ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      exact ⟨r', hr', hrn', hne', hget⟩

/--
@isnad1 id=isrun.2h5v.s5.02124286ab11 from=translated src=- shape=d0ea2afe vocab=02172a47
-/
theorem IsRun.append {st st₁ st₂ : MonomialState} {L₁ L₂ : List (Finset (Finset ℕ))}
    (h₁ : IsRun st L₁ st₁) (h₂ : IsRun st₁ L₂ st₂) : IsRun st (L₁ ++ L₂) st₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons r hr hrn h _ ih => exact IsRun.cons r hr hrn h (ih h₂)

/-- The final state of a run is the fold of its centres.
@isnad1 id=eq.1h3v.s4.7968e410776a from=translated src=- shape=939a9d38 vocab=80f93393
-/
theorem IsRun.fold {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st' = L.foldl blowUp st := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

/--
@isnad1 id=eq.1h3v.s4.6b1ac7c1ba30 from=translated src=- shape=105d8b9f vocab=53ee8821
-/
theorem IsRun.n_eq {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st'.n = st.n := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

/--
@isnad1 id=eq.1h3v.s4.16cc2cd994b5 from=translated src=- shape=105d8b9f vocab=24823d62
-/
theorem IsRun.m_eq {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st'.m = st.m := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

/-- The run of one phase, when the phase is within the dimension bound.
@isnad1 id=isrun.3h2v.s5.650047f1b8ba from=translated src=- shape=2ca2afda vocab=33f74aa6
-/
theorem phase_isRun (hr : 1 ≤ r) (st : MonomialState) (hs : ∀ s < r, st.Star s) (hrn : r ≤ st.n) :
    IsRun st (phase r st hs).2 (phase r st hs).1 := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih =>
    rw [phase_of_nonempty st hs h]
    exact IsRun.cons r hr hrn h (ih hrn)
  | case2 st hs h =>
    rw [phase_of_not_nonempty st hs h]
    exact IsRun.nil st

/-- At the end of phase `r`, `(∗_r)` holds: Kollár's "eventually we reach the stage where the
property `(∗_r)` also holds" of [Kol07, 111, Step 3.r].
@isnad1 id=star.1h2v.s4.770e2bcdaa5f from=translated src=- shape=e6dd607c vocab=0d492a74
-/
theorem phase_star (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.Star r := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h =>
    rw [phase_of_not_nonempty st hs h]
    exact st.choice_eq_empty_iff.mp (Finset.not_nonempty_iff_eq_empty.mp h)

/-- `(∗_s)`, `s < r`, still holds at the end of phase `r` (`star_blowUp` along the run).
@isnad1 id=star.2h3v.s5.958f8834b62b from=translated src=- shape=cd5ef75e vocab=0d492a74
-/
theorem phase_star_of_lt (st : MonomialState) (hs : ∀ s < r, st.Star s) {s : ℕ} (hsr : s < r) :
    (phase r st hs).1.Star s := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]; exact hs s hsr

/--
@isnad1 id=eq.1h2v.s4.3787d710108d from=translated src=- shape=41b61dec vocab=e3e1286f
-/
theorem phase_n (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.n = st.n := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

/--
@isnad1 id=eq.1h2v.s4.6c89e274bdb6 from=translated src=- shape=41b61dec vocab=7fb3a41c
-/
theorem phase_m (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.m = st.m := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

/-! ### The phases `r, r + 1, …` and Step 3 -/

/-- `(∗_s)` for `s < r + 1` from `(∗_s)` for `s < r` at the end of phase `r`.
@isnad1 id=star.2h3v.s5.eb219a106a6f from=translated src=- shape=7b00b4fd vocab=b14b05c9
-/
theorem phase_star_succ (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ s < r + 1, (phase r st hs).1.Star s := fun s hsr => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hsr with h | rfl
  · exact phase_star_of_lt st hs h
  · exact phase_star st hs

/-- `k` consecutive phases starting at phase `r`.-/
def phases : (k r : ℕ) → (st : MonomialState) → (∀ s < r, st.Star s) →
    MonomialState × List (Finset (Finset ℕ))
  | 0, _, st, _ => (st, [])
  | k + 1, r, st, hs =>
    let p := phase r st hs
    let q := phases k (r + 1) p.1 (phase_star_succ st hs)
    (q.1, p.2 ++ q.2)

/--
@isnad1 id=eq.1h2v.s5.c29b74f0e120 from=translated src=- shape=4394cbae vocab=427d8814
-/
theorem phases_zero (r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    phases 0 r st hs = (st, []) := rfl

/--
@isnad1 id=eq.1h3v.s7.b57df32685d8 from=translated src=- shape=92ab3372 vocab=697f69ee
-/
theorem phases_succ (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    phases (k + 1) r st hs =
      ((phases k (r + 1) (phase r st hs).1 (phase_star_succ st hs)).1,
        (phase r st hs).2 ++ (phases k (r + 1) (phase r st hs).1 (phase_star_succ st hs)).2) := rfl

/--
@isnad1 id=eq.1h3v.s5.a2a2ab0b545b from=translated src=- shape=f0fc8e93 vocab=413a7306
-/
theorem phases_n (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    (phases k r st hs).1.n = st.n := by
  induction k generalizing r st with
  | zero => rfl
  | succ k ih => rw [phases_succ, ih, phase_n]

/--
@isnad1 id=eq.1h3v.s5.cf96b6b0d667 from=translated src=- shape=f0fc8e93 vocab=d2c0ff17
-/
theorem phases_m (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    (phases k r st hs).1.m = st.m := by
  induction k generalizing r st with
  | zero => rfl
  | succ k ih => rw [phases_succ, ih, phase_m]

/-- After the phases `r, …, r + k - 1`, `(∗_s)` holds for every `s < r + k`.
@isnad1 id=star.2h4v.s5.28e0b7df0b34 from=translated src=- shape=4263c6c5 vocab=ae53d46b
-/
theorem phases_star (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ s < r + k, (phases k r st hs).1.Star s := by
  induction k generalizing r st with
  | zero => intro s hsr; exact hs s (by simpa using hsr)
  | succ k ih =>
    intro s hsr
    rw [phases_succ]
    exact ih (r + 1) _ (phase_star_succ st hs) s (by omega)

/--
@isnad1 id=isrun.3h3v.s6.4699eeae904e from=translated src=- shape=e5385443 vocab=e265f358
-/
theorem phases_isRun (k r : ℕ) (hr : 1 ≤ r) (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (hk : r + k ≤ st.n + 1) : IsRun st (phases k r st hs).2 (phases k r st hs).1 := by
  induction k generalizing r st with
  | zero => exact IsRun.nil st
  | succ k ih =>
    rw [phases_succ]
    have hp := phase_isRun hr st hs (by omega)
    refine hp.append (ih (r + 1) (by omega) _ (phase_star_succ st hs) ?_)
    rw [phase_n]; omega

/-- `(∗_0)` holds since faces are nonempty (`star_zero`).
@isnad1 id=star.1h2v.s4.b67326768ef9 from=translated src=- shape=57211671 vocab=9909f7af
-/
theorem star_of_lt_one (st : MonomialState) : ∀ s < 1, st.Star s := fun s hs => by
  obtain rfl : s = 0 := by omega
  exact st.star_zero

/-- Step 3 of [Kol07, 111]: the phases `1, …, n` in order, each by well-founded recursion on
`(m_r, n_r)`; the final state and the list of centres.-/
def step3 (st : MonomialState) : MonomialState × List (Finset (Finset ℕ)) :=
  phases st.n 1 st (star_of_lt_one st)

/--
@isnad1 id=eq.0h1v.s3.07dbeb217418 from=translated src=- shape=833453c4 vocab=089402cc
-/
theorem step3_n (st : MonomialState) : (step3 st).1.n = st.n := phases_n _ _ _ _

/--
@isnad1 id=eq.0h1v.s3.50fef5faa929 from=translated src=- shape=833453c4 vocab=891f813b
-/
theorem step3_m (st : MonomialState) : (step3 st).1.m = st.m := phases_m _ _ _ _

/-- At the end of Step 3, `(∗_s)` holds for every `s`.
@isnad1 id=star.0h2v.s3.e527c01d888c from=translated src=- shape=78a75477 vocab=5fe8cc1a
-/
theorem step3_star (st : MonomialState) (s : ℕ) : (step3 st).1.Star s := by
  by_cases hs : s < 1 + st.n
  · exact phases_star st.n 1 st (star_of_lt_one st) s hs
  · exact star_of_lt _ (by rw [step3_n]; omega)

/-- The postcondition of [Kol07, 111, Step 3] ("at the end of Step 3.n we are done"): every face
of the final nerve has sum `< m`. On the geometric side this is `max-ord (M(I), m) < m`.
@isnad1 id=lt.1h2v.s5.d8aec3c3cc99 from=translated src=- shape=6288299d vocab=60f85e95
-/
theorem step3_maxOrd_lt (st : MonomialState) {T : Finset ℕ} (hT : T ∈ (step3 st).1.nerve) :
    (step3 st).1.total T < st.m := by
  rw [← step3_m st]
  exact step3_star st T.card T ((step3 st).1.mem_faces.mpr ⟨hT, rfl⟩)

/-- The list of centres of Step 3 is a run: each centre is Kollár's nonempty choice at a phase
`r ∈ [1, n]` of the state before it, and the final state is their fold.
@isnad1 id=isrun.0h1v.s4.c9ae2e56337b from=translated src=- shape=39d14397 vocab=531a58f4
-/
theorem step3_isRun (st : MonomialState) : IsRun st (step3 st).2 (step3 st).1 :=
  phases_isRun st.n 1 le_rfl st (star_of_lt_one st) (by omega)

/-! ### Executable copies with fuel -/

/-- `phase` with fuel: `none` when the fuel runs out.-/
def phaseFuel : ℕ → ℕ → MonomialState → Option (MonomialState × List (Finset (Finset ℕ)))
  | 0, _, _ => none
  | fuel + 1, r, st =>
    if (st.choice r).Nonempty then
      (phaseFuel fuel r (st.blowUp (st.choice r))).map fun res => (res.1, st.choice r :: res.2)
    else some (st, [])

/--
@isnad1 id=eq.2h4v.s5.c9cb6e91537e from=translated src=- shape=0f9d5523 vocab=aab32641
-/
theorem phase_eq_of_phaseFuel {fuel : ℕ} {st : MonomialState} (hs : ∀ s < r, st.Star s)
    {res : MonomialState × List (Finset (Finset ℕ))} (h : phaseFuel fuel r st = some res) :
    phase r st hs = res := by
  induction fuel generalizing st res with
  | zero => exact absurd h (by simp [phaseFuel])
  | succ fuel ih =>
    by_cases hne : (st.choice r).Nonempty
    · rw [phaseFuel, ite_eq_left hne, Option.map_eq_some_iff] at h
      obtain ⟨res', hres', rfl⟩ := h
      rw [phase_of_nonempty st hs hne, ih (fun _ hsr => st.star_blowUp hs hsr) hres']
    · rw [phaseFuel, ite_eq_right hne, Option.some.injEq] at h
      rw [phase_of_not_nonempty st hs hne, h]

/-- `phases` with fuel per phase.-/
def phasesFuel (fuel : ℕ) : ℕ → ℕ → MonomialState →
    Option (MonomialState × List (Finset (Finset ℕ)))
  | 0, _, st => some (st, [])
  | k + 1, r, st =>
    match phaseFuel fuel r st with
    | none => none
    | some p =>
      match phasesFuel fuel k (r + 1) p.1 with
      | none => none
      | some q => some (q.1, p.2 ++ q.2)

/--
@isnad1 id=eq.2h5v.s5.50ce7cfeb225 from=translated src=- shape=56b9fd03 vocab=89300140
-/
theorem phases_eq_of_phasesFuel {fuel k r : ℕ} {st : MonomialState} (hs : ∀ s < r, st.Star s)
    {res : MonomialState × List (Finset (Finset ℕ))} (h : phasesFuel fuel k r st = some res) :
    phases k r st hs = res := by
  induction k generalizing r st res with
  | zero =>
    simp only [phasesFuel, Option.some.injEq] at h
    rw [phases_zero, h]
  | succ k ih =>
    rcases hp : phaseFuel fuel r st with _ | p
    · simp [phasesFuel, hp] at h
    · rcases hq : phasesFuel fuel k (r + 1) p.1 with _ | q
      · simp [phasesFuel, hp, hq] at h
      · simp only [phasesFuel, hp, hq, Option.some.injEq] at h
        have hpe : phase r st hs = p := phase_eq_of_phaseFuel hs hp
        have hq' : phasesFuel fuel k (r + 1) (phase r st hs).1 = some q := by rw [hpe]; exact hq
        rw [phases_succ, ih (phase_star_succ st hs) hq', hpe, ← h]

/-- `step3` with fuel per phase.-/
def step3Fuel (fuel : ℕ) (st : MonomialState) : Option (MonomialState × List (Finset (Finset ℕ))) :=
  phasesFuel fuel st.n 1 st

/--
@isnad1 id=eq.1h3v.s5.b5e913325b08 from=translated src=- shape=a28717c5 vocab=9b2ff67e
-/
theorem step3_eq_of_step3Fuel {fuel : ℕ} {st : MonomialState}
    {res : MonomialState × List (Finset (Finset ℕ))} (h : step3Fuel fuel st = some res) :
    step3 st = res :=
  phases_eq_of_phasesFuel (star_of_lt_one st) h

/-- Any function `f` of the run read off the fuelled copy (for `decide`: the final state has
function fields, so it is compared through `f`).
@isnad1 id=eq.1h5v.s5.d93a40394fdc from=translated src=- shape=991864cc vocab=f4fd58cf
-/
theorem step3_map_eq_of_step3Fuel {fuel : ℕ} {st : MonomialState} {α : Type*}
    (f : MonomialState × List (Finset (Finset ℕ)) → α) {x : α}
    (h : (step3Fuel fuel st).map f = some x) : f (step3 st) = x := by
  obtain ⟨res, hres, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [step3_eq_of_step3Fuel hres]

end Hironaka.Monomial.MonomialState
